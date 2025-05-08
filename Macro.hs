
module Macro where

import Control.Monad
import Data.Map qualified as Map
import Data.Map (Map)
import Data.Monoid
import Data.Maybe
import Data.Bits
import Data.List
import Text.Printf
import Text.Pretty
import RList
import Tape
import Debug.Trace
import Test.QuickCheck

{-

Goals
  - JIT compiler for the macro machines in Turing
  - Combine with exploration

Plan

  - Switch macro machine to use CMachine and applyClause
    - How to handle the wall? It's part of the input but shouldn't be part of the output.
      - Maybe make it part of the pattern!
    - Compile single macro steps to compound rules

  - JIT: keep history of how many times two rules are used together and combine them if over a
    threshold (could be low threshold!)
    - analyse rules for batchability
    - could you combine batched rules? might need extension to clause language, but maybe

-}

data Batching = NoBatch
              | Batch Dir Int  -- Bind any multiple of k number of the left/right-most symbol
  deriving (Eq, Ord, Show)

isBatch :: Dir -> Batching -> Bool
isBatch d (Batch d' _) = d == d'
isBatch _ NoBatch      = False

data WallPat = AnyWall | NoWall | YesWall
  deriving (Eq, Ord, Show)

data Pattern = Pattern Batching WallPat [Symbol] [Symbol]
  deriving (Eq, Ord, Show)

data RHSSymbol = Single Symbol | Batched Symbol   -- The same number as was matched in a batched pattern
  deriving (Eq, Ord, Show)

data RHS = RHS [RHSSymbol] [RHSSymbol] Dir
  deriving (Eq, Ord, Show)

data Clause = Pattern :=> RHS
  deriving (Eq, Ord, Show)

data CRule s = CRule Clause s Int  -- Next state and cost
  deriving (Eq, Ord, Show)

newtype CMachine s = CMachine (Map s [CRule s])
  deriving newtype (Eq, Ord, Show)

emptyCMachine :: Ord s => CMachine s
emptyCMachine = CMachine mempty

addCRule :: Ord s => s -> CRule s -> CMachine s -> CMachine s
addCRule s r (CMachine m) = CMachine $ Map.insertWith ins s [r] m
  where
    -- Batched rules have priority
    ins new old = foldr ins1 old new
    subsumedBy (CRule (lhs1 :=> _) _ n1) (CRule (lhs2 :=> _) _ n2) = lhs1 == lhs2 && n1 >= n2
    ins1 r@(CRule (Pattern NoBatch _ _ _ :=> _) _ _)
         (r1@(CRule (Pattern b _ _ _ :=> _) _ _) : rs)
      | b /= NoBatch = r1 : ins1 r rs
    ins1 r rs = r : filter (not . subsumedBy r) rs

getCRules :: Ord s => s -> CMachine s -> [CRule s]
getCRules s (CMachine m) = fromMaybe [] $ Map.lookup s m

-- Applying rules ---------------------------------------------------------

-- The integer is the multiplicity of the batched match (1 if NoBatch)
matchPattern :: Pattern -> Tape -> Maybe (Tape, Int)
matchPattern (Pattern b wall lp rp) (Tape w l r) = do
  let batchLast
        | wall /= NoWall = True
        | isBatch L b    = False
        | otherwise      = True
      rh | rh :@ _ <- r = rh
         | otherwise    = 0
  (l', bl) <- if | null lp, isBatch L b -> match L batchLast True [rh] (rh :@ l)
                 | otherwise            -> match L batchLast (isBatch L b) lp l
  (r', br) <- match R True (isBatch R b) rp r
  guard $ matchWall wall l'
  pure (Tape (w - length lp - bl + 1) l' r', max bl br)
  where
    match _ _ _ [] ys = pure (ys, 1)
    match _ bLast True [x] (RList (RLE y n : ys))
      | not bLast, null ys = (y :@ RList ys, n - 1) <$ guard (x == y && n > 1)
      | otherwise          = (RList ys, n) <$ guard (x == y)
    match d bLast b (x : xs) (y :@ ys) = guard (x == y) *> match d bLast b xs ys
    match R bLast b (0 : xs) NilR = match R bLast b xs NilR
    match _ _ _ _ _ = Nothing

    matchWall AnyWall _  = True
    matchWall NoWall  ls = ls /= NilR
    matchWall YesWall ls = ls == NilR

rhsToRLEs :: Int -> [RHSSymbol] -> [RLE Symbol]
rhsToRLEs n rhs = map eval rhs
  where
    eval (Single x)  = RLE x 1
    eval (Batched x) = RLE x n

writeRHS :: Int -> RHS -> Tape -> Tape
writeRHS n (RHS lrhs rrhs d) = writeAndMove d (rhsToRLEs n lrhs) (rhsToRLEs n rrhs)
  where
    writeAndMove L []        rs' = move L . write [] rs'
    writeAndMove L (l : ls') rs' = write ls' (l : rs')
    writeAndMove R ls'       []  = move R . write ls' []
    writeAndMove R ls' (r : rs') = write (r : ls') rs'

    write :: [RLE Symbol] -> [RLE Symbol] -> Tape -> Tape
    write ls' rs' (Tape w ls rs) = Tape (w + lengthR lsR) (lsR <> ls) (rsR <> rs)
      where lsR = foldMap (RList . (:[])) ls'
            rsR = foldMap (RList . (:[])) rs'

applyClause :: Clause -> Tape -> Maybe (Tape, Int)
applyClause (pat :=> rhs) tape = do
  (tape', n) <- matchPattern pat tape
  pure (writeRHS n rhs tape', n)

applyCRule :: CRule s -> Tape -> Maybe (s, Tape, Int)
applyCRule (CRule cl s n) tape = do
  (tape, m) <- applyClause cl tape
  pure (s, tape, n * m)

-- Smarts -----------------------------------------------------------------

batchRule :: (Show s, Eq s) => s -> CRule s -> CRule s
batchRule s r = -- trace (printf "batchRule %s (%s)" (show s) (show r)) $
  batchRule' s r

batchRule' :: Eq s => s -> CRule s -> CRule s
batchRule' s rule@(CRule (Pattern b w _ _ :=> _) s' _)
  | s /= s' || b /= NoBatch || w == YesWall = rule
batchRule' _ (CRule (Pattern NoBatch w lsP rsP :=> RHS ls (Single r : rs) d) s' n)
  | Just r <- go d = r
  where
    matchAndPad z [] [] = pure 0
    matchAndPad z (p : ps) []
      | z == p = succ <$> matchAndPad z ps []
    matchAndPad z (p : ps) (Single x : xs)
      | x == p = matchAndPad z ps xs
    matchAndPad _ _ _ = Nothing

    go R = do
      rP : _ <- pure $ reverse rsP
      guard $ map Single lsP `isPrefixOf` ([Single r] ++ ls)
      k <- matchAndPad rP rsP rs
      guard $ k > 0
      let r' : ls' = batchLast (Single r : ls)
      pure $ CRule (Pattern (Batch R k) w lsP rsP :=> RHS ls' (r' : rs) R) s' n
    go L = do
      rL : _ <- pure $ reverse (take 1 rsP ++ lsP)
      guard $ map Single lsP == drop 1 (ls ++ [Single rL])
      guard $ map Single rsP `isPrefixOf` take (length rsP) (take 1 (ls ++ [Single rL]) ++ Single r : rs)
      pure $ CRule (Pattern (Batch L 1) w lsP rsP :=> RHS ls (batchLast $ Single r : rs) L) s' n
batchRule' _ rule = rule

batchLast :: [RHSSymbol] -> [RHSSymbol]
batchLast [Single r] = [Batched r]
batchLast (r : rs) = r : batchLast rs
batchLast _ = error "impossible"

r1 :: CRule String
r1 = CRule (Pattern NoBatch AnyWall [] [7, 7] :=> RHS [Single 7] [Single 7] R) "AR" 6

-- r1, r2, r3 :: CRule String
-- r1 = CRule (Pattern NoBatch NoWall [] [7]  :=> RHS [] [Single 3]           L) "BL" 1
-- r2 = CRule (Pattern NoBatch NoWall [] [0]  :=> RHS [] [Single 0]           R) "CR" 1
-- r3 = CRule (Pattern NoBatch NoWall [0] [7] :=> RHS [] [Single 0, Single 3] R) "CR" 2

allSingle :: [RHSSymbol] -> Maybe [Symbol]
allSingle = mapM unSingle
  where unSingle (Single x) = pure x
        unSingle Batched{} = Nothing

-- Check that one of the lists is a prefix of the other. Returns the remaining part of both lists
-- (one of which will be empty).
dropEitherPrefix :: Eq a => [a] -> [a] -> Maybe ([a], [a])
dropEitherPrefix [] ys = pure ([], ys)
dropEitherPrefix xs [] = pure (xs, [])
dropEitherPrefix (x : xs) (y : ys) = guard (x == y) *> dropEitherPrefix xs ys

combineRules :: (Show s, Eq s) => CRule s -> CRule s -> Maybe (CRule s)
combineRules (CRule (Pattern b1 w1 _ _ :=> _) _ _)
             (CRule (Pattern b2 w2 _ _ :=> _) _ _)
  | or [b1 /= NoBatch, b2 /= NoBatch, w1 == YesWall, w2 == YesWall] = Nothing
combineRules      (CRule (Pattern NoBatch w1 lp1   rp1          :=> RHS []  rs1 L) _ n1)
                  (CRule (Pattern NoBatch w2 lp2   (rp2 : rps2) :=> RHS ls2 rs2 d) s n2) = do
  rs1s <- allSingle rs1
  (rs1', rp2') <- dropEitherPrefix rs1s rps2
  let lp = lp1 ++ rp2 : lp2
      rp = rp1 ++ rp2'
      ls = ls2
      rs = rs2 ++ map Single rs1'
  pure $ CRule (Pattern NoBatch w2 lp rp :=> RHS ls rs d) s (n1 + n2)
combineRules      (CRule (Pattern NoBatch w1 lp1   rp1   :=> RHS (l1 : ls1) rs1 L) _ n1)
                  (CRule (Pattern NoBatch w2 lp2   rp2   :=> RHS ls2        rs2 d) s n2) = do
  ls1s <- allSingle ls1
  rs1s <- allSingle (l1 : rs1)
  (ls1', lp2') <- dropEitherPrefix ls1s lp2
  (rs1', rp2') <- dropEitherPrefix rs1s rp2
  let w = if null ls1' then w2 else w1
      lp = lp1 ++ lp2'
      rp = rp1 ++ rp2'
      ls = ls2 ++ map Single ls1'
      rs = rs2 ++ map Single rs1'
  pure $ CRule (Pattern NoBatch w lp rp :=> RHS ls rs d) s (n1 + n2)
combineRules      (CRule (Pattern NoBatch w1 lp1   rp1   :=> RHS ls1 (r : rs1) R) _ n1)
                  (CRule (Pattern NoBatch w2 lp2   rp2   :=> RHS ls2 rs2       d) s n2) = do
  ls1s <- allSingle (r : ls1)
  rs1s <- allSingle rs1
  (ls1', lp2') <- dropEitherPrefix ls1s lp2
  (rs1', rp2') <- dropEitherPrefix rs1s rp2
  let w | null ls1' = w2
        | otherwise = w1
      lp = lp1 ++ lp2'
      rp = rp1 ++ rp2'
      ls = ls2 ++ map Single ls1'
      rs = rs2 ++ map Single rs1'
  pure $ CRule (Pattern NoBatch w lp rp :=> RHS ls rs d) s (n1 + n2)
combineRules _ _ = Nothing

-- Pretty printing --------------------------------------------------------

instance Pretty Clause where
  pPrint (pat :=> rhs) = sep [ pPrint pat <+> text "=>", nest 2 $ pPrint rhs ]

instance Pretty Pattern where
  pPrint (Pattern b w ls rs) = ppW w <> sep [ ppL ls, text "∙" <> ppR rs ]
    where
      ppW AnyWall = text "? "
      ppW YesWall = text "| "
      ppW NoWall  = text "… "

      batchIf True  = zipWith ($) (Batched : repeat Single)
      batchIf False = map Single

      ppL (reverse -> ls) = sep $ map pPrint $ batchIf (isBatch L b) ls
      ppR rs = sep $ map pPrint $ batchIf (isBatch R b) rs

instance Pretty RHS where
  pPrint (RHS ls rs d) =
    case d of
      L | l : ls <- ls -> sep [ text " ", ppr ls, text "∙" <> ppr (l : rs) ]
        | otherwise    -> sep [ text "∙_  ", ppr rs ]
      R | r : rs <- rs -> sep [ text " " <> ppr (ls ++ [r]), text "∙" <> if null rs then text "_ " else ppr rs ]
        | otherwise    -> sep [ text " " <> ppr ls, text "_ ∙_ " ]  -- Impossible
    where
      ppr = sep . punctuate (text " ") . map pPrint

instance Pretty RHSSymbol where
  pPrint (Single  x) = text (show x ++ " ")
  pPrint (Batched x) = text (show x ++ "ⁿ")

instance Show s => Pretty (CRule s) where
  pPrint (CRule pat s n) = hsep [ pPrint pat, text (show s), parens $ text (show n) <> text " steps"]

instance Show s => Pretty (CMachine s) where
  pPrint (CMachine m) = vcat [ text (show s ++ ":") <+> vcat (map pPrint rs) | (s, rs) <- Map.toList m ]

-- QuickCheck tests -------------------------------------------------------

genSym :: Gen Symbol
genSym = Symbol <$> choose (0, 2)

genSyms :: Gen [Symbol]
genSyms = choose (0, 3) >>= (`vectorOf` genSym)

instance Arbitrary Pattern where
  arbitrary = (Pattern NoBatch AnyWall <$> genSyms <*> genSyms) `suchThat` \ (Pattern _ _ lp rp) -> not $ null $ lp ++ rp
  shrink (Pattern b w lp rp) =
    [ Pattern b w lp rp | lp <- shrink lp, not $ null $ lp ++ rp ] ++
    [ Pattern b w lp rp | rp <- shrink rp, not $ null $ lp ++ rp ]

instance Arbitrary RHS where
  arbitrary = RHS <$> (map Single <$> genSyms) <*> (map Single <$> genSyms) <*> arbitrary

instance Arbitrary Clause where
  arbitrary = do
    lhs <- arbitrary
    rhs <- arbitrary `suchThat` \ rhs -> clauseInvariant (lhs :=> rhs)
    pure (lhs :=> rhs)
  shrink (lhs :=> rhs) = filter clauseInvariant $
    [ lhs :=> rhs | lhs <- shrink lhs ] ++
    [ lhs :=> rhs | rhs <- shrink rhs ] ++
    [ lhs :=> rhs | lhs <- shrink lhs,
                    rhs <- shrink rhs ]

clauseInvariant :: Clause -> Bool
clauseInvariant (Pattern _ _ lp rp :=> RHS ls rs _) = n > 0 && n == m
  where
    n = length (lp ++ rp)
    m = length (ls ++ rs)

instance Arbitrary s => Arbitrary (CRule s) where
  arbitrary = CRule <$> arbitrary <*> arbitrary <*> choose (1, 10)
  shrink (CRule c s n) =
    [ CRule c s n | c <- shrink c ] ++
    [ CRule c s n | s <- shrink s ] ++
    [ CRule c s n | n <- shrink n, n > 0 ]

newtype St = St String
  deriving newtype (Eq, Ord, Show)

instance Arbitrary St where
  arbitrary = elements $ map St ["AL", "AR", "BL", "BR", "CL", "CR"]

ppTape :: Tape -> Doc
ppTape (Tape _ ls rs) = hsep (map (text . show) $ expand ls) <+> (text "∙" <> hsep (map (text . show) $ expand rs))

prop_combine :: CRule St -> CRule St -> Property
prop_combine r1 r2 =
  case combineRules r1 r2 of
    Nothing -> discard
    Just r3@(CRule (Pattern _ _ lp rp :=> _) _ _) ->
      collect (length $ lp ++ rp) $
      case applyCRule r3 tape of
        Nothing                      -> whenFail (putStrLn "failed to apply r3!") False
        applyR3@(Just (_, tape3, _)) -> whenFail onErr $ checkInv r3 .&&. applyR3 === applyR12
          where
            checkInv r@(CRule c _ _) = whenFail (print $ text "invariant broken:" <+> text (show r)) $ clauseInvariant c
            applyR1 = applyCRule r1 tape
            applyR2 = applyCRule r2
            applyR12 = do
              (_, tape1, n) <- applyR1
              (s, tape2, m) <- applyR2 tape1
              pure (s, tape2, n + m)
            applyR3 = applyCRule r3 tape
            onErr = do
              print $ text "r1 =" <+> pPrint r1
              print $ text "r2 =" <+> pPrint r2
              print $ text "r3 =" <+> pPrint r3
              print $ nest 7 $ ppTape tape
              case applyR12 of
                Just (_, tape2, _)
                  | Just (_, tape1, _) <- applyR1 -> do
                  print $ vcat [ text "=>{r1}" <+> ppTape tape1
                               , text "=>{r2}" <+> ppTape tape2
                               ]
                Nothing            -> pure ()
              print $ text "=>{r3}" <+> ppTape tape3
      where
        tape = mkTape lp rp

prop_batch :: Property
prop_batch =
  forAllShrink genBatched shrinkBatched $ \ (r, rS) -> theProp r rS :: Property
  where
  genBatched :: Gen (CRule St, CRule St)
  genBatched = do
      r@(CRule _ s _) <- arbitrary
      pure (r, batchRule s r)
    `suchThat` uncurry (/=)
  shrinkBatched (r, _) =
    [ (r, rS) | r@(CRule _ s _) <- shrink r, let rS = batchRule s r, r /= rS ]

  reps = 5

  theProp r rS@(CRule (Pattern b _ lsP rsP :=> _) _ _) =
    applyRules 0 [rS] tape $ \ res1@(_, n) ->
    whenFail (printf "(%d steps)\n" n) $
    applyRules 0 (replicate (reps + 1) r) tape $ \ res2@(_, n) ->
    whenFail (printf "(%d steps)\n" n) $
      res1 === res2
    where
      tape = case b of
               Batch L k -> mkTape (lsP ++ replicate (k * reps) (last $ take 1 rsP ++ lsP)) rsP
               Batch R k -> mkTape lsP (rsP ++ replicate (k * reps) (last rsP))
               NoBatch   -> error "impossible"
      applyRules n [] tape k = whenFail (print $ ppTape tape) $ k (tape, n)
      applyRules !n (r : rs) tape k =
        case applyCRule r tape of
          Nothing -> whenFail (print $ vcat [ text "Failed to apply"
                                            , nest 2 $ pPrint r
                                            , text "to"
                                            , nest 2 $ ppTape tape ]) False
          Just (_, tape1, m) ->
            whenFail (print $ vcat [ ppTape tape, nest 2 $ pPrint r ]) $ applyRules (n + m) rs tape1 k
