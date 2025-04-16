{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Compressed lists.
module CList where

import Prelude hiding (take, drop, reverse)
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Either
import Data.List hiding (take, drop, reverse, isPrefixOf, isSuffixOf)
import Data.List qualified as List
import Data.Maybe
import Test.QuickCheck
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Text.Printf

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data CLE a = Atom a | CList a :^ Int -- Power always ≥ 2
  deriving (Eq, Ord, Show)

newtype CList a = CList [CLE a]
  deriving (Eq, Ord, Show, Foldable)

unCList :: CList a -> [CLE a]
unCList (CList xs) = xs

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

instance Foldable CLE where
  foldMap f (xs :^ n) = fold (replicate n $ foldMap f xs)
  foldMap f (Atom x)  = f x

instance Eq a => Semigroup (CList a) where
  CList xs <> ys = foldr consC ys xs

instance Eq a => Monoid (CList a) where
  mempty = CList []

------------------------------------------------------------------------
-- API
------------------------------------------------------------------------

-- fromList ---------------------------------------------------------------

fromList :: Eq a => [a] -> CList a
fromList = foldr cons mempty

-- reverse ----------------------------------------------------------------

reverse :: Eq a => CList a -> CList a
reverse (CList xs) = foldl (flip consC) mempty $ map rev xs
  where
    rev x@Atom{}  = x
    rev (xs :^ n) = reverse xs :^ n

-- Prefix and suffix ------------------------------------------------------

dropPrefix :: CList a -> CList a -> Maybe (CList a)
dropPrefix (CList xs) (CList ys) = foldM (flip go) ys xs
  where
    go (Atom x) ys = do
      (y, ys) <- uncons ys
      guard $ x == y
      pure ys
    go (CList xs :^ n) ys = undefined

isPrefixOf :: CList a -> CList a -> Bool
isPrefixOf xs ys = isJust $ dropPrefix xs ys

isSuffixOf :: CList a -> CList a -> Bool
isSuffixOf xs ys = isPrefixOf (rawReverse xs) (rawReverse ys)

------------------------------------------------------------------------
-- Internal functions
------------------------------------------------------------------------

-- RepView ----------------------------------------------------------------

data RepView a = RepView { rvPrefix :: [CLE a]  -- rvPrefix is a suffix of rvRepeat
                         , rvRepeat :: CList a
                         , rvCount  :: Int
                         , rvSuffix :: [CLE a]
                         }
  deriving (Eq, Ord, Show)

fromRepView :: RepView a -> CList a
fromRepView (RepView xs ys n zs) = CList (xs ++ [ys :^ n] ++ zs)

-- Raw reverse ------------------------------------------------------------

-- Ignoring invariant
rawReverse :: CList a -> CList a
rawReverse (CList xs) = CList $ List.reverse $ map rev xs
  where
    rev x@Atom{}  = x
    rev (xs :^ n) = rawReverse xs :^ n

-- uncons -----------------------------------------------------------------

uncons :: CList a -> Maybe (a, CList a)
uncons (CList []) = Nothing
uncons (CList (Atom x : xs)) = pure (x, CList xs)
uncons (CList (xs :^ n : ys)) = do
  (x, CList zs) <- uncons xs
  if | n > 2     -> pure (x, CList (zs ++ xs :^ (n - 1) : ys))
     | otherwise -> pure (x, CList (zs ++ xs ++ ys))

-- cons -------------------------------------------------------------------

cons :: Eq a => a -> CList a -> CList a
cons = consC . Atom

consC :: Eq a => CLE a -> CList a -> CList a
consC x (CList xs) = CList $ fromMaybe (x : xs) $
  case x of
    Atom x -> consC' [Atom x] xs
    CList ys :^ n
      | Just zs <- consCs ys xs -> pure $ if n > 2 then rec (CList ys :^ (n - 1)) zs
                                                   else foldr rec zs ys
      | otherwise -> consC' [x] xs
  where
    rec x xs = unCList $ consC x (CList xs)

    consCs [y]      xs = consC' [y] xs
    consCs (y : ys) xs
      | Just zs <- consCs ys xs = pure $ rec y zs
      | otherwise               = consC' [y] (ys ++ xs)

    consC' [CList xs :^ n] ys
      | Just zs <- dropPrefix xs ys = pure $ rec (CList xs :^ (n + 1)) zs
      | CList ys :^ m : zs <- ys
      , xs == ys                    = pure $ rec (CList xs :^ (n + m)) zs
    consC' xs ys
      | Just zs <- dropPrefix xs ys = pure $ rec (double xs) zs
      where
        double [xs :^ n] = xs :^ (2 * n)
        double xs        = CList xs :^ 2
    consC' xs (c@(CList ys) :^ n : zs)
      | xs == ys = pure $ rec (c :^ (n + 1)) zs
    consC' xs (y : ys) = consC' (xs ++ [y]) ys
    consC' _ _ = Nothing

------------------------------------------------------------------------
-- Utility functions
------------------------------------------------------------------------

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left x)  = Left (f x)
mapLeft f (Right y) = Right y

-- Non-empty splits
splits :: [a] -> [([a], [a])]
splits []       = []
splits [x]      = []
splits (x : xs) = ([x], xs) : [ (x : ys, zs) | (ys, zs) <- splits xs ]

dropPrefix :: Eq a => [a] -> [a] -> Maybe [a]
dropPrefix      []       ys  = pure ys
dropPrefix (x : xs) (y : ys) = guard (x == y) *> dropPrefix xs ys
dropPrefix (_ :  _)      []  = Nothing

------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

showP :: Pretty a => a -> String
showP = show . pPrint

pShow :: Show a => a -> Doc
pShow = text . show

instance Pretty a => Pretty (CList a) where
  pPrintPrec _ _ (CList []) = "ε"
  pPrintPrec _ p (CList xs) = parensIf (p > 0 && notAtom xs) $ hcat $ map pPrint xs
    where notAtom [Atom{}] = False
          notAtom _        = True

instance Pretty a => Pretty (CLE a) where
  pPrintPrec _ _ (Atom x)  = pPrint x
  pPrintPrec l p (xs :^ n) = parensIf (p > 0) $ pPrintPrec l 1 xs <> pow n
    where
      pow = text . map ((ds !!) . subtract (fromEnum '0') . fromEnum) . show
      ds  = "⁰¹²³⁴⁵⁶⁷⁸⁹"

instance Pretty Doc where
  pPrint = id

------------------------------------------------------------------------
-- QuickCheck tests
------------------------------------------------------------------------

counterexampleP :: (Pretty a, Testable p) => a -> p -> Property
counterexampleP = counterexample . showP

-- Random list of positive integers summing to a given value.
genSum :: Int -> Gen [Int]
genSum n | n < 1 = error $ printf "genSum: %d < 1" n
genSum n = shuffle =<< go n
  where
    go 0 = pure []
    go n = choose (1, n) >>= \ k -> (k :) <$> go (n - k)

-- Arbitrary instances ----------------------------------------------------

instance (Eq a, Arbitrary a) => Arbitrary (CList a) where
  arbitrary = fromList <$> arbitrary
  shrink = map fromList . shrink . toList

newtype Bit = Bit Int
  deriving newtype (Eq, Ord, Show, Num, Pretty)

instance Arbitrary Bit where
  arbitrary = elements [0, 1]
  shrink 1 = [0]
  shrink _ = []

-- Without regard for invariant.
newtype RawCList a = Raw (CList a)
  deriving newtype Show

instance Arbitrary a => Arbitrary (RawCList a) where
  arbitrary = Raw <$> sized go
    where
      go n
        | n < 2 = CList . (:[]) . Atom <$> arbitrary
        | otherwise = frequency [ (1, go 0)
                                , (5, CList <$> (mapM goC =<< genSum n))
                                ]

      goC 0 = Atom <$> arbitrary
      goC n = frequency [ (1, Atom <$> arbitrary)
                        , (4, (:^) <$> go n <*> choose (2, 8))
                        ]
  shrink (Raw (CList xs)) = Raw . CList . concat <$> shrinkList shrinkCLE (map pure xs)
    where
      shrinkCLE [Atom x] = [] : [ [Atom x] | x <- shrink x ]
      shrinkCLE [xs :^ n] = [] : unCList xs :
        [ [xs :^ n] | Raw xs <- shrink (Raw xs) ] ++
        [ [xs :^ n] | n <- shrink n, n > 1 ]

-- Roundtrip properties ---------------------------------------------------

prop_list_roundtrip :: [Bit] -> Property
prop_list_roundtrip xs =
  counterexample (printf "fromList: %s" (show ys)) $
    xs === toList ys
  where
    ys = fromList xs

prop_clist_roundtrip :: CList Bit -> Property
prop_clist_roundtrip xs =
  counterexample (printf "toList: %s" (show ys)) $
    xs === fromList ys
  where
    ys = toList xs

-- Operation: cons --------------------------------------------------------

prop_cons :: Bit -> CList Bit -> Property
prop_cons x xs = cons x xs === fromList (x : toList xs)

prop_cons_inv :: Bit -> CList Bit -> Property
prop_cons_inv x xs = counterexample (show $ cons x xs) $
  invariant xs ==> prop_invariant (cons x xs)

-- Operation: <> ----------------------------------------------------------

prop_append :: CList Bit -> CList Bit -> Property
prop_append xs ys = counterexampleP (vcat [ "xs       =" <+> pPrint xs
                                          , "ys       =" <+> pPrint ys
                                          , "xs <> ys =" <+> pPrint zs ]) $
    conjoin [ toList zs === toList xs ++ toList ys
            , prop_invariant zs ]
  where
    zs = xs <> ys

-- Operation: reverse -----------------------------------------------------

prop_reverse :: CList Bit -> Property
prop_reverse xs = toList (reverse xs) === List.reverse (toList xs)

prop_reverse_inv :: CList Bit -> Property
prop_reverse_inv xs = counterexample (showP xs) $
  prop_invariant (reverse xs)

-- Operation: isSuffixOf --------------------------------------------------

prop_isSuffixOf :: RawCList Bit -> RawCList Bit -> Property
prop_isSuffixOf (Raw xs) (Raw ys) = check xs ys .&&. check ys xs
  where
    check xs ys =
      counterexampleP (vcat [ "xs  =" <+> pPrint xs
                            , "ys  =" <+> pPrint ys
                            , "xsL =" <+> pPrint xsL
                            , "ysL =" <+> pPrint ysL
                            ]) $
        isSuffixOf xs ys === List.isSuffixOf xsL ysL
      where
        xsL = toList xs
        ysL = toList ys

-- Invariant checking -----------------------------------------------------

invariant :: (Eq a, Show a, Pretty a) => CList a -> Bool
invariant = isRight . checkInvariant

checkInvariant :: (Eq a, Show a, Pretty a) => CList a -> Either Doc ()
checkInvariant xs = mapLeft ("Invariant failed for" <+> (pPrint xs <> ":") $$) $ do
    let xss = sublists xs
    mapM_ checkRepeats xss
    mapM_ checkConsecutive xss
    mapM_ checkExponents (concat xss)
  where
    sublists (CList xs) = xs : concat [ sublists ys | ys :^ _ <- xs ]

    checkExponents x@(_ :^ n) | n < 2 = Left $ "Exponent too small:" <+> pPrint x
    checkExponents x@(CList [_ :^ _] :^ _) = Left $ "Nested exponents:" <+> pPrint x
    checkExponents _ = pure ()

    checkRepeats xs =
      mapM_ checkRepeat $ splits xs
      where
        checkRepeat (ys, zs)
          | List.isPrefixOf ys zs = Left ("Repeated" <+> pPrint ys)
          | otherwise             = pure ()

    checkConsecutive = go . List.reverse
      where
        go (c@(x :^ _) : ys)
          | List.isSuffixOf xs zs =
              Left $ sep [ pPrint $ CList $ List.reverse ys
                         , nest 2 "should fold into"
                         , pPrint c ]
          where
            xs = toList x
            zs = toList (CList $ List.reverse ys)
        go (_ : xs) = go xs
        go []       = pure ()

prop_invariant :: CList Bit -> Property
prop_invariant xs = case checkInvariant xs of
  Left err -> counterexampleP err False
  Right () -> property True

-- Running all the properties ---------------------------------------------

return []
qcAll :: (Property -> Property) -> IO Bool
qcAll f = $forAllProperties (quickCheckResult . f)
