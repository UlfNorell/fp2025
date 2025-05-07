{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Compressed lists.
module Data.List.Compressed where

import Prelude hiding (take, drop, reverse)
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Either
import Data.List hiding (take, drop, reverse, isPrefixOf, isSuffixOf, uncons)
import Data.List qualified as List
import Data.Maybe
import Test.QuickCheck
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Text.Printf

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data Rep a = a :^ Int -- Power ≥ 1
  deriving (Eq, Ord, Show, Functor)

newtype CList a = CList [Rep [a]] -- Nonempty list of a's
  deriving (Eq, Ord, Show, Foldable)

unCList :: CList a -> [Rep [a]]
unCList (CList xs) = xs

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

instance Foldable Rep where
  foldMap f (x :^ n) = fold (replicate n $ f x)

instance Eq a => Semigroup (CList a) where
  CList xs <> ys = foldr consRep ys xs

instance Eq a => Monoid (CList a) where
  mempty = CList []

------------------------------------------------------------------------
-- API
------------------------------------------------------------------------

pattern NilC = CList []
pattern (:@) :: Eq a => a -> CList a -> CList a
pattern x :@ xs <- (uncons -> Just (x, xs))
  where x :@ xs = cons x xs
{-# COMPLETE NilC, (:@) #-}

-- fromList ---------------------------------------------------------------

fromList :: Eq a => [a] -> CList a
fromList = foldr cons mempty

-- reverse ----------------------------------------------------------------

reverse :: CList a -> CList a
reverse = CList . List.reverse . map rev . unCList
  where rev (xs :^ n) = List.reverse xs :^ n

-- Prefix and suffix ------------------------------------------------------

dropPrefix :: Eq a => CList a -> CList a -> Maybe (CList a)
dropPrefix (CList xs) (CList ys) = go xs ys
  where
    go ([] :^ _ : xss) yss = go xss yss
    go xss ([] :^ _ : yss) = go xss yss
    go (_ :^ 0 : xss) yss  = go xss yss
    go xss (_ :^ 0 : yss)  = go xss yss
    go [] yss = pure $ CList yss
    go _ [] = Nothing
    go ((x : xs) :^ 1 : xss) ((y : ys) :^ 1 : yss)
      | x == y    = go (xs :^ 1 : xss) (ys :^ 1 : yss)
      | otherwise = Nothing
    go (xs :^ n : xss) (ys :^ m : yss)
      | xs == ys, n <= m = go xss (ys :^ (m - n) : yss)
    go (xs :^ n : xss) yss
      | n > 1 = go (xs :^ 1 : xs :^ (n - 1) : xss) yss
    go xss (ys :^ n : yss)
      | n > 1 = go xss (ys :^ 1 : ys :^ (n - 1) : yss)

isPrefixOf :: (Pretty a, Eq a) => CList a -> CList a -> Bool
isPrefixOf xs ys = isJust $ dropPrefix xs ys

------------------------------------------------------------------------
-- Internal functions
------------------------------------------------------------------------

-- uncons -----------------------------------------------------------------

uncons :: CList a -> Maybe (a, CList a)
uncons (CList []) = Nothing
uncons (CList ([x] :^ n : ys))
  | n == 1    = pure (x, CList ys)
  | otherwise = pure (x, CList $ [x] :^ (n - 1) : ys)
uncons (CList ((x : xs) :^ n : ys))
  | n == 1    = pure (x, CList $ xs :^ 1 : ys)
  | otherwise = pure (x, CList $ xs :^ 1 : (x : xs) :^ (n - 1) : ys)
uncons (CList ([] :^ _ : ys)) = uncons (CList ys)

-- cons -------------------------------------------------------------------

cons :: Eq a => a -> CList a -> CList a
cons x xs = consRep ([x] :^ 1) xs

consRep :: Eq a => Rep [a] -> CList a -> CList a
consRep x (CList xs) = CList $ squash $ go x xs
  where
    go (_ :^ 0) zs = zs
    go ([] :^ _) zs = zs
    go (xs :^ n) (ys :^ m : zs)
      | xs == ys                = go (ys :^ (n + m)) zs
    go (xs :^ n) (ys :^ m : zs)
      | Just xs' <- dropSuffix ys xs = go (xs :^ (n - 1)) $ go (xs' :^ 1) $ go (ys :^ (m + 1)) zs
    go (xs :^ n) (ys :^ 1 : zs)
      | Just ys' <- dropPrefixL xs ys = go (xs :^ (n + 1)) $ go (ys' :^ 1) zs
    go (xs :^ 1) ((y : ys) :^ 1 : zs) = go ((xs ++ [y]) :^ 1) $ go (ys :^ 1) zs
    go (xs :^ 1) ys = compress xs ++ ys
    go x xs = x : xs

    compress [] = []
    compress (x : xs) = go ([x] :^ 1) xs
      where
        go (xs :^ n) ys
          | Just zs <- dropPrefixL xs ys = go (xs :^ (n + 1)) zs
        go (xs :^ 1) (y : ys) = go ((xs ++ [y]) :^ 1) ys
        go r (y : ys) = r : go ([y] :^ 1) ys
        go r [] = [r]

    squash [] = []
    squash (x : xs) = goS [x] xs
      where
        goS xs ys
          | Just zs <- dropPrefixL xs ys = go (toList (CList xs) :^ 2) zs
        goS xs (ys :^ n : zs)
          | n > 1, Just (CList []) <- dropPrefix (CList xs) (CList [ys :^ 1]) = ys :^ (n + 1) : zs
        goS xs (y : ys) = goS (xs ++ [y]) ys
        goS xs [] = xs

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

dropPrefixL :: Eq a => [a] -> [a] -> Maybe [a]
dropPrefixL      []       ys  = pure ys
dropPrefixL (x : xs) (y : ys) = guard (x == y) *> dropPrefixL xs ys
dropPrefixL (_ :  _)      []  = Nothing

dropSuffix :: Eq a => [a] -> [a] -> Maybe [a]
dropSuffix xs ys = List.reverse <$> dropPrefixL (List.reverse xs) (List.reverse ys)

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

newtype Seq a = Seq [a]

instance Pretty a => Pretty (Seq a) where
  pPrintPrec l p (Seq [])  = "EMPTY"
  pPrintPrec l p (Seq [x]) = pPrintPrec l p x
  pPrintPrec l p (Seq xs)  = parensIf (p > 0) $ hcat $ map (pPrintPrec l 1) xs

instance Pretty a => Pretty (CList a) where
  pPrintPrec _ _ (CList [])         = "ε"
  pPrintPrec l p (CList [[x] :^ 1]) = pPrintPrec l p x
  pPrintPrec _ p (CList xs)         = parensIf (p > 0) $ pPrint $ Seq $ (map . fmap) Seq xs

instance Pretty a => Pretty (Rep a) where
  pPrintPrec l p (x :^ n)
    | n == 1    = pPrintPrec l p x
    | otherwise = parensIf (p > 1) $ pPrintPrec l 2 x <> pow n
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

instance Arbitrary a => Arbitrary (Rep a) where
  arbitrary = (:^) <$> arbitrary <*> choose (1, 8)
  shrink (x :^ n) =
    [ x :^ n | x <- shrink x ] ++
    [ x :^ n | n <- shrink n, n > 0 ]

instance Arbitrary a => Arbitrary (RawCList a) where
  arbitrary = Raw . CList <$> arbitrary
  shrink (Raw (CList xs)) = Raw . CList <$> shrink xs

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
prop_cons x xs = counterexampleP (vcat [ "x    =" <+> pPrint x
                                       , "xs   =" <+> pPrint xs
                                       , "x:xs =" <+> pPrint (cons x xs)
                                       ]) $
  conjoin [ toList (cons x xs) === x : toList xs
          , invariant xs ==> prop_invariant (cons x xs)
          ]

-- Operation: <> ----------------------------------------------------------

prop_append :: CList Bit -> CList Bit -> Property
prop_append xs ys = counterexampleP (vcat [ "xs       =" <+> pPrint xs
                                          , "ys       =" <+> pPrint ys
                                          , "xs <> ys =" <+> pPrint zs ]) $
    conjoin [ toList zs === toList xs ++ toList ys
            , prop_invariant zs ]
  where
    zs = xs <> ys

-- Operation: isPrefixOf --------------------------------------------------

prop_isPrefixOf :: RawCList Bit -> RawCList Bit -> Property
prop_isPrefixOf (Raw xs) (Raw ys) = check xs ys .&&. check ys xs
  where
    check xs ys =
      counterexampleP (vcat [ "xs  =" <+> pPrint xs
                            , "ys  =" <+> pPrint ys
                            , "xsL =" <+> pPrint xsL
                            , "ysL =" <+> pPrint ysL
                            ]) $
        isPrefixOf xs ys === List.isPrefixOf xsL ysL
      where
        xsL = toList xs
        ysL = toList ys

-- Operation: uncons ------------------------------------------------------

prop_uncons :: CList Bit -> Property
prop_uncons xs =
  case uncons xs of
    Nothing -> xs === mempty
    Just (x, ys) ->
      counterexampleP (vcat [ "xs =" <+> pPrint xs
                            , "   =" <+> pPrint x <+> ":" <+> pPrint ys
                            ]) $
        conjoin [ prop_invariant ys
                , cons x ys === xs
                ]

-- Invariant checking -----------------------------------------------------

invariant :: (Eq a, Show a, Pretty a) => CList a -> Bool
invariant = isRight . checkInvariant

checkInvariant :: (Eq a, Show a, Pretty a) => CList a -> Either Doc ()
checkInvariant xs@(CList cs) = mapLeft ("Invariant failed for" <+> (pPrint xs <> ":") $$) $ do
    sequence_ [ Left $ "Exponent too small:" <+> pPrint x | x@(_ :^ n) <- cs, n < 1 ]
    checkConsecutive cs
    checkCompact xs
  where
    checkConsecutive (xs :^ n : ys :^ m : zs)
      | xs == ys = Left $ sep [ "Unmerged repeats"
                              , nest 2 $ pPrint (Seq xs :^ n)
                              , nest 2 $ pPrint (Seq ys :^ m)
                              ]
    checkConsecutive (x : xs) = checkConsecutive xs
    checkConsecutive []       = pure ()

    checkCompact xs = do
        checkFolds . unCList $ reverse xs
        mapM_ localRepeat $ unCList xs
        globalRepeat $ unCList xs
      where
        checkFolds (xs :^ n : pre)
          | List.isPrefixOf xs (toList (CList pre)) = Left $ sep [ pPrint $ reverse $ CList [xs :^ n]
                                                                 , "should expand into"
                                                                 , pPrint $ reverse $ CList pre
                                                                 ]
        checkFolds (_ : xs) = checkFolds xs
        checkFolds [] = pure ()

        cleanPrefix :: Eq a => [Rep [a]] -> [Rep [a]] -> Bool
        cleanPrefix xs ys = any ((== toList (CList xs)) . toList . CList) $ inits ys

        globalRepeat [] = pure ()
        globalRepeat (x : xs) = go [x] xs
          where
            go xs ys
              | cleanPrefix xs ys =
                  Left $ sep [ pPrint $ CList xs
                             , "should fold into"
                             , pPrint $ CList ys
                             ]
            go xs (y : ys) = go (xs ++ [y]) ys
            go _ _ = pure ()

        localRepeat top@((x : xs) :^ n)
          | n == 1    = check [x] xs
          | otherwise = pure ()
          where
            check xs ys
              | List.isPrefixOf xs ys = Left $ hsep ["Repeated", pPrint (Seq xs), "in", pPrint (CList [top])]
            check xs (y : ys) = check (xs ++ [y]) ys
            check _ [] = pure ()
        localRepeat ([] :^ n) = Left "Repeat of empty list"

prop_invariant :: CList Bit -> Property
prop_invariant xs = case checkInvariant xs of
  Left err -> counterexampleP err False
  Right () -> property True

-- Running all the properties ---------------------------------------------

return []
qcAll :: (Property -> Property) -> IO Bool
qcAll f = $forAllProperties (quickCheckResult . f)
