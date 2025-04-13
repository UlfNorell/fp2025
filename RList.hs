
module RList where

data RLE a = RLE a {-# UNPACK #-} !Int
  deriving (Eq, Ord, Show, Functor)

newtype RList a = RList [RLE a]
  deriving (Eq, Ord, Show, Functor)

instance Eq a => Semigroup (RList a) where
  RList [] <> ys = ys
  RList [RLE x n] <> RList (RLE y m : ys)
    | x == y = RList (RLE y (n + m) : ys)
  RList (x : xs) <> RList ys = RList (x : zs)
    where
      RList zs = RList xs <> RList ys

instance Eq a => Monoid (RList a) where
  mempty = RList []

expand :: RList a -> [a]
expand (RList xs) = concat [ replicate n x | RLE x n <- xs ]

toRList :: Eq a => [a] -> RList a
toRList = foldr consR NilR

lengthR :: RList a -> Int
lengthR (RList xs) = sum [ n | RLE _ n <- xs ]

consR :: Eq a => a -> RList a -> RList a
consR x (RList []) = RList [RLE x 1]
consR x (RList xs@(RLE y n : ys))
  | x == y    = RList (RLE y (n + 1) : ys)
  | otherwise = RList (RLE x 1 : xs)

headR :: RList a -> Maybe a
headR (RList []) = Nothing
headR (RList (RLE x _ : _)) = Just x

dropR :: Int -> RList a -> RList a
dropR 0 xs = xs
dropR n (RList (RLE x m : xs))
  | n < m     = RList (RLE x (m - n) : xs)
  | otherwise = dropR (n - m) (RList xs)

unconsR :: RList a -> Maybe (a, RList a)
unconsR (RList []) = Nothing
unconsR (RList (RLE x n : xs))
  | n > 1     = Just (x, RList (RLE x (n - 1) : xs))
  | otherwise = Just (x, RList xs)

infixr 5 :@
pattern (:@) :: Eq a => a -> RList a -> RList a
pattern x :@ xs <- (unconsR -> Just (x, xs))
  where
    x :@ xs = consR x xs

pattern NilR = RList []
{-# COMPLETE NilR, (:@) #-}

