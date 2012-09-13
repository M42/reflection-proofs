{-# LANGUAGE ViewPatterns #-}
module Fact where

import Prelude hiding (const, succ, pred)

true = \ x -> \ y -> x
const = true
false = \ x -> \ y -> y
ifthenelse = \ a -> \ b -> \ c -> a b c

data Nat = Z
         | S Nat deriving (Show)

type Getal a = (a -> a) -> a -> a

{-cons = \ a -> \ b -> \ c -> ((c)a)b-}
{-head = \ x -> x true-}
{-tail = \ x -> x false-}

{-l0 :: Getal a-}
l0 = \ f -> \ x -> x
--l1 :: Getal a
l1 = \ f -> \ x -> f x
--l2 :: Getal a
l2 = \ f -> \ x -> f(f x)
--l3 :: Getal a
l3 = \ f -> \ x -> f(f(f x))

unit = \x -> x
test = \b -> \t -> \f -> b t f unit



--succ :: Getal a -> Getal a
succ  = \ n -> \ f -> \ x -> f (n f x)
--plus :: Getal a -> Getal a -> Getal a
plus  = \ m -> \ n -> \ f -> \ x -> m f (n f x)
--times :: Getal a -> Getal a -> Getal a
times = \ m -> \ n -> \ f -> \ x -> m (n f) x
--zeroQ :: Getal (a -> a -> a) -> a -> a -> a
zeroQ = \ n -> n (\ x -> false) true

fix :: (Getal a -> Getal a) -> Getal a
fix f = f (fix f)

{-pred = \ n -> n (\ g -> \ k -> zeroQ (g l1) k (plus (g k) l1)) (const l0) l0-}
pred = \ n -> \f -> \x -> n (\ g -> \ h -> h (g f)) (\ u -> x) (\u -> u)

{-fact :: Getal a -> Getal a-}
gg = fix (\fct -> \n ->             test (zeroQ n)
                                         (\dummy -> l1)
                                         (\dummy -> times (plus l1 l2) (fct l1)))
{-fact = fix gg-}
