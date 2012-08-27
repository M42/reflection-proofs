module SKI where

-- figure out types of composition etc.
--


s :: (a -> (b -> c)) -> (a -> b) -> (a -> c)
s f g x = f x (g x)

k :: a -> (b -> a)
k x y = x

i :: a -> a
i x = x

o :: (b -> c) -> (a -> b) -> a -> c
o = s ( k ( s ) ) (k)

compose g f = o g f

f = s (k (s (k (s)))) (s (k (s )) (k))

{-weaken 0 acc = acc-}
{-weaken n acc = weaken (n-1) (k (acc ))-}
