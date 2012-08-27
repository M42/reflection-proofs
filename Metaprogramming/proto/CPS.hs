module CPS where

import Data.List
import Debug.Trace
import Test.QuickCheck
import Control.Monad


-- same as above, but with Halt included.
data Exp = Vr Int
         | Ap Exp Exp
         | Lm Exp
         | Const String
         | Halt
         deriving (Show, Eq)

g = Vr 0
a = Vr 1

example0 :: Exp
example0 = Ap g a


increase :: Exp -> Exp
increase (Vr n) = Vr (n + 1)
increase a = a


tc :: Exp -> Exp -> Exp
tc (Halt   ) c = Ap c (mh Halt)
tc (Lm body) c = Ap c (mh (Lm body))
tc (Vr n   ) c = Ap c (mh (Vr n   ))
tc (Const s) c = Ap c (mh (Const s))
tc (Ap f e ) c = tk f (\ df ->
                        (tk e (\ de ->
                             (Ap (Ap df de) c))))

tk :: Exp -> (Exp -> Exp) -> Exp
tk (Halt   ) k = k (mh Halt)
tk (Lm body) k = k (mh (Lm body))
tk (Vr n   ) k = k (mh (Vr n   ))
tk (Const s) k = k (mh (Const s))
tk (Ap f e ) k = tk f (\ df ->
                        (tk e (\ de ->
                                (Ap (Ap df de) cont))))
            where cont = Lm (k (Vr 0))

mh :: Exp -> Exp
mh (Lm wtl) = Lm (Lm (tc (increase wtl) (Vr 0)))
mh (Vr n)   = Vr n
mh (Const s) = Const s
mh (Halt) = Halt

type Env = [Exp]

-- beta reduction
reduce :: Env -> Exp -> Exp
reduce env Halt      = Halt
reduce env (Const s) = Const s
reduce env (Lm b)    = Lm b
reduce env (Vr n)    = env !! n
reduce env (Ap f e)  = app env (reduce env f) (reduce env e)
  where
    app :: Env -> Exp -> Exp -> Exp
    app env (Lm b) x = reduce (x : env) b
    app env f      v = Ap f v

-- the identity combinator
i = Lm (Vr 0)


-- a few unit tests for CPS
prop_0 = Lm (Lm (Ap (Vr 0) (Vr 1))) == reduce [] (tc i i)

prop_1 = Ap (Ap (Vr 0) (Vr 1)) Halt == tc (Ap g a) Halt


factCPS 0 k = k 1
factCPS n k = factCPS (n-1) (\ f -> mult f n k)

mult :: Int -> Int -> (Int -> a) -> a
mult n m k = k (n * m)

