{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import           Syntax
import           Unbound.LocallyNameless
import           Unif

x = s2n "x"
y = s2n "y"
z = s2n "z"
w = s2n "w"
c = s2n "c"

idTm = lam x (B x)

-- Note: you should keep logic variables and bound variables disjoint
-- so that logic variables are not accidently captured by Bind

t1 = lam x $ app (B y) (app (V$s2n"F") (B x))
t2 = lam x $ app (B y) (app (C c) (appMany (V$s2n"G") [B y,B x]))

main :: IO ()
main = do
  putStrLn "hello world"
  print idTm
  print . runFreshM . stepBN $ idTm `App` idTm
  let s = runFreshM $ u ([(t1,t2)],emptyMap)
  print s
  print . runFreshM $ expand  s (V$s2n"F")
  print . runFreshM $ expand' s (V$s2n"F")
  print . runFreshM $ expand  s (V$s2n"G")
  print . runFreshM $ expand' s (V$s2n"G")
