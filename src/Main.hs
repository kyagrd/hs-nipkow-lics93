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

idTm = lam x (var x)

t1 = lam x $ app (var y) (app (var $ s2n "F") (var x))
t2 = lam x $ app (var y) (app (con c) (appMany (var $ s2n "G") [var y,var x]))

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
