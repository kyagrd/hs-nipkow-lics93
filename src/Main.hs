{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import           Syntax
import           Unbound.LocallyNameless
import           Unif

x = s2n "x"
y = s2n "y"
z = s2n "z"
w = s2n "w"

idTm = lam x (var x)

main :: IO ()
main = do
  putStrLn "hello world"
  print idTm
  print . runFreshM . stepBN $ idTm `App` idTm
