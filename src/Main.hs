module Main where

import           Syntax
import Unbound.LocallyNameless

main :: IO ()
main = do
  putStrLn "hello world"
  print $ Lam (bind (s2n "x") (Var (s2n "x")))
