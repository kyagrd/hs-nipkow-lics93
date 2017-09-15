{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- {-# LANGUAGE ScopedTypeVariables       #-}
-- {-# LANGUAGE StandaloneDeriving        #-}
-- {-# LANGUAGE TemplateHaskell           #-}
-- {-# LANGUAGE UndecidableInstances      #-}
module Unif where
import           Control.Applicative
import           Data.List               hiding (insert, map, null)
import           Data.Map.Strict         hiding (insert, map, mapMaybe, null)
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           Syntax
import           Unbound.LocallyNameless
---- -# ANN module "HLint: ignore Use fmap" #-}
---- -# ANN module "HLint: ignore Use mappend" #-}

{-
Alternative implemntation of the rule-based unfication algorithm U
from the unfication chapter of the "handbook of automated reasoning"
http://www.cs.bu.edu/~snyder/publications/UnifChapter.pdf

Instead of applying to the unification to the rest of the equation es,
make a feedback when there already exists a mapping from same variable.
Becuase the variables in the equations are not substituted by the current
substitution, we need to use a helper function expand that expand terms
according to the current substitution.
-}


expand :: Fresh f => Map Nm Tm -> Tm -> f Tm
expand s v@(Var x) = case M.lookup x s of { Nothing -> return v; Just u -> expand s u }
expand s (App t1 t2) = App <$> expand s t1 <*> expand s t2
expand s (Lam b) = do { (x,t) <- unbind b; t' <- expand s t; return $ lam x t' }

{-
ustep :: Monad m => ([(Tm,Tm)], Map Nm Tm) -> m ([(Tm,Tm)], Map Nm Tm)
ustep ([], s)                       = return s
ustep ((t1@(Var x), t2@(Var y)):es, s) | x == y  = return (es, s)
                                       | x > y   = ustep ((t2,t1):es, s)
ustep ((Var t1, Lam t2):es, s)      = undefined
ustep ((Var t1, App t21 t22):es, s) = undefined
ustep ((Lam t1, Var t2):es, s)      = undefined

ustep ((Lam b1, Lam b2):es, s) = do Just _ t1 _ t2 <- unbind2 b1 b2
                                    ustep ((b1,b2):es, s)
ustep ((Lam t1, App t21 t22):es, s) = undefined
ustep ((App t11 t12, Var t2):es, s) = undefined
ustep ((App t11 t12, Lam t2):es, s) = undefined
ustep ((App t11 t12, App t21 t22):es, s) = undefined
-}
{-
ustep ((t1@(App t11 t12), t2@(App t21 t22)) : es, s)
  | f1==f2 && length ts1==length ts2 = return (zip ts1 ts2 ++ es, s)
ustep ((t1@(D _ _), t2@(Var x)) : es, s) = return (t2 `Eq` t1 : es, s)
ustep ((t1@(Var x), t2@(Var y)) : es, s)
  | x == y = return (es, s)
  | x > y = ustep (t2 `Eq` t1 : es, s)
ustep ((Var x, t) : es, s)
  | occurs x t' = fail $ show x ++" occurs in "++show t
                      ++ let t' = expand s t in
                          if t /= t' then ", that is, "++show t' else ""
  | M.member x s = return ((s!x,t') : es, s')
  | otherwise = return (es, s')
    where
      t' = expand s t
      s' = M.insert x t' (subst x t' <$> s)

u :: Monad m => ([(Tm,Tm)], Map Nm Tm) -> m (Map Nm Tm)
u ([], s) = return s
u (es, s) = u =<< ustep (es, s)
-}
