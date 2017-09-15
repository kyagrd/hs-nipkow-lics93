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
import           Data.Char               (isUpper)
import           Data.List               hiding (insert, map, null)
import           Data.Map.Strict         hiding (foldr, insert, map, mapMaybe,
                                          null)
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           Syntax
import           Unbound.LocallyNameless

expand :: Fresh m => Map Nm Tm -> Tm -> m Tm
expand s v@(Var x) = case M.lookup x s of { Nothing -> pure v; Just u -> expand s u }
expand s (App t1 t2) = App <$> expand s t1 <*> expand s t2
expand s (Lam b) = do { (x,t) <- unbind b; lam x <$> expand s t }

u :: Fresh m => ([(Tm, Tm)], Map Nm Tm) -> m (Map Nm Tm)
u ([], s) = return s
u ((t1,t2):es, s) = do t1' <- devar s t1
                       t2' <- devar s t2
                       u =<< ustep ((t1',t2'):es, s)

-- assuming all the terms are in beta-normal form
ustep :: Fresh m => ([(Tm,Tm)], Map Nm Tm) -> m ([(Tm,Tm)], Map Nm Tm)
ustep p@([], s) = return p
-- on the fly eta-expansion
ustep ((Lam b1, Lam b2):es, s) = do Just(_,t1,_,t2) <- unbind2 b1 b2
                                    pure ((t1,t2):es, s)
ustep ((t1, Lam b):es, s)      = do (x,t) <- unbind b
                                    pure ((App t1 (Var x), t):es, s)
ustep ((Lam b, t2):es, s)      = do (x,t) <- unbind b
                                    pure ((t, App t2 (Var x)):es, s)
-- the real unification work
ustep ((t1, t2):es, s) -- require caller of ustep to invoke devar on t1 and t2
  -- rigidrigid
  | rigid x1 && rigid x2 && x1==x2 && len1==len2
                             = pure (zip ts1 ts2++es, s)
  | rigid x1 && rigid x2     = fail $ show (t1, t2) ++ " cannot unify because "
                                    ++ show x1 ++ " /= " ++ show x2
  | rigid x1 && occurs x2 t1 = fail $ show (t1, t2) ++ " cannot unify because "
                                    ++ show x2 ++ " occurs in " ++ show t1
  | rigid x2 && occurs x1 t2 = fail $ show (t1, t2) ++ " cannot unify because "
                                    ++ show x1 ++ " occurs in " ++ show t2
  | rigid x1  = (,) es <$> (proj vs2 s =<< devar s t1) -- rigidflex
  | rigid x2  = (,) es <$> (proj vs1 s =<< devar s t2) -- flexrigid
  | x1==x2 && len1 == len2   =
                do h <- Var <$> fresh (s2n "H") -- flexflex1
                   let s' = M.insert x1 (lamMany vs1 $ appMany h (Var<$>xs)) s
                   pure (es, s')
  | x1==x2                   = fail $ show (t1, t2) ++ " cannot unify because "
                                    ++ "they have different number of args"
  | otherwise = do h <- Var <$> fresh (s2n "H") -- flexflex2
                   let f1 = lamMany vs1 $ appMany h (Var<$>zs)
                       f2 = lamMany vs2 $ appMany h (Var<$>zs)
                   let s' = M.insert x1 f1 . M.insert x2 f2 $ s
                   pure (es, s')
  where
     Var x1 : ts1 = unfoldApp t1
     Var x2 : ts2 = unfoldApp t2
     len1 = length ts1
     len2 = length ts2
     vs1 = map (\(Var x) -> x) ts1
     vs2 = map (\(Var x) -> x) ts2
     xs = [x1 | (x1,x2)<-zip vs1 vs2, x1==x2]
     zs = [x1 | x1 <- vs1, x2 <- vs2, x1==x2]

proj :: Fresh m => [Nm] -> Map Nm Tm -> Tm -> m (Map Nm Tm)
proj vs s t = undefined -- TODO

appMany t ts = foldl1 App (t:ts)

lamMany = foldr ((.) . lam) id

devar :: Fresh m => Map Nm Tm -> Tm -> m Tm
devar s t = do t' <- expand s t
               if rigid x || t == t' then pure t else redapps t' ts
  where
    Var x : ts = unfoldApp t

redapps (Lam b) (t:ts) = do (x,t1) <- unbind b
                            redapps (subst x t t1) ts
redapps t       ts     = return $ appMany t ts

{-
      t' = expand s t
      s' = M.insert x t' (subst x t' <$> s)
-}

rigid = not . isUpper . head . name2String

unfoldApp = reverse . unstackApp

unstackApp (App t1 t2) = t2 : unstackApp t1
unstackApp t           = [t]
