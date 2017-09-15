{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module Syntax    where

-- import           Control.Applicative
import           Unbound.LocallyNameless

type Nm = Name Tm

data Tm = Var Nm | Lam (Bind Nm Tm) | App Tm Tm deriving Show

$(derive [''Tm])

instance Alpha Tm

instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing

var = Var
lam x = Lam . bind x
app = App

occurs :: Alpha t => Nm -> t -> Bool
occurs x t = x `elem` (fv t :: [Nm])

stepBN :: Fresh f => Tm -> f Tm
stepBN v@(Var _)           = pure v
stepBN (Lam b)             = do (x,t) <- unbind b; Lam . bind x <$> stepBN t
stepBN (App (Lam b) t2)    = do (x,t) <- unbind b; stepBN $ subst x t2 t
stepBN (App t1@(Var _) t2) = App <$> pure t1 <*> stepBN t2
stepBN (App t1 t2)         = App <$> stepBN t1 <*> pure t2

whnf :: Tm -> Bool
whnf (Var _)     = True
whnf (App t1 t2) = whnf t1 && whnf t2
whnf (Lam _)     = True

stepWH :: Fresh f => Tm -> f Tm
stepWH v@(Var _)           = pure v
stepWH v@(Lam _)           = pure v
stepWH (App (Lam b) t2)    = do (x,t) <- unbind b; stepBN $ subst x t2 t
stepWH (App t1@(Var _) t2) = App <$> pure t1 <*> stepBN t2
stepWH (App t1 t2)         = App <$> stepBN t1 <*> pure t2
