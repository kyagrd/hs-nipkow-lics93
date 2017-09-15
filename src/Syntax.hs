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

occurs :: Alpha t => Nm -> t -> Bool
occurs x t = x `elem` (fv t :: [Nm])

whnf :: Tm -> Bool
whnf (Var _)     = True
whnf (App t1 t2) = whnf t1 && whnf t2
whnf (Lam _)     = True

{-
step (Var _) = Nothing
step (Lam _) = Nothing
step (App (Var _) _)
-}
