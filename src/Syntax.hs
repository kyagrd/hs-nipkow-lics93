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

data Tm = V Nm -- logic variable   (non rigid)
        | B Nm -- bound variable   (rigid)
        | C Nm -- global constants (rigid)
        | Lam (Bind Nm Tm)
        | App Tm Tm
     deriving (Eq,Ord,Show)

instance Eq (Bind Nm Tm) where (==) = aeq
instance Ord (Bind Nm Tm) where compare = acompare

$(derive [''Tm])

instance Alpha Tm

instance Subst Tm Tm where
  isvar (V x) = Just (SubstName x) -- for logic variable substitution
  isvar (B x) = Just (SubstName x) -- for reduction, alpha conviersion
  isvar _     = Nothing

lam x = Lam . bind x
app = App

occurs :: Alpha t => Nm -> t -> Bool
occurs x t = x `elem` (fv t :: [Nm])

---------------------------------------------------------------------------
-- below are not used in the HOpattern-unif algorithm; just some utility
---------------------------------------------------------------------------

stepBN :: Fresh f => Tm -> f Tm
stepBN v@(V _)           = pure v
stepBN v@(B _)           = pure v
stepBN v@(C _)           = pure v
stepBN (Lam b)           = do (x,t) <- unbind b; Lam . bind x <$> stepBN t
stepBN (App (Lam b) t2)  = do (x,t) <- unbind b; stepBN $ subst x t2 t
stepBN (App t1@(V _) t2) = App <$> pure t1 <*> stepBN t2
stepBN (App t1@(B _) t2) = App <$> pure t1 <*> stepBN t2
stepBN (App t1@(C _) t2) = App <$> pure t1 <*> stepBN t2
stepBN (App t1 t2)       = App <$> stepBN t1 <*> pure t2

fixM :: (Eq t, Monad m) => (t -> m t) -> t -> m t
fixM step t = do t' <- step t
                 if t == t' then pure t else fixM step t'

whnf :: Tm -> Bool
whnf (V _)            = True
whnf (B _)            = True
whnf (C _)            = True
whnf (App (Lam _) t2) = False
whnf (App t1 t2)      = whnf t1 && whnf t2
whnf (Lam _)          = True

stepWH :: Fresh f => Tm -> f Tm
stepWH v@(V _)           = pure v
stepWH v@(B _)           = pure v
stepWH v@(C _)           = pure v
stepWH v@(Lam _)         = pure v
stepWH (App (Lam b) t2)  = do (x,t) <- unbind b; stepBN $ subst x t2 t
stepWH (App t1@(V _) t2) = App <$> pure t1 <*> stepBN t2
stepWH (App t1@(B _) t2) = App <$> pure t1 <*> stepBN t2
stepWH (App t1@(C _) t2) = App <$> pure t1 <*> stepBN t2
stepWH (App t1 t2)       = App <$> stepBN t1 <*> pure t2

normBeta, normWH :: Fresh m => Tm -> m Tm
normBeta = fixM stepBN
normWH = fixM stepWH
