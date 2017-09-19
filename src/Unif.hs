{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Unif where
import           Control.Applicative
import           Control.Monad
import           Data.Char               (isUpper)
import           Data.Foldable           (foldlM)
import           Data.List               hiding (insert, map, null)
import           Data.Map.Strict         hiding (foldl, foldr, insert, map,
                                          mapMaybe, null)
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           Syntax
import           Unbound.LocallyNameless

-- import           Debug.Trace
trace = flip const

emptyMap = M.empty

expand, expand' :: Fresh m => Map Nm Tm -> Tm -> m Tm
expand s v@(V x) = case M.lookup x s of { Nothing -> pure v; Just u -> expand s u }
expand s v@(B x) = pure v
expand s v@(C x) = pure v
expand s (App t1 t2) = App <$> expand s t1 <*> expand s t2
expand s (Lam b) = do { (x,t) <- unbind b; lam x <$> expand s t }

expand' s v@(V x) = case M.lookup x s of { Nothing -> pure v; Just u -> expand' s u }
expand' s v@(B x) = pure v
expand' s v@(C x) = pure v
expand' s (App t1 t2) = do { t1' <- expand' s t1; t2' <- expand' s t2; redapps t1' [t2'] }
expand' s (Lam b) = do { (x,t) <- unbind b; lam x <$> expand' s t }

infixr .+
(x,t) .+ s = M.insert x t s

u :: Fresh m => ([(Tm, Tm)], Map Nm Tm) -> m (Map Nm Tm)
u ([], s) = return s
u ((t1,t2):es, s) = do t1' <- devar s t1
                       t2' <- devar s t2
                       u =<< ustep ((t1',t2'):es, s)

ustep :: Fresh m => ([(Tm,Tm)], Map Nm Tm) -> m ([(Tm,Tm)], Map Nm Tm)
ustep p@([], s) = return p
-- on the fly eta-expansion
ustep ((Lam b1, Lam b2):es, s) = do Just(x,t1,_,t2) <- unbind2 b1 b2
                                    pure ((t1,t2):es, s)
ustep ((t1, Lam b):es, s)      = do (x,t) <- unbind b
                                    pure ((App t1 (B x), t):es, s)
ustep ((Lam b, t2):es, s)      = do (x,t) <- unbind b
                                    pure ((t, App t2 (B x)):es, s)
-- the real unification work
ustep ((t1, t2):es, s) =
  case (tF, tG) of
    -- flexflex1
    (V _, V _)
      | xF==xG && len1/=len2 -> cantUnify "their arguments differ"
      | xF==xG && ts1 == ts2 -> pure (es, s)
      | xF==xG      -> do h <- V <$> fresh (s2n "H")
                          pure (es, (xF, hnf bs1 h xs).+s)
      -- flexflex2
      | subset bs1 bs2 -> pure (es, (xG, hnf bs2 tF ts1).+s)
      | subset bs2 bs1 -> pure (es, (xF, hnf bs1 tG ts2).+s)
      | otherwise   -> do h <- V <$> fresh (s2n "H")
                          pure (es, (xF, hnf bs1 h zs).+(xG, hnf bs2 h zs).+s)
    -- flexrigid
    (V _, _) -> trace ("flexrigid "++show((t1,t2):es)) $
                do xF't2 <- occ s xF t2
                   when xF't2 . cantUnify $ show xF++" occurs in "++show t2
                   let s' = (xF, lamMany bs1 t2) .+ s
                   (,) es <$> (proj bs1 s' =<< devar s' t2)
    -- rigidflex
    (_, V _) -> trace ("rigidflex "++show((t1,t2):es)) $
                do xG't1 <- occ s xG t1
                   when xG't1 . cantUnify $ show xG++" occurs in "++show t1
                   let s' = (xG, lamMany bs2 t1) .+ s
                   (,) es <$> (proj bs2 s' =<< devar s' t1)
    -- rigidrigid
    _ | xF==xG && len1==len2 -> pure (zip ts1 ts2++es, s)
      | xF/=xG               -> cantUnify $ show xF++" /= "++show xG
      | otherwise            -> cantUnify "their arguments differ"
  where
     tF : ts1 = unfoldApp t1; xF = nm2tm tF; bs1 = unB<$>ts1; len1 = length ts1
     tG : ts2 = unfoldApp t2; xG = nm2tm tG; bs2 = unB<$>ts2; len2 = length ts2
     xs = [x1 | (x1,x2)<-zip ts1 ts2, x1==x2]
     zs = [x1 | x1 <- ts1, x2 <- ts2, x1==x2]
     subset xs ys = all (`elem` ys) xs
     cantUnify whymsg = fail $ "cannot unify " ++ show (t1,t2)
                            ++ " because " ++ whymsg

unB (B x) = x
unB t     = error $ show t ++ " is not a bound variable"

occ s x t = occurs x <$> expand s t

proj :: Fresh m => [Nm] -> Map Nm Tm -> Tm -> m (Map Nm Tm)
proj vs s t =
  trace ("\nproj ("++show vs++") ("++show s++") ("++show t++")\n***\n") $
  case unfoldApp t of
    [Lam b]         -> do { (x,tb) <- unbind b; proj (x:vs) s =<< devar s tb }
    [_]             -> error "non-reachable pattern"
    C x : ts        -> foldlM (\s t -> proj vs s =<< devar s t) s ts
    B x : ts
      | x `elem` vs -> foldlM (\s t -> proj vs s =<< devar s t) s ts
      | otherwise   ->  fail $ "unbound rigid variable "++ show x
    V x : ts        -> do h <- V <$> fresh (s2n "H")
                          let ys = unB <$> ts
                              zs = [B y | y<-ys, y `elem` vs]
                          pure $ (x, hnf ys h zs) .+ s

hnf vs h zs = lamMany vs $ appMany h zs

appMany t ts = foldl1 App (t:ts)

lamMany = foldr ((.) . lam) id

devar :: Fresh m => Map Nm Tm -> Tm -> m Tm
devar s t = case t1 of
              V x -> case M.lookup x s of
                       Just t' -> devar s =<< redapps t' ts
                       Nothing -> pure t
              _   -> pure t
  where t1 : ts = unfoldApp t

redapps (Lam b) (t:ts) = do (x,tb) <- unbind b
                            redapps (subst x t tb) ts
redapps t       ts     = return $ appMany t ts

nm2tm (V x) = x
nm2tm (B x) = x
nm2tm (C x) = x
nm2tm t     = error $ show t ++ " is neither variable nor constant"

unfoldApp = reverse . unstackApp

unstackApp (App t1 t2) = t2 : unstackApp t1
unstackApp t           = [t]
