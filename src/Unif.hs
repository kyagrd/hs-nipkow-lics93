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
(.+) :: Fresh m => (Nm,Tm) -> m ([(Tm,Tm)],Map Nm Tm) -> m ([(Tm,Tm)],Map Nm Tm)
(x,t) .+ mess = do (es,s) <- mess
                   t' <- expand' s t
                   let s' = M.insert x t' (subst x t' <$> s)
                   let es' | M.member x s = (s!x,t'):es
                           | otherwise    = es
                   return (es', s')

u :: Fresh m => ([(Tm, Tm)], Map Nm Tm) -> m (Map Nm Tm)
u ([], s) = return s
u ess     = u =<< ustep' ess

ustep' ess@([], _) = return ess
ustep' ((t1,t2):es, s) = do t1' <- devar s t1
                            t2' <- devar s t2
                            ustep ((t1',t2'):es, s)

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
    -- flexflex
    (V _, V _)
      -- flexflex1
      | xF==xG && len1/=len2 -> cantUnify "their arguments differ"
      | xF==xG && ts1 == ts2 -> pure (es, s)
      | xF==xG -> do h <- V <$> fresh (s2n "H")
                     (xF, hnf bs1 h xs) .+ pure(es, s)
      -- flexflex2
      | subset bs1 bs2 -> (xG, hnf bs2 tF ts1) .+ pure(es, s)
      | subset bs2 bs1 -> (xF, hnf bs1 tG ts2) .+ pure(es, s)
      | otherwise -> do h <- V <$> fresh (s2n "H")
                        (xF, hnf bs1 h zs) .+ (xG, hnf bs2 h zs) .+ pure(es, s)
    -- flexrigid
    (V _, _) -> trace ("flexrigid "++show((t1,t2):es)) $
                do xF't2 <- occ s xF t2
                   when xF't2 . cantUnify $ show xF++" occurs in "++show t2
                   (es',s') <- (xF, lamMany bs1 t2) .+ pure(es, s)
                   proj' bs1 (es',s') t2
    -- rigidflex
    (_, V _) -> trace ("rigidflex "++show((t1,t2):es)) $
                do xG't1 <- occ s xG t1
                   when xG't1 . cantUnify $ show xG++" occurs in "++show t1
                   (es',s') <- (xG, lamMany bs2 t1) .+ pure(es, s)
                   proj' bs2 (es',s') t1
    -- rigidrigid
    _ | xF==xG && len1==len2 -> pure (zip ts1 ts2 ++ es, s)
      | xF/=xG               -> cantUnify $ show xF++" /= "++show xG
      | otherwise            -> cantUnify "their arguments differ"
  where
     tF : ts1 = unfoldApp t1; xF = nm2tm tF; bs1 = unB<$>ts1; len1 = length ts1
     tG : ts2 = unfoldApp t2; xG = nm2tm tG; bs2 = unB<$>ts2; len2 = length ts2
     xs = [x1 | (x1,x2)<-zip ts1 ts2, x1==x2]
     zs = [x1 | x1 <- ts1, x2 <- ts2, x1==x2]
     cantUnify whymsg = fail $ "cannot unify " ++ show (t1,t2)
                            ++ " because " ++ whymsg

unB (B x) = x
unB t     = error $ show t ++ " is not a bound variable"

occ s x t = occurs x <$> expand s t

subset xs ys = all (`elem` ys) xs

proj :: Fresh m => [Nm] -> ([(Tm,Tm)],Map Nm Tm) -> Tm -> m ([(Tm,Tm)],Map Nm Tm)
proj vs ess t =
  trace ("\nproj ("++show vs++") ("++show ess++") ("++show t++")\n***\n") $
  case unfoldApp t of
    [Lam b]         -> do { (x,tb) <- unbind b; proj' (x:vs) ess tb }
    C x : ts        -> foldlM (proj' vs) ess ts
    B x : ts
      | x `elem` vs -> foldlM (proj' vs) ess ts
      | otherwise   -> fail $ "unbound rigid variable "++ show x
    V x : ts        -> let ys = unB <$> ts
                           zs = [B y | y<-ys, y `elem` vs]
                       in if subset ys vs then pure ess
                                          else do h <- V <$> fresh (s2n "H")
                                                  (x, hnf ys h zs) .+ pure ess
    _ -> error $ "non-reachable pattern: t = "++show t
                         ++" ; unfoldApp t = "++show(unfoldApp t)

-- helper function wrapping proj with devar
proj' vs ess@(es,s) t = proj vs ess =<< devar s t

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
