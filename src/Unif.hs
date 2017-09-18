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
expand s v@(C x) = pure v
expand s (App t1 t2) = App <$> expand s t1 <*> expand s t2
expand s (Lam b) = do { (x,t) <- unbind b; lam x <$> expand s t }

expand' s v@(V x) = case M.lookup x s of { Nothing -> pure v; Just u -> expand' s u }
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

-- assuming all the terms are in beta-normal form
ustep :: Fresh m => ([(Tm,Tm)], Map Nm Tm) -> m ([(Tm,Tm)], Map Nm Tm)
ustep p@([], s) = return p
-- on the fly eta-expansion
ustep ((Lam b1, Lam b2):es, s) = do Just(x,t1,_,t2) <- unbind2 b1 b2
                                    pure ((t1,t2):es, s)
ustep ((t1, Lam b):es, s)      = do (x,t) <- unbind b
                                    pure ((App t1 (V x), t):es, s)
ustep ((Lam b, t2):es, s)      = do (x,t) <- unbind b
                                    pure ((t, App t2 (V x)):es, s)
-- the real unification work
ustep ((t1, t2):es, s) -- caller invokes devar; see definition of u
  | rigid x1 && rigid x2 && x1==x2 && len1==len2 = pure (zip ts1 ts2++es, s)
  | rigid x1 && rigid x2 && x1/=x2 = cantUnify $ show x1++" /= "++show x2
  | rigid x1 && rigid x2           = cantUnify "their argumnets differ"
  | rigid x1 = trace ("rigidflex "++show((t1,t2):es)) $
               do x2't1 <- occ s x2 t1 -- rigidflex
                  when x2't1 . cantUnify $ show x2++" occurs in "++show t1
                  let s' = (x2, lamMany vs2 t1) .+ s
                  (,) es <$> (proj vs2 s' =<< devar s' t1)
  | rigid x2 = trace ("flexrigid "++show((t1,t2):es)) $
               do x1't2 <- occ s x1 t2 -- flexrigid
                  when x1't2 . cantUnify $ show x1++" occurs in "++show t2
                  let s' = (x1, lamMany vs1 t2) .+ s
                  (,) es <$> (proj vs1 s' =<< devar s' t2)
  -- flexflex1
  | x1==x2 && ts1 == ts2 = pure (es, s)
  | x1==x2 && len1==len2 = do h <- V <$> fresh (s2n "H")
                              pure (es, (x1, hnf vs1 h xs) .+ s)
  | x1==x2               = cantUnify "their arguments differ"
  -- flexflex2
  | subset vs1 vs2 = pure (es, (x2, hnf vs2 (V x1) vs1) .+ s)
  | subset vs2 vs1 = pure (es, (x1, hnf vs1 (V x2) vs2) .+ s)
  | otherwise = do h <- V <$> fresh (s2n "H")
                   pure (es, (x1, hnf vs1 h zs) .+ (x2, hnf vs2 h zs) .+ s)
  where
     x1Tm : ts1 = unfoldApp t1; x1 = nameFromTm x1Tm; len1 = length ts1
     x2Tm : ts2 = unfoldApp t2; x2 = nameFromTm x2Tm; len2 = length ts2
     vs1 = map (\(V x) -> x) ts1
     vs2 = map (\(V x) -> x) ts2
     xs = [x1 | (x1,x2)<-zip vs1 vs2, x1==x2]
     zs = [x1 | x1 <- vs1, x2 <- vs2, x1==x2]
     subset xs ys = all (`elem` ys) xs
     cantUnify whymsg = fail $ "cannot unify " ++ show (t1,t2)
                            ++ " because " ++ whymsg


occ s x t = occurs x <$> expand s t

proj :: Fresh m => [Nm] -> Map Nm Tm -> Tm -> m (Map Nm Tm)
proj vs s t = -- TODO no syntax for constants yet
  trace ("\nproj ("++show vs++") ("++show s++") ("++show t++")\n***\n") $
  case unfoldApp t of
    [Lam b] -> do { (x,tb) <- unbind b; proj (x:vs) s =<< devar s tb }
    [_]     -> error "non-reachable pattern"
    C x : ts             -> foldlM (\s t -> proj vs s =<< devar s t) s ts
    V x : ts | rigid x && x `elem` vs
                         -> foldlM (\s t -> proj vs s =<< devar s t) s ts
             | rigid x   -> fail $ "unbound rigid variable "++ show x
             | otherwise -> do h <- V <$> fresh (s2n "H")
                               let ys = map (\(V v) -> v) ts
                                   zs = [y | y<-ys, y `elem` vs]
                               pure $ (x, hnf ys h zs) .+ s

hnf vs h zs = lamMany vs $ appMany h (V<$>zs)

appMany t ts = foldl1 App (t:ts)

lamMany = foldr ((.) . lam) id

devar :: Fresh m => Map Nm Tm -> Tm -> m Tm
devar s t =
  case t1 of
    V x | not (rigid x)
        -> case M.lookup x s of
             Just t' -> devar s =<< redapps t' ts
             Nothing -> pure t
    _   -> pure t
  where t1 : ts = unfoldApp t

redapps (Lam b) (t:ts) = do (x,tb) <- unbind b
                            redapps (subst x t tb) ts
redapps t       ts     = return $ appMany t ts

rigid = not . isUpper . head . name2String

nameFromTm (V x) = x
nameFromTm (C x) = x
nameFromTm t     = error $ show t ++ " is neither variable nor constant"

unfoldApp = reverse . unstackApp

unstackApp (App t1 t2) = t2 : unstackApp t1
unstackApp t           = [t]
