{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE MultiWayIf                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module SmplUnif where
import           Control.Applicative
import           Control.Monad
import           Data.Char               (isUpper)
import           Data.Foldable           (foldlM)
import           Data.List               hiding (insert, map, null)
import           Data.Map.Strict         hiding (foldl, foldr, insert, map,
                                          mapMaybe, null)
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           SmplSyntax
import           Unbound.LocallyNameless

-- import           Debug.Trace
trace = flip const

-- TODO Sig is basically an environment. should we abstract it as reader monad?

type Sig = Map Nm VarType
data VarType = Cnst | Flex deriving (Eq,Ord,Show,Read)

emptyMap = M.empty

expand :: Fresh m => Map Nm Tm -> Tm -> m Tm
expand s v@(V x) = case M.lookup x s of { Nothing -> pure v; Just u -> expand s u }
expand s (App t1 t2) = App <$> expand s t1 <*> expand s t2
expand s (Lam b) = do { (x,t) <- unbind b; lam x <$> expand s t }

expand' :: Fresh m => Map Nm Tm -> Tm -> m Tm
expand' s v@(V x) = case M.lookup x s of { Nothing -> pure v; Just u -> expand' s u }
expand' s (App t1 t2) = do { t1' <- expand' s t1; t2' <- expand' s t2; redapps t1' [t2'] }
expand' s (Lam b) = do { (x,t) <- unbind b; lam x <$> expand' s t }

infixr .+
(.+) :: Fresh m => (Nm,Tm) -> m (sig, [(Tm,Tm)],Map Nm Tm) -> m (sig, [(Tm,Tm)],Map Nm Tm)
(x,t) .+ mess = do (sig,es,s) <- mess
                   t' <- expand' s t
                   let s' = M.insert x t' (subst x t' <$> s)
                   let es' | M.member x s = (s!x,t'):es
                           | otherwise    = es
                   return (sig,es', s')

u :: Fresh m => (Sig, [(Tm, Tm)], Map Nm Tm) -> m (Map Nm Tm)
u (_, [], s) = return s
u ess        = u =<< ustep' ess

ustep' ess@(_, [], _) = return ess
ustep' (sig, (t1,t2):es, s) = do t1' <- devar s t1
                                 t2' <- devar s t2
                                 ustep (sig, (t1',t2'):es, s)

ustep :: Fresh m => (Sig, [(Tm,Tm)], Map Nm Tm) -> m (Sig, [(Tm,Tm)], Map Nm Tm)
ustep p@(_, [], _) = return p
-- on the fly eta-expansion
ustep (sig, (Lam b1, Lam b2):es, s) = do Just(x,t1,_,t2) <- unbind2 b1 b2
                                         pure (sig, (t1,t2):es, s)
ustep (sig, (t1, Lam b):es, s)      = do (x,t) <- unbind b
                                         pure (sig, (App t1 (V x), t):es, s)
ustep (sig, (Lam b, t2):es, s)      = do (x,t) <- unbind b
                                         pure (sig, (t, App t2 (V x)):es, s)
-- the real unification work
ustep (sig, (t1, t2):es, s) =
  case (tF, tG) of
    (V xF, V xG)
    -- flexflex
      | flex sig xF && flex sig xG -> if -- multy way if
        -- flexflex1
        | xF == xG -> if len1/=len2 then cantUnify "their arguments differ"
                      else do h <- fresh (s2n "H")
                              let sig' = M.insert h Flex sig
                              (xF, hnf bs1 (V h) xs) .+ pure(sig', es, s)
        -- flexflex2
        | subset bs1 bs2 -> (xG, hnf bs2 tF ts1) .+ pure(sig, es, s)
        | subset bs2 bs1 -> (xF, hnf bs1 tG ts2) .+ pure(sig, es, s)
        | otherwise ->
          do h <- fresh (s2n "H")
             let sig' = M.insert h Flex sig
             (xF, hnf bs1 (V h) zs) .+ (xG, hnf bs2 (V h) zs) .+ pure(sig',es,s)
    -- flexrigid
      | flex sig xF -> trace ("flexrigid "++show((t1,t2):es)) $
                do xF't2 <- occ s xF t2
                   when xF't2 . cantUnify $ show xF++" occurs in "++show t2
                   (sig',es',s') <- (xF, lamMany bs1 t2) .+ pure(sig, es, s)
                   proj' bs1 (sig',es',s') t2
    -- rigidflex
      | flex sig xG -> trace ("rigidflex "++show((t1,t2):es)) $
                do xG't1 <- occ s xG t1
                   when xG't1 . cantUnify $ show xG++" occurs in "++show t1
                   (sig',es',s') <- (xG, lamMany bs2 t1) .+ pure(sig,es, s)
                   proj' bs2 (sig',es',s') t1
    -- rigidrigid
      | xF==xG && len1==len2 -> pure (sig, zip ts1 ts2 ++ es, s)
      | xF/=xG               -> cantUnify $ show xF++" /= "++show xG
      | otherwise            -> cantUnify "their arguments differ"
  where
     tF : ts1 = unfoldApp t1; bs1 = unB<$>ts1; len1 = length ts1
     tG : ts2 = unfoldApp t2; bs2 = unB<$>ts2; len2 = length ts2
     xs = [x1 | (x1,x2)<-zip ts1 ts2, x1==x2]
     zs = [x1 | x1 <- ts1, x2 <- ts2, x1==x2]
     cantUnify whymsg = fail $ "cannot unify " ++ show (t1,t2)
                            ++ " because " ++ whymsg

unB (V x) = x -- x must not be in sig but not really checking here yet

occ s x t = occurs x <$> expand s t

subset xs ys = all (`elem` ys) xs

flex sig x = Just Flex == M.lookup x sig
cnst sig x = Just Cnst == M.lookup x sig

proj :: Fresh m => [Nm] -> (Sig,[(Tm,Tm)],Map Nm Tm) ->
                   Tm -> m (Sig,[(Tm,Tm)],Map Nm Tm)
proj vs ess@(sig,es,s) t =
  trace ("\nproj ("++show vs++") ("++show ess++") ("++show t++")\n***\n") $
  case unfoldApp t of
    [Lam b]         -> do { (x,tb) <- unbind b; proj' (x:vs) ess tb }
    V x : ts
      | cnst sig x -> foldlM (proj' vs) ess ts   -- global const
      | flex sig x -> let ys = unB <$> ts        -- logic var
                          zs = [V y | y<-ys, y `elem` vs]
                       in if subset ys vs then pure ess
                          else do h <- fresh (s2n "H")
                                  let sig' = M.insert h Flex sig
                                  (x, hnf ys (V h) zs) .+ pure(sig',es,s)
      | x `elem` vs -> foldlM (proj' vs) ess ts  -- bound var
      | otherwise   -> fail $ "unbound rigid variable "++ show x
    _ -> error $ "non-reachable pattern: t = "++show t
                         ++" ; unfoldApp t = "++show(unfoldApp t)

-- helper function wrapping proj with devar
proj' vs ess@(sig,es,s) t = proj vs ess =<< devar s t

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

unfoldApp = reverse . unstackApp

unstackApp (App t1 t2) = t2 : unstackApp t1
unstackApp t           = [t]
