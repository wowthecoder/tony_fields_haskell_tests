{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
module SC where

import Data.List
import Data.Maybe
import Data.Bifunctor

import Types
import Examples

---------------------------------------------------------

prims :: [Id]
prims
  = ["+", "-", "*", "<=", "ite"]

lookUp :: Id -> [(Id, a)] -> a
lookUp v env
  = fromMaybe (error ("lookUp failed with search key " ++ v))
              (lookup v env)

---------------------------------------------------------
-- Part I

isFun :: Exp -> Bool
isFun (Fun _ _) = True 
isFun _ = False 

splitDefs :: [Binding] -> ([Binding], [Binding])
splitDefs [] = ([], [])
splitDefs (def:defs)
  | isFun (snd def) = (def : fst next, snd next)
  | otherwise       = (fst next, def : snd next)
  where 
    next = splitDefs defs

topLevelFunctions :: Exp -> Int
topLevelFunctions (Let bs e) = length $ filter (isFun . snd) bs
topLevelFunctions _ = 0

---------------------------------------------------------
-- Part II

unionAll :: Eq a => [[a]] -> [a]
unionAll = foldr union [] 

freeVars :: Exp -> [Id]
freeVars (Const _) = []
freeVars (Var id) 
  | id `elem` prims = []
  | otherwise       = [id]
freeVars (Fun ids e) = freeVars e \\ ids
freeVars (App e1 es) = unionAll $ map freeVars (e1:es)
freeVars (Let bs e) = (unionAll $ freeVars e : map freeVars (map snd bs)) \\ map fst bs

---------------------------------------------------------
-- Part III

-- Given...
lambdaLift :: Exp -> Exp
lambdaLift e
  = lift (modifyFunctions (buildFVMap e) e)

buildFVMap :: Exp -> [(Id, [Id])]
buildFVMap (Let bs e)   = buildFVMap e
                  ++ unionAll (map (buildFVMap . snd) bs)
                  ++ map (second (\\ map fst fDefs)) (iter fFreeVars)
  where
    (fDefs, _) = splitDefs bs
    fDefCount  = length fDefs
    fFreeVars  = second freeVars <$> fDefs
    -- Before removing the function references from the freeVars output, 
    -- we use the function reference to union the free variables
    -- use iterate because function might have nested references
    iter ffvs  = second sort <$> iterate (map (second expand)) ffvs !! fDefCount
    expand fvs = unionAll (fvs : map (fromMaybe [] . (`lookup` fFreeVars)) fvs)
buildFVMap (App e1 es) = unionAll $ map buildFVMap (e1 : es)
buildFVMap (Fun _ e)    = buildFVMap e
buildFVMap _ = []

modifyFunctions :: [(Id, [Id])] -> Exp -> Exp
-- Pre: The mapping table contains a binding for every function
-- named in the expression.
modifyFunctions bt (Let bs e) = Let (map modify bs) (modifyFunctions bt e)
  where 
    modify (name, Fun ids e) = let fvs = lookUp name bt
                                in ('$' : name, Fun (fvs `union` ids) (modifyFunctions bt e)) 
    modify (id, e) = (id, modifyFunctions bt e)
modifyFunctions bt (Var f) 
  | f `elem` (map fst bt) = case fvs of 
    [] -> Var ('$' : f)
    _  -> App (Var ('$' : f)) (map Var fvs)
  | otherwise             = Var f
  where 
    fvs = lookUp f bt
modifyFunctions bt (App e1 es) = App (modifyFunctions bt e1) (map (modifyFunctions bt) es)
modifyFunctions _ e = e

-- The default definition here is id.
-- If you implement the above two functions but not this one
-- then lambdaLift above will remove all the free variables
-- in functions; it just won't do any lifting.
lift :: Exp -> Exp
-- lift (Let [] e) = e
lift orig@(Let _ _) = Let scbs e
  where 
    (e, scbs) = lift' orig

-- You may wish to use this...
lift' :: Exp -> (Exp, [Supercombinator])
lift' (Let bs e1) 
  | null others = (e2, fs1 ++ fs2 ++ concatMap snd tups)
  | otherwise   = (Let others e2, fs1 ++ fs2 ++ concatMap snd tups)
  where
    (e2, fs2) = lift' e1
    tups = map (lift' . snd) bs
    newBs = zip (map fst bs) (map fst tups)
    (fs1, others) = splitDefs newBs
lift' (Fun ids e1) = (Fun ids e2, fs2)
  where 
    (e2, fs2) = lift' e1
lift' (App e1 es) = (App e2 (map fst tups), fs2 ++ concatMap snd tups) 
  where 
    (e2, fs2) = lift' e1
    tups = map lift' es 
lift' e = (e, [])

