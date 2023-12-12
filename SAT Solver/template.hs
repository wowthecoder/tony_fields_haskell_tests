{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
module SOL where

import Data.List
import Data.Maybe

import Types
import TestData
import System.Posix.Internals (lstat)
import Data.Ord (comparing)

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp x lst = fromJust $ lookup x lst

-- 3 marks
vars :: Formula -> [Id]
vars fml = sort $ nub (vars' fml)
    where
        vars' fml = case fml of
            Var x       -> [x]
            Not fm1     -> vars fm1
            And fm1 fm2 -> vars fm1 ++ vars fm2
            Or fm1 fm2  -> vars fm1 ++ vars fm2

-- 1 mark
idMap :: Formula -> IdMap
idMap fml = let vs = vars fml in zip vs [1..(length vs)]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF fml = case fml of
    Not (Not fm1)     -> toNNF fm1
    Not (Or fm1 fm2)  -> And (toNNF (Not fm1)) (toNNF (Not fm2))
    Not (And fm1 fm2) -> Or (toNNF (Not fm1)) (toNNF (Not fm2))
    And fm1 fm2 -> And (toNNF fm1) (toNNF fm2)
    Or fm1 fm2  -> Or (toNNF fm1) (toNNF fm2)
    _ -> fml -- for Var x and Not (Val x)

-- 3 marks
toCNF :: Formula -> CNF
toCNF fml = cnf' (toNNF fml)
    where
        cnf' (Or fm1 fm2)  = distribute (cnf' fm1) (cnf' fm2)
        cnf' (And fm1 fm2) = And (cnf' fm1) (cnf' fm2)
        cnf' fm1 = fm1

-- 4 marks
flatten :: CNF -> CNFRep
flatten fml = flat' (toCNF fml)
    where
        pairs = idMap fml
        flat' frm = case frm of
            Var x -> [[lookUp x pairs]]
            Not (Var x) -> [[negate $ lookUp x pairs]]
            And fm1 fm2 -> flat' fm1 ++ flat' fm2
            Or fm1 fm2  -> [concat (flat' fm1 ++ flat' fm2)]

--------------------------------------------------------------------------
-- Part III

-- 5 marks 
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits [] = ([], [])
-- propUnits [[]] = ([[]], [])
propUnits rep 
  | uc == 0 = (rep, [])
  | otherwise = (rep', uc:ucs)
  where
    clause = map (delete (negate uc)) (filter (notElem uc) rep)
    uc = head $ fromMaybe [0] firstUC
    firstUC = find isSingleton rep
    isSingleton [_] = True
    isSingleton _ = False
    (rep', ucs) = propUnits clause

-- 4 marks
dp :: CNFRep -> [[Int]]
dp rep
  | any null cl = []
  | null cl = [ucs]
  | otherwise    = map (ucs++) (dp ([head $ head cl]:cl) ++ dp ([negate $ head $ head cl]:cl))
  where 
    (cl, ucs) = propUnits rep

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat fml = helper (dp (flatten fml))
  where 
    len = length (vars fml)
    idm = idMap' fml
    helper [] = []
    helper (x:xs) 
      | length x /= len = let missing = sum[1..(len)] - sum (map abs x)
                              a = missing:x
                              b = (negate missing):x
                           in helper (a:b:xs)
      | otherwise       = sortBy (comparing fst) (map (\y -> (lookUp (abs y) idm, y > 0)) x) : helper xs

-- Idmap reversed
idMap' :: Formula -> [(Int, Id)]
idMap' fml = let vs = vars fml in zip [1..(length vs)] vs


