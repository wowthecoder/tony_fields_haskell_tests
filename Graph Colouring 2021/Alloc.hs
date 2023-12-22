module Alloc where

import Data.Maybe
import Data.List
import Data.Tuple (swap)

import Types
import Examples

------------------------------------------------------
--
-- Part I
--
count :: Eq a => a -> [a] -> Int
count e xs = length $ filter (==e) xs 

degrees :: Eq a => Graph a -> [(a, Int)]
degrees (as, edges) = map (\a -> (a, count a xs + count a ys)) as
  where 
    (xs, ys) = unzip edges

neighbours :: Eq a => a -> Graph a -> [a]
neighbours _ (_, []) = []
neighbours node (as, (n1, n2):edges) 
  | n1 == node = n2 : neighbours node (as, edges)
  | n2 == node = n1 : neighbours node (as, edges)
  | otherwise  = neighbours node (as, edges)

removeNode :: Eq a => a -> Graph a -> Graph a
removeNode node (as, edges) = (filter (/= node) as, filter (\(x, y) -> x /= node && y /= node) edges)

------------------------------------------------------
--
-- Part II
--
colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph _ ([], _) = []
colourGraph max graph = (n, c) : others
  where 
    n      = (snd . minimum . map swap . degrees) graph
    c      = fromMaybe 0 (find (`notElem` nbcs) [1..max])
    others = colourGraph max (removeNode n graph)
    nbcs   = map (\x -> lookUp x others) (neighbours n graph)
    

------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap [] = [("return", "return")]
buildIdMap ((id, c):colours) 
  | c == 0    = (id, id) : buildIdMap colours
  | otherwise = (id, "R" ++ show c) : buildIdMap colours

buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments ids idm = map (\i -> Assign (lookUp i idm) (Var i)) ids

renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp (Const p) _ = Const p
renameExp (Var id) idm = Var (lookUp id idm)
renameExp (Apply op e1 e2) idm = Apply op (renameExp e1 idm) (renameExp e2 idm)

renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock [] _ = []
renameBlock b idm = filter notEqual (renameStatements b)
  where 
    notEqual (Assign x (Var y)) = x /= y
    notEqual _ = True
    renameStatements (st:b) = case st of 
      Assign id e -> Assign (lookUp id idm) (renameExp e idm) : next
      If e b1 b2  -> If (renameExp e idm) (renameBlock b1 idm) (renameBlock b2 idm) : next
      While e b1  -> While (renameExp e idm) (renameBlock b1 idm) : next
      where 
        next = renameBlock b idm

renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--
buildIG :: [[Id]] -> IG
buildIG lvs = (as, edges)
  where 
    as = nub $ concat lvs
    edges = nub $ concatMap (\lst -> [(x,y) | (x:ys) <- tails lst, y <- ys]) lvs

-----------------------------------------------------
--
-- Part V
--
liveVars :: CFG -> [[Id]]
liveVars 
  = undefined

buildCFG :: Function -> CFG
buildCFG 
  = undefined
