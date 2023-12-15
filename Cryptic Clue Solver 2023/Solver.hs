module Solver where

import Data.List
import Data.Char

import Types
import WordData
import Clues
import Examples

------------------------------------------------------
-- Part I

punctuation :: String
punctuation 
  = "';.,-!?"

cleanUp :: String -> String
cleanUp cs = [toLower c | c <- cs, c `notElem` punctuation]

split2 :: [a] -> [([a], [a])]
split2 xs = [splitAt i xs | i <- [1..(length xs - 1)]]

split3 :: [a] -> [([a], [a], [a])]
split3 xs = [(xs1, xs2, xs3) | (xs0, xs3) <- split2 xs, (xs1, xs2) <- [splitAt i xs0 | i <- [1..(length xs0)]]]
  -- Also works: = concat [[(xs1, xs2, xs3) | (xs1, xs2) <- [splitAt i xs0 | i <- [1..(length xs0)]]] | (xs0, xs3) <- split2 xs]

uninsert :: [a] -> [([a], [a])]
uninsert xs = [(xs2, xs1 ++ xs3) | (xs1, xs2, xs3) <- split3 xs, not (null xs2)]

-- {- Uncomment these functions when you have defined the above.
split2M :: [a] -> [([a], [a])]
split2M xs
  = sxs ++ [(y, x) | (x, y) <- sxs] 
  where
    sxs = split2 xs

split3M :: [a] -> [([a], [a], [a])]
split3M xs
  = sxs ++ [(z, y, x) | (x, y, z) <- sxs]
  where
    sxs = split3 xs
-- -}

------------------------------------------------------
-- Part II

matches :: String -> ParseTree -> Bool
matches def (Synonym syn) 
  = let syns = synonyms syn
     in not (null syns) && def `elem` syns
matches target (Anagram _ ang) 
  = sort target == sort ang
matches target (Reversal _ subt) 
  = matches (reverse target) subt
matches target (Insertion _ left right)
 = or [(matches mid left) && (matches sides right) | (mid, sides) <- uninsert target]
matches target (Charade _ left right) 
  = or [(matches s1 left) && (matches s2 right) | (s1, s2) <- split2 target]

evaluate :: Parse -> Int -> [String]
evaluate (def, _, pTree) len = [ans | ans <- words, matches ans pTree]
  where 
    words = filter (\x -> length x == len) (synonyms $ concat def)

------------------------------------------------------
-- Part III

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat [parseSynonym ws,
            parseAnagram ws,
            parseReversal ws,
            parseInsertion ws,
            parseCharade ws]
    
parseSynonym :: [String] -> [ParseTree]
parseSynonym ws
  | not (null $ synonyms w) = [Synonym w]
  | otherwise               = []
  where 
    w = concat ws

parseAnagram :: [String] -> [ParseTree]
parseAnagram
  = const []

parseReversal :: [String] -> [ParseTree]
parseReversal
  = const []

parseInsertion :: [String] -> [ParseTree]
parseInsertion
  = const []

parseCharade :: [String] -> [ParseTree]
parseCharade 
  = const []

-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText
  = undefined

solve :: Clue -> [Solution]
solve 
  = undefined


------------------------------------------------------
-- Some additional test functions

-- Returns the solution(s) to the first k clues.
-- The nub removes duplicate solutions arising from the
-- charade parsing rule.
solveAll :: Int -> [[String]]
solveAll k
  = map (nub . map getSol . solve . (clues !!)) [0..k-1]

getSol :: Solution -> String
getSol (_, _, sol) = sol

showAll
  = mapM_ (showSolutions . solve . (clues !!)) [0..23]


