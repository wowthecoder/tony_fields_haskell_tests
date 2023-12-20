module Solver where

import Data.List
import Data.Char

import Types
import WordData
import Clues
import Examples
import Data.Maybe (fromMaybe)
import GHC.Plugins (addBootSuffix)

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
  = def `elem` synonyms syn
matches target (Anagram _ ang) 
  = sort target == sort ang
matches target (Reversal _ subt) 
  = matches (reverse target) subt
matches target (Insertion _ left right)
  = or [(matches mid left) && (matches sides right) | (mid, sides) <- uninsert target]
matches target (Charade _ left right) 
  = or [(matches s1 left) && (matches s2 right) | (s1, s2) <- split2 target]
matches target (HiddenWord _ hw)
  | len == 1  = target `isInfixOf` hw 
  | len == 2  = target `isInfixOf` combined && not (target `isInfixOf` (head ws)) && not (target `isInfixOf` (last ws))
  | otherwise = target `isInfixOf` combined && (concat . tail . init) ws `isInfixOf` target
  where 
    ws = words hw
    len = length ws
    combined = concat ws

evaluate :: Parse -> Int -> [String]
-- evaluate (def, _, pTree) len = [ans | ans <- words, matches ans pTree]
--   where 
--     words = filter (\x -> length x == len) (synonyms $ unwords def)
evaluate (d, _, t) l = filter (\s -> s `matches` t && length s == l) (synonyms (unwords d))

------------------------------------------------------
-- Part III

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat [parseSynonym ws,
            parseAnagram ws,
            parseReversal ws,
            parseInsertion ws,
            parseCharade ws,
            parseHiddenWord ws]
    
parseSynonym :: [String] -> [ParseTree]
parseSynonym ws
  | not (null $ synonyms w) = [Synonym w]
  | otherwise               = []
  where 
    w = unwords ws

oneArg :: [String] -> [String] -> ParseTree -> [ParseTree]
oneArg inds arg typ
  | Just (ind, ws) <- pair = case typ of 
    Anagram {}    -> [Anagram ind (unwords ws)] 
    Reversal {}   -> map (Reversal ind) (parseWordplay ws)
    HiddenWord {} -> [HiddenWord ind (unwords ws)]
    _             -> []
  | otherwise = []
    where 
      pair = find (\x -> (unwords $ fst x) `elem` inds) (split2M arg)

twoArgs :: [String] -> [String] -> ParseTree -> [ParseTree]
twoArgs inds arg typ = case typ of 
  Insertion ["Insert"] _ _ -> concatMap (\(a, ind, a') -> 
    [Insertion ind t1 t2 | t1 <- parseWordplay a, t2 <- parseWordplay a']) ins
  Insertion ["Envelope"] _ _ -> concatMap (\(a, ind, a') -> 
    [Insertion ind t2 t1 | t1 <- parseWordplay a, t2 <- parseWordplay a']) ins
  Charade ["Before"] _ _ -> concatMap (\(a, ind, a') -> 
    [Charade ind t1 t2 | t1 <- parseWordplay a, t2 <- parseWordplay a']) chd
  Charade ["After"] _ _ -> concatMap (\(a, ind, a') -> 
    [Charade ind t2 t1 | t1 <- parseWordplay a, t2 <- parseWordplay a']) ins
  _ -> []
  where 
    ins = filter (\(_, y, _) -> not (null y) && (unwords y) `elem` inds) (split3 arg)
    chd = filter (\(_, y, _) -> null y || (unwords y) `elem` inds) (split3 arg)

parseAnagram :: [String] -> [ParseTree]
parseAnagram ws = oneArg anagramIndicators ws (Anagram [] "")

parseReversal :: [String] -> [ParseTree]
parseReversal ws = oneArg reversalIndicators ws (Reversal [] (Synonym ""))

parseInsertion :: [String] -> [ParseTree]
parseInsertion ws = twoArgs insertionIndicators ws (Insertion ["Insert"] (Synonym "") (Synonym ""))
  ++ twoArgs envelopeIndicators ws (Insertion ["Envelope"] (Synonym "") (Synonym ""))

parseCharade :: [String] -> [ParseTree]
parseCharade ws = twoArgs beforeIndicators ws (Charade ["Before"] (Synonym "") (Synonym ""))
  ++ twoArgs afterIndicators ws (Charade ["After"] (Synonym "") (Synonym ""))

parseHiddenWord :: [String] -> [ParseTree]
parseHiddenWord ws = oneArg hiddenWordIndicators ws (HiddenWord [] "")

-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText ws = concatMap (\(def, link, wp) -> [(def, link, pTree) | pTree <- parseWordplay wp]) filtered 
  where 
    filtered = filter (\(x, y, _) -> not (null (synonyms (unwords x))) && (unwords y) `elem` linkWords) (split3M ws)

solve :: Clue -> [Solution]
solve clue@(s, n) = [(clue, p, ans) | p <- ps, ans <- nub $ evaluate p n]
  where 
    ps = parseClue clue 


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


