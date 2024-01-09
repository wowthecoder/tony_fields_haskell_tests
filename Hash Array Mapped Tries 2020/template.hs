module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes n 
  | n < 16 = bitTable !! n 
  | otherwise = (bitTable !! (n .&. (bit 4 - 1))) + countOnes (shiftR n 4)

countOnesFrom :: Int -> Int -> Int
countOnesFrom idx n
  = popCount (n .&. (bit idx - 1))

getIndex :: Int -> Int -> Int -> Int
getIndex n idx bSize
  = shiftR n (idx * bSize) .&. (bit bSize - 1)

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace _ [] _
  = []
replace n (x:xs) y 
  | n == 0    = y:xs 
  | otherwise = x : replace (n-1) xs y

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt idx y xs
  = ys ++ [y] ++ ys'
  where 
    (ys, ys') = splitAt idx xs

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie f g (Leaf xs)
  = g xs
sumTrie f g (Node _ []) 
  = 0
sumTrie f g (Node bv (sn:sns))
  = sumTrie' sn + sumTrie f g (Node bv sns)
  where 
    sumTrie' (Term x) = f x 
    sumTrie' (SubTrie t) = sumTrie f g t


--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)

member :: Int -> Hash -> Trie -> Int -> Bool
member v h trie bSize 
  = worker trie 0 
  where 
    worker (Leaf xs) _ 
      = v `elem` xs
    worker t@(Node bv sns) idx 
      | testBit bv i = case sns !! n of 
          Term x     -> v == x 
          SubTrie t' -> worker t' (idx + 1)
      | otherwise    = False
      where 
        i = getIndex h idx bSize
        n = countOnesFrom i bv

--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert hf maxDepth bSize v trie 
  = worker v trie 0 
  where
    worker v (Leaf xs) _ 
      | v `elem` xs = Leaf xs 
      | otherwise   = Leaf $ sort (v:xs)

    worker v (Node bv sns) lvl 
      | lvl == (maxDepth - 1) 
        = Leaf [v]
      | not (testBit bv i)         
        = Node (setBit bv i) (insertAt n (Term v) sns)
      | SubTrie t' <- sn      
        = Node bv (replace n sns (SubTrie (worker v t' (lvl + 1))))
      | Term v' <- sn         
        = if v == v' 
          then Node bv sns
          else let newT = worker v' (Node 0 []) (lvl + 1)
                   newSn = SubTrie (worker v newT (lvl + 1))
                in Node bv (replace n sns newSn)
      where 
        i = getIndex (hf v) lvl bSize
        n = countOnesFrom i bv
        sn = sns !! n

buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hf md bs xs 
  = foldl' (flip $ insert hf md bs) empty xs
