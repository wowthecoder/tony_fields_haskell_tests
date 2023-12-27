import Data.Maybe
import Data.List
import GHC.Builtin.Names (dTyConKey)
import Data.Ord (comparing)

type AttName = String

type AttValue = String

type Attribute = (AttName, [AttValue])

type Header = [Attribute]

type Row = [AttValue]

type DataSet = (Header, [Row])

data DecisionTree = Null |
                    Leaf AttValue | 
                    Node AttName [(AttValue, DecisionTree)]
                  deriving (Eq, Show)

type Partition = [(AttValue, DataSet)]

type AttSelector = DataSet -> Attribute -> Attribute

xlogx :: Double -> Double
xlogx p
  | p <= 1e-100 = 0.0
  | otherwise   = p * log2 p 
  where
    log2 x = log x / log 2

lookUp :: (Eq a, Show a, Show b) => a -> [(a, b)] -> b
lookUp x table
  = fromMaybe (error ("lookUp error - no binding for " ++ show x ++ 
                      " in table: " ++ show table))
              (lookup x table)

--------------------------------------------------------------------
-- PART I
--------------------------------------------------------------------

allSame :: Eq a => [a] -> Bool
allSame [] = True
allSame xs = length (nub xs) == 1

remove :: Eq a => a -> [(a, b)] -> [(a, b)]
remove p = filter (\(x, y) -> x /= p) 

lookUpAtt :: AttName -> Header -> Row -> AttValue
--Pre: The attribute name is present in the given header.
lookUpAtt name h r = head $ intersect r (lookUp name h)

removeAtt :: AttName -> Header -> Row -> Row
removeAtt name h r = delete (lookUpAtt name h r) r

addToMapping :: Eq a => (a, b) -> [(a, [b])] -> [(a, [b])]
addToMapping pair@(x, y) ps 
  | key `elem` (map fst ps) = (k, y:vs) : (remove key ps)
  | otherwise               = (x, [y]) : ps
  where 
    key = fst pair
    (k, vs) = fromJust $ find (\(x, _) -> x == key) ps

buildFrequencyTable :: Attribute -> DataSet -> [(AttValue, Int)]
--Pre: Each row of the data set contains an instance of the attribute
buildFrequencyTable (name, atts) (h, rs) 
  = map (\x -> (x, length $ filter (==x) vals)) atts
  where 
    vals = map (lookUpAtt name h) rs

--------------------------------------------------------------------
-- PART II
--------------------------------------------------------------------

nodes :: DecisionTree -> Int
nodes Null = 0
nodes (Leaf _) = 1
nodes (Node _ ns) = 1 + sum (map (nodes . snd) ns)

evalTree :: DecisionTree -> Header -> Row -> AttValue
evalTree Null _ _       = ""
evalTree (Leaf val) _ _ = val
evalTree (Node name ns) h r = evalTree nextNode h (removeAtt name h r)
  where 
    nextVal = lookUpAtt name h r
    nextNode = lookUp nextVal ns

--------------------------------------------------------------------
-- PART III
--------------------------------------------------------------------

--
-- Given...
-- In this simple case, the attribute selected is the first input attribute 
-- in the header. Note that the classifier attribute may appear in any column,
-- so we must exclude it as a candidate.
--
nextAtt :: AttSelector
--Pre: The header contains at least one input attribute
nextAtt (header, _) (classifierName, _)
  = head (filter ((/= classifierName) . fst) header)

partitionData :: DataSet -> Attribute -> Partition
partitionData (h, rs) (name, vals) = zip vals dts
  where 
    newH = remove name h
    newRs = map (\v -> filter (\r -> lookUpAtt name h r == v) rs) vals
    dts = [(newH, map (removeAtt name h) dt) | dt <- newRs]



buildTree :: DataSet -> Attribute -> AttSelector -> DecisionTree 
buildTree dt@(h, rs) clf@(name, vals) sel 
  | null rs 
    = Null 
  | allSame clfVals
    = Leaf (head clfVals)
  | otherwise 
    = Node nextname (map (\(v, d) -> (v, buildTree d clf sel)) parts)
  where 
    nextAtt = sel dt clf
    nextname = fst nextAtt
    parts = partitionData dt nextAtt
    clfVals = map (lookUpAtt name h) rs

    

--------------------------------------------------------------------
-- PART IV
--------------------------------------------------------------------

-- helper function
prob :: Int -> DataSet -> Double 
prob freq dt = (fromIntegral freq) / (fromIntegral $ length $ snd dt)

entropy :: DataSet -> Attribute -> Double
entropy (_, []) _ = 0.0
entropy dt att 
  = (sum . map (\(_, freq) ->  negate $ xlogx $ prob freq dt)) ftable
    where 
      ftable = buildFrequencyTable att dt

gain :: DataSet -> Attribute -> Attribute -> Double
gain dt att clf = ent - sum (zipWith (*) probs ents)
  where 
    ent = entropy dt clf
    ftable = buildFrequencyTable att dt 
    probs = map (\(_, freq) -> prob freq dt) ftable
    ents = map (\(_, d) -> entropy d clf) (partitionData dt att)

bestGainAtt :: AttSelector
bestGainAtt dt@(h, _) clf@(clfName, _) = fst $ maximumBy (comparing snd) gainMap
  where 
    noClf = remove clfName h
    gainMap = map (\att -> (att, gain dt att clf)) noClf

--------------------------------------------------------------------

outlook :: Attribute
outlook 
  = ("outlook", ["sunny", "overcast", "rainy"])

temp :: Attribute 
temp 
  = ("temp", ["hot", "mild", "cool"])

humidity :: Attribute 
humidity 
  = ("humidity", ["high", "normal"])

wind :: Attribute 
wind 
  = ("wind", ["windy", "calm"])

result :: Attribute 
result
  = ("result", ["good", "bad"])

fishingData :: DataSet
fishingData
  = (header, table)

header :: Header
table  :: [Row]
header 
  =  [outlook,    temp,   humidity, wind,    result] 
table 
  = [["sunny",    "hot",  "high",   "calm",  "bad" ],
     ["sunny",    "hot",  "high",   "windy", "bad" ],
     ["overcast", "hot",  "high",   "calm",  "good"],
     ["rainy",    "mild", "high",   "calm",  "good"],
     ["rainy",    "cool", "normal", "calm",  "good"],
     ["rainy",    "cool", "normal", "windy", "bad" ],
     ["overcast", "cool", "normal", "windy", "good"],
     ["sunny",    "mild", "high",   "calm",  "bad" ],
     ["sunny",    "cool", "normal", "calm",  "good"],
     ["rainy",    "mild", "normal", "calm",  "good"],
     ["sunny",    "mild", "normal", "windy", "good"],
     ["overcast", "mild", "high",   "windy", "good"],
     ["overcast", "hot",  "normal", "calm",  "good"],
     ["rainy",    "mild", "high",   "windy", "bad" ]]

--
-- This is the same as the above table, but with the result in the second 
-- column...
--
fishingData' :: DataSet
fishingData'
  = (header', table')

header' :: Header
table'  :: [Row]
header' 
  =  [outlook,    result, temp,   humidity, wind] 
table' 
  = [["sunny",    "bad",  "hot",  "high",   "calm"],
     ["sunny",    "bad",  "hot",  "high",   "windy"],
     ["overcast", "good", "hot",  "high",   "calm"],
     ["rainy",    "good", "mild", "high",   "calm"],
     ["rainy",    "good", "cool", "normal", "calm"],
     ["rainy",    "bad",  "cool", "normal", "windy"],
     ["overcast", "good", "cool", "normal", "windy"],
     ["sunny",    "bad",  "mild", "high",   "calm"],
     ["sunny",    "good", "cool", "normal", "calm"],
     ["rainy",    "good", "mild", "normal", "calm"],
     ["sunny",    "good", "mild", "normal", "windy"],
     ["overcast", "good", "mild", "high",   "windy"],
     ["overcast", "good", "hot",  "normal", "calm"],
     ["rainy",    "bad",  "mild", "high",   "windy"]]

fig1 :: DecisionTree
fig1
  = Node "outlook" 
         [("sunny", Node "temp" 
                         [("hot", Leaf "bad"),
                          ("mild",Node "humidity" 
                                       [("high",   Leaf "bad"),
                                        ("normal", Leaf "good")]),
                          ("cool", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "temp" 
                         [("hot", Null),
                          ("mild", Node "humidity" 
                                        [("high",Node "wind" 
                                                      [("windy",  Leaf "bad"),
                                                       ("calm", Leaf "good")]),
                                         ("normal", Leaf "good")]),
                          ("cool", Node "humidity" 
                                        [("high", Null),
                                         ("normal", Node "wind" 
                                                         [("windy",  Leaf "bad"),
                                                          ("calm", Leaf "good")])])])]

fig2 :: DecisionTree
fig2
  = Node "outlook" 
         [("sunny", Node "humidity" 
                         [("high", Leaf "bad"),
                          ("normal", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "wind" 
                         [("windy", Leaf "bad"),
                          ("calm", Leaf "good")])]


outlookPartition :: Partition
outlookPartition
  = [("sunny",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","bad"],["hot","high","windy","bad"],
                   ["mild","high","calm","bad"],["cool","normal","calm","good"],
                   ["mild","normal","windy","good"]])),
     ("overcast",([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","good"],["cool","normal","windy","good"],
                   ["mild","high","windy","good"],["hot","normal","calm","good"]])),
     ("rainy",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["mild","high","calm","good"],["cool","normal","calm","good"],
                   ["cool","normal","windy","bad"],["mild","normal","calm","good"],
                   ["mild","high","windy","bad"]]))]
