import Data.List
import Data.Maybe

type Id = String

type State = Int

type Transition = ((State, State), Id)

type LTS = [Transition]

type Alphabet = [Id]

data Process = STOP | Ref Id | Prefix Id Process | Choice [Process] 
             deriving (Eq, Show)

type ProcessDef = (Id, Process)

type StateMap = [((State, State), State)]

------------------------------------------------------
-- PART I

lookUp :: Eq a => a -> [(a, b)] -> b
--Pre: The item is in the table
lookUp k ps = fromJust $ lookup k ps

states :: LTS -> [State]
states lts = nub $ concat [ [st1,st2] | (st1, st2) <- map fst lts]

transitions :: State -> LTS -> [Transition]
transitions st lts = filter (\((from, to), id) -> from == st) lts

alphabet :: LTS -> Alphabet
alphabet lts = map (\((_, _), id) -> id) lts

------------------------------------------------------
-- PART II

actions :: Process -> [Id]
actions (Ref _) = []
actions STOP = []
actions (Prefix id pro) = id : actions pro 
actions (Choice pros) = concatMap actions pros

accepts :: [Id] -> [ProcessDef] -> Bool
--Pre: The first item in the list of process definitions is
--     that of the start process.
accepts trace pDefs = accept' (snd $ head pDefs) trace pDefs
  where 
    -- helper function to recurse over the current process
    accept' :: Process -> [Id] -> [ProcessDef] -> Bool
    accept' _ [] _     = True 
    accept' STOP _ _   = False 
    -- if next process is not in the pDef list, STOP case will handle it
    accept' (Ref pName) ts pds 
      = let nextProc = fromMaybe STOP (lookup pName pds) 
         in accept' nextProc ts pds
    accept' (Prefix id pro) (t:ts) pds 
      = id == t && accept' pro ts pds 
    accept' (Choice pros) ts pds 
      = any (\x -> accept' x ts pds) pros
      

------------------------------------------------------
-- PART III

composeTransitions :: Transition -> Transition 
                  -> Alphabet -> Alphabet 
                  -> StateMap 
                  -> [Transition]
--Pre: The first alphabet is that of the LTS from which the first transition is
--     drawn; likewise the second.
--Pre: All (four) pairs of source and target states drawn from the two transitions
--     are contained in the given StateMap.
composeTransitions ((s, t), a) ((s', t'), a') alpha1 alpha2 m
  | a == a'                             = [((newS1, newS2), a)]
  | a `elem` alpha2 && a' `elem` alpha1 = []
  | a' `elem` alpha1                    = [t3]
  | a `elem` alpha2                     = [t4]
  | otherwise                           = [t3, t4]
  where 
    newS1 = lookUp (s, s') m
    newS2 = lookUp (t, t') m
    newS3 = lookUp (t, s') m
    newS4 = lookUp (s, t') m
    t3 = ((newS1, newS3), a)
    t4 = ((newS1, newS4), a')

pruneTransitions :: [Transition] -> LTS
pruneTransitions ts = nub (visit 0 []) 
  where 
    visit :: State -> [State] -> [Transition]
    visit curr visited 
      | curr `elem` visited = []
      | otherwise           = concatMap visitNext next
      where 
        next = transitions curr ts
        visitNext t@((from, to), _) = t : visit to (from : visited)
        

------------------------------------------------------
-- PART IV

compose :: LTS -> LTS -> LTS
compose lts1 lts2 = pruneTransitions res
  where 
    sts1 = states lts1 
    sts2 = states lts2
    m = length sts1 
    n = length sts2
    stateMap = zip [(s1, s2) | s1 <- sts1, s2 <- sts2] [0..(m*n-1)]
    alpha1 = alphabet lts1 
    alpha2 = alphabet lts2 
    -- transition pairs
    tps = map (getTrans . fst) stateMap 
    res = concat [compose' p p' | (p, p') <- tps]
    -- helper functions
    getTrans :: (State, State) -> ((State, [Transition]), (State, [Transition]))
    getTrans (s, s') = ((s, transitions s lts1), (s', transitions s' lts2)) 
    compose' :: (State, [Transition]) -> (State, [Transition]) -> [Transition]
    compose' (s, xs) (s', ys)
      | null xs && null ys 
        = composeTransitions d1 d2 ("$'" : alpha1) ("$" : alpha2) stateMap
      | null xs            
        = concat [composeTransitions d1 t2 alpha1 ("$" : alpha2) stateMap
                  | t2 <- ys]
      | null ys            
        = concat [composeTransitions t1 d2 ("$'" : alpha1) alpha2 stateMap 
                  | t1 <- xs]
      | otherwise          
        = concat [composeTransitions t1 t2 alpha1 alpha2 stateMap
                  | t1 <- xs, t2 <- ys]
      where 
        d1 = ((s, s'), "$")
        d2 = ((s', s), "$'")

------------------------------------------------------
-- PART V

buildLTS :: [ProcessDef] -> LTS
-- Pre: All process references (Ref constructor) have a corresponding
--      definition in the list of ProcessDefs.
buildLTS 
  = undefined

------------------------------------------------------
-- Sample process definitions...

vendor, clock, play, maker, user, p, q, switch, off, on :: ProcessDef

vendor 
  = ("VENDOR", Choice [Prefix "red"  (Prefix "coffee" (Ref "VENDOR")),
                       Prefix "blue" (Prefix "tea" (Ref "VENDOR")),
                       Prefix "off" STOP])

clock 
  = ("CLOCK", Prefix "tick" (Prefix "tock" (Ref "CLOCK")))

play 
  = ("PLAY", Choice [Prefix "think" (Prefix "move" (Ref "PLAY")), 
                     Prefix "end" STOP])

maker 
  = ("MAKER", Prefix "make" (Prefix "ready" (Ref "MAKER")))

user  
  = ("USER",  Prefix "ready" (Prefix "use" (Ref "USER")))

p = ("P", Prefix "a" (Prefix "b" (Prefix "c" STOP)))

q = ("Q",  Prefix "d" (Prefix "c" (Prefix "b" (Ref "Q"))))

switch 
  = ("SWITCH", Ref "OFF")

off 
  = ("OFF", Choice [Prefix "on" (Ref "ON")])

on  
  = ("ON",  Choice [Prefix "off" (Ref "OFF")])

------------------------------------------------------
-- Sample LTSs...

vendorLTS, clockLTS, playLTS, clockPlayLTS, makerLTS, userLTS, makerUserLTS, 
  pLTS, qLTS, pqLTS, switchLTS :: LTS

vendorLTS 
  = [((0,1),"off"),((0,2),"blue"),((0,3),"red"),((2,0),"tea"),((3,0),"coffee")]

clockLTS 
  = [((0,1),"tick"),((1,0),"tock")]

playLTS 
  = [((0,1),"end"),((0,2),"think"),((2,0),"move")]

clockPlayLTS 
  = [((0,1),"end"),((1,4),"tick"),((4,1),"tock"),((0,3),"tick"),
     ((3,4),"end"),((3,0),"tock"),((3,5),"think"),((5,3),"move"),
     ((5,2),"tock"),((2,0),"move"),((2,5),"tick"),((0,2),"think")]

makerLTS 
  = [((0,1),"make"),((1,0),"ready")]

userLTS 
  = [((0,1),"ready"),((1,0),"use")]

makerUserLTS 
  = [((0,2),"make"),((2,1),"ready"),((1,0),"use"),((1,3),"make"),((3,2),"use")]

pLTS 
  = [((0,1),"a"),((1,2),"b"),((2,3),"c")]

qLTS 
  = [((0,1),"d"),((1,2),"c"),((2,0),"b")]

pqLTS 
  = [((0,1),"d"),((1,4),"a"),((0,3),"a"),((3,4),"d")]

switchLTS 
  = [((0,1),"on"),((1,0),"off")]

