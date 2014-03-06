-- Testing the theorem prover
module Main where

import Test.HUnit hiding (State)
import Test.QuickCheck
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (empty)
import qualified Data.Map as Map
--import Control.Monad.State
import Control.Monad
import TP
import System.Exit
import Parser (parseSequent)
import NDS
import DataTypes

-- Test stuff

-- |Tries to prove a linear sequent (i.e. identities must be of the form a => a),
-- returns True if proven, False otherwise
-- we use this as a sort of golden standard given that it's much cleaner than the version with curry-howard

-- prove :: Sequent -> Bool
-- prove s@(gamma,f) = any (==True) proofs where
--     proofs = left ++ right
--     right = [r s | r <- [implicationRight, monadRight]]
--     left = [r g (delete g gamma,f) | g <- gamma, r <- [identity,implicationLeft,monadLeft]]

-- identity :: Formula -> Sequent -> Bool
-- identity a ([],a') = a == a'
-- identity _ _ = False

-- implicationLeft :: Formula -> Sequent -> Bool
-- implicationLeft (a :->: b) (gamma,c) = any (==True) proofs where
--     proofs = do
--       (g,g') <- split gamma
--       return $ (prove (g,a)) && (prove (b : g',c))
-- implicationLeft _ _ = False

-- monadLeft :: Formula -> Sequent -> Bool
-- monadLeft (M a) (gamma,M b) = prove (a : gamma, M b)
-- monadLeft _ _ = False

-- implicationRight :: Sequent -> Bool
-- implicationRight (gamma,a :->: b) = prove (a : gamma,b)
-- implicationRight _ = False

-- monadRight :: Sequent -> Bool
-- monadRight (gamma,M a) = prove (gamma,a)
-- monadRight _ = False

a = Atom "a" (TAtomic "a")
b = Atom "b" (TAtomic "b")
c = Atom "c" (TAtomic "c")

(.->.) :: Formula -> Formula -> Formula
f .->. g = I f g $ TFunctional (getType f) (getType g)

infixr 7 .->.

(.*.) :: Formula -> Formula -> Formula
a .*. b = P a b $ TPair (getType a) (getType b)

mon :: Formula -> Formula
mon f = M f $ TMonadic $ getType f

atom :: String -> Formula
atom s = Atom s (TAtomic s)

var :: String -> String -> Formula
var x t = Var x (TAtomic t)

-- |Given a pool of atomic formulae and a maximum depth generates all possible formulae
generateFormulae :: [Formula] -> Int -> Set Formula
generateFormulae [] _ = Set.empty
generateFormulae l 0 = Set.fromList l
generateFormulae l n = Set.fromList new where
    new = monadic ++ functional ++ lower
    monadic = [mon f | f <- lower]
    functional = [f .->. g | f <- lower , g <- lower]
    lower = Set.toList $ generateFormulae l (n-1)

maxDepth :: Formula -> Int
maxDepth (Atom _ _) = 0
maxDepth (Var _ _) = 0
maxDepth (M f _) = 1 + (maxDepth f)
maxDepth (I f g _) = 1 + (max (maxDepth f) (maxDepth g))
maxDepth (P a b _) = 1 + (max (maxDepth a) (maxDepth b))


-- |This function is used for test, it reduces the information about proofs
-- to a boolean answer
compress :: [a] -> Bool
compress [] = False
compress _ = True

broofs s = do
  ds <- toDecorated s
  proofs ds

kompress ps = compress (evalState ps startState)

-- HUnit

tests = TestList [ testGenerateFormualae
                 , testMaxDepth
--                 , testProve
                 , testSplit
                 , testProofs
                 , testSub
                 , testCollectVars
                 , testAlphaEquivalent 
                 , testEtaReduce 
                 , testMonadReduce
                 , testEquivalentDecoratedSequent 
                 , testMixMap 
                 , testParsers ]

testGenerateFormualae = "generateFormulae" ~: TestList
   [ generateFormulae [] 0 ~?= Set.empty
   , generateFormulae [a] 0 ~?= Set.fromList [a]
   , generateFormulae [a,b] 0 ~?= Set.fromList [a,b]
   , generateFormulae [a] 1 ~?= Set.fromList [a, mon a, a .->. a]
   , generateFormulae [a,b] 1 ~?= Set.fromList [a,b,mon a,mon b, a .->. a, a .->. b, b .->. b, b .->. a]]

testMaxDepth = "maxDepth" ~: TestList
   [ maxDepth a ~?= 0
   , maxDepth (mon a) ~?= 1
   , maxDepth (a .->. (b .->. c)) ~?= 2
   , all (\x -> maxDepth x <= 3) (Set.toList $ generateFormulae [a] 3) ~?= True]

-- testProve = "prove" ~: TestList
--    [ prove ([a],a) ~?= True
--    , prove ([a],b) ~?= False
--    , prove ([a :->: b, a],b) ~?= True
--    , prove ([a :->: c, b],c) ~?= False
--    , prove ([a :->: b, b],b) ~?= False 
--    , prove ([a :->: b, a],b) ~?= True 
--    , prove ([a :->: b], (M a) :->: (M b)) ~?= True ]

testSplit = "split" ~: TestList
   [ split ([] :: Context) ~?= [([],[])]
   , Set.fromList (split [a]) ~?= Set.fromList ([([],[a]),([a],[])])
   , Set.fromList (split [a,b]) ~?= Set.fromList ([([],[a,b])
                                                  ,([a],[b])
                                                  ,([b],[a])
                                                  ,([a,b],[])])]

testProofs = "proofs" ~: TestList
   [ kompress (broofs ([a],a)) ~?= True
   , kompress (broofs ([a],b)) ~?= False
   , kompress (broofs ([a .->. b, a],b)) ~?= True
   , kompress (broofs ([a .->. c, b],c)) ~?= False
   , kompress (broofs ([a .->. b, b],b)) ~?= False 
   , kompress (broofs ([a .->. b, a],b)) ~?= True 
   , kompress (broofs ([a,b],a .*. b)) ~?= True
   , kompress (broofs ([a .->. b, a, c], b .*. c)) ~?= True
   , kompress (broofs ([a .->. b, a], a .*. b)) ~?= False
   , kompress (broofs ([a .->. b], (mon a) .->. (mon b))) ~?= True
   , kompress (broofs ([mon a .->. b], a .->. b)) ~?= True
   , kompress (broofs ([mon (a .->. b)], mon a .->. mon b)) ~?= True
-- theorems from the papers
   , kompress (broofs ([a, (mon b) .->. a .->. c, mon b], c)) ~?= True
   , kompress (broofs ([a, (mon b) .->. a .->. c, (b .->. c) .->. c], c)) ~?= True
   , kompress (broofs ([var "X" "x"],var "X" "x")) ~?= True
   , kompress (broofs ([a],var "X" "a")) ~?= True
   , kompress (broofs ([var "X" "b" .->. a,b],a)) ~?= True
   , kompress (broofs ([a .->. b .->. c, (a .->. (var "X" "c")) .->. (var "X" "c"), (b .->. (var "Y" "c")) .->. (var "Y" "c")],c)) ~?= True ]

testSub = "sub" ~: TestList                 
   [ sub (V 1) (V 2) (V 3) ~?= V 3
   , sub (V 1) (V 2) (V 2) ~?= V 1
   , sub (V 1) (V 2) (Lambda (V 3) (V 2)) ~?= (Lambda (V 3) (V 1))
   , sub (V 1) (V 2) (Lambda (V 2) (V 2)) ~?= (Lambda (V 2) (V 2))
   , sub (V 1) (V 2) (App (Lambda (V 2) (V 2)) (Lambda (V 3) (V 2))) ~?= (App (Lambda (V 2) (V 2)) (Lambda (V 3) (V 1)))]

testCollectVars = "collectVars" ~: TestList
   [ collectVars (Branch ImpL (Leaf Id ([DF {identifier = -3, term = V (-11), formula = atom "a"}],DF {identifier = -7, term = V (-11), formula = atom "a"})) ([DF {identifier = -1, term = V (-13), formula = atom "a" .->. atom "b"},DF {identifier = -3, term = V (-11), formula = atom "a"}],DF {identifier = -5, term = App (V (-13)) (V (-11)), formula = atom "b"}) (Leaf Id ([DF {identifier = -8, term = V (-12), formula = atom "b"}],DF {identifier = -5, term = V (-12), formula = atom "b"}))) ~?= Set.fromList [V (-11), V (-13), V (-12)]]

testAlphaEquivalent = "alphaEquivalent" ~: TestList
   [ alphaEquivalent (V 1) (V 2) m ~?= False
   , alphaEquivalent (V 1) (V 1) m ~?= True
   , alphaEquivalent (C "a") (C "a") m ~?= True
   , alphaEquivalent (C "a") (C "b") m ~?= False
   , alphaEquivalent (Lambda (V 1) (V 1)) (Lambda (V 2) (V 2)) m ~?= True
   , alphaEquivalent (Lambda (V 1) (V 2)) (Lambda (V 1) (V 1)) m ~?= False
   , alphaEquivalent (App (Lambda (V 1) (V 1)) (V 3)) (App (Lambda (V 2) (V 2)) (V 3)) m ~?= True
   , alphaEquivalent (Eta (V 1)) (Eta (V 1)) m ~?= True
   , alphaEquivalent ((V 1) :*: (Lambda (V 1) (V 2))) ((V 1) :*: (Lambda (V 1) (V 2))) m ~?= True
   , alphaEquivalent (Lambda (V 1) (V 1)) (Lambda (V 2) (V 1)) m ~?= False] where
    m = empty

testEtaReduce = "etaReduce" ~: TestList
   [ etaReduce (Lambda (V 1) (App (V 2) (V 1))) ~?= (V 2)
   , etaReduce (V 1) ~?= (V 1)
   , etaReduce (App (V 2) (V 1)) ~?= (App (V 2) (V 1))
   , etaReduce (Lambda (V 1) (App (Lambda (V 2) (App (V 3) (V 2))) (V 1))) ~?= (V 3) ]

testMonadReduce = "monadReduce" ~: TestList
   [ monadReduce ((Eta (V 1)) :*: (V 2)) ~?= (App (V 2) (V 1))
   , monadReduce ((V 1) :*: (Lambda (V 2) (Eta (V 2)))) ~?= (V 1) 
   , monadReduce ((V 1) :*: (Lambda (V 2) (Eta (V 3)))) ~?= ((V 1) :*: (Lambda (V 2) (Eta (V 3)))) ]

testEquivalentDecoratedSequent = "equivalentDecoratedSequent" ~: TestList
   [ equivalentDecoratedSequent ([] , DF 1 (V 1) a)
                                ([] , DF 1 (V 1) a) ~?= True
   , equivalentDecoratedSequent ([] , DF 1 (V 1) a)
                                ([] , DF 2 (V 1) a) ~?= True
   , equivalentDecoratedSequent ([] , DF 1 (V 2) a)
                                ([] , DF 1 (V 1) a) ~?= False
   , equivalentDecoratedSequent ([] , DF 1 (V 1) b)
                                ([] , DF 1 (V 1) a) ~?= False 
   , equivalentDecoratedSequent ([DF 1 (V 1) a], DF 2 (V 1) a)
                                ([DF 1 (V 2) a], DF 2 (V 2) a) ~?= True
   , equivalentDecoratedSequent ([DF 1 (V 1) a, DF 2 (V 2) b], DF 2 (V 1) a)
                                ([DF 1 (V 2) a, DF 2 (V 3) b], DF 2 (V 2) a) ~?= True ]

testMixMap = "mixMaps" ~: TestList
   [ mixMaps empty empty ~?= empty
   , mixMaps (Map.fromList [(a,1)]) (Map.fromList [(a,2)]) ~?= Map.fromList [(1,2)]
   , mixMaps (Map.fromList [(a,1),(b,2)]) (Map.fromList [(a,3),(b,2)]) ~?= Map.fromList [(1,3),(2,2)] ]

testParsers = "Parsers" ~: TestList
   [ read "a.a" ~?= atom "a" 
   , read "A.a" ~?= var "A" "a"
   , read "  A123 . a" ~?= var "A123" "a"
   , read "    abc123 .abc123 " ~?= atom "abc123" 
   , read "<>a.a" ~?= mon (atom "a") 
   , read "a.a -> b.b" ~?= (atom "a") .->. (atom "b")
   , read "a.a -> b.b -> c.c" ~?= (atom "a") .->. ((atom "b") .->. (atom "c")) 
   , read "a.a * b.b * c.c" ~?= (atom "a") .*. ((atom "b") .*. (atom "c"))
   , read "(a.a)" ~?= atom "a" 
   , read "<> (a.a)" ~?= mon (atom "a")
   , read "(<> a.a)" ~?= mon (atom "a")
   , read "(a.a -> b.b) -> c.c" ~?= ((atom "a") .->. (atom "b")) .->. (atom "c") 
   , read "(<> a.a -> b.b) -> <> c.c" ~?= ((mon $ atom "a") .->. (atom "b")) .->. (mon $ atom "c")
   , read "<><><>a.a -> b.b" ~?= (mon $ mon $ mon $ atom "a") .->. (atom "b") 
   , read "<><><>(a.a -> b.b)" ~?= (mon $ mon $ mon $ (atom "a") .->. (atom "b"))
   , parseSequent "a.a -> b.b , c.c , a.a => a.a" ~?= Right (Left (([a .->. b, c , a],a) :: Sequent))
   , parseSequent "f : a.a -> b.b, x : a.a => b.b" ~?= Right (Right ([(C "f", a .->. b) , (C "x", a)],b)) ]

testMonadicTP = runTestTT tests

-- QuickCheck

randFormula = sized aux where
  aux 0 = liftM atom (elements ["a","b","c","d"])
  aux n = oneof [ liftM atom (elements ["a","b","c","d"])
                , liftM mon subformula1
                , liftM2 (.->.) subformula2 subformula2] where
                  subformula1 = aux (n `div` 2)
                  subformula2 = aux (n `div` 2)

instance Arbitrary Formula where
  arbitrary = randFormula

-- quickTest = quickCheck (\s -> kompress (broofs s) == prove s)

main = do
  counts <- testMonadicTP
  if errors counts == 0 && failures counts == 0 then exitSuccess else exitFailure