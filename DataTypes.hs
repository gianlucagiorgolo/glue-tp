module DataTypes where

import Data.Foldable hiding (msum)
import Data.Map (Map)
import Data.Monoid
import Control.Monad.State

data Type = TAtomic String
          | TMonadic Type
          | TPair Type Type         
          | TFunctional Type Type deriving (Eq, Show, Ord)

data Formula = Atom String Type
             | Var String Type
             | M Formula Type
             | P Formula Formula Type
             | I Formula Formula Type deriving (Eq, Show, Ord)

getType :: Formula -> Type
getType (Atom _ t) = t
getType (Var _ t) = t
getType (M _ t) = t
getType (I _ _ t) = t
getType (P _ _ t) = t

type Context = [Formula]
type Sequent = (Context, Formula)

-- infixr 7 :->:

data BinTree a = Branch Label (BinTree a) a (BinTree a)
               | Unary Label a (BinTree a)
               | Leaf Label a deriving (Eq, Show)

instance Foldable BinTree where
  foldMap f (Leaf _ a) = f a
  foldMap f (Unary _ a c) = f a `mappend` foldMap f c
  foldMap f (Branch _ l a r) = foldMap f l `mappend` f a `mappend` foldMap f r                     

instance Functor BinTree where
  fmap f (Leaf l a) = Leaf l (f a)
  fmap f (Unary l a c) = Unary l (f a) (fmap f c)
  fmap f (Branch lab l a r) = Branch lab (fmap f l) (f a) (fmap f r)

getVal :: BinTree a -> a
getVal (Leaf _ a) = a
getVal (Branch _ _ a _) = a
getVal (Unary _ a _) = a

setVal :: a -> BinTree a -> BinTree a
setVal a (Leaf l _) = Leaf l a
setVal a (Branch lab l _ r) = Branch lab l a r
setVal a (Unary l _ c) = Unary l a c

data Label = Id
           | ImpL
           | ImpR
           | TensL
           | TensR
           | MonL
           | MonR deriving (Eq, Show)

-- Curry Howard

data LambdaTerm = V Int
                | C String
                | Lambda LambdaTerm LambdaTerm -- this definition sucks because we want only variables but it'll do for now
                | App LambdaTerm LambdaTerm 
                | Pair LambdaTerm LambdaTerm
                | FirstProjection LambdaTerm
                | SecondProjection LambdaTerm                              
                | Eta LambdaTerm
                | LambdaTerm :*: LambdaTerm deriving (Eq, Show, Ord) -- also this one is a poor definition

infixr 7 :*:

data DecoratedFormula = DF { identifier :: Int
                           , term :: LambdaTerm
                           , formula :: Formula } deriving Show

instance Eq DecoratedFormula where
  f == g = (identifier f) == (identifier g)

type DecoratedSequent = ([DecoratedFormula],DecoratedFormula)

data S = S { counter :: Int
           , vars    :: Map Formula Formula} deriving Show

sanevars = ["x","y","z","w","v","k","h","l","m","n","a","b","c","d","e"]

type NonDeterministicState s a = StateT s [] a

failure :: NonDeterministicState s a
failure = StateT $ \_ -> []

every :: [NonDeterministicState s a] -> NonDeterministicState s a
every = msum

evaluateState :: NonDeterministicState s a -> s -> [a]
evaluateState = evalStateT