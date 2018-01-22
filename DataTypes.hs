module DataTypes where

import Data.Foldable hiding (msum)
import Data.Map (Map)
import Data.Monoid
import Control.Monad.State
import Data.Traversable
import Data.Functor
import Control.Applicative

type Modality = String

data Type = TAtomic String
          | TMonadic Modality Type
          | TPair Type Type
          | TFunctional Type Type deriving (Eq, Show, Ord)

data Linearity = Linear
               | Classical deriving (Eq,Show,Ord)

data Formula = Atom String Type Linearity
             | Var String Type Linearity
             | M Formula Modality Type Linearity
             | P Formula Formula Type Linearity
             | I Formula Formula Type Linearity deriving (Eq, Show, Ord)

isLinear :: Formula -> Bool
isLinear (Atom _ _ Linear) = True
isLinear (Var _ _ Linear) = True
isLinear (M _ _ _ Linear) = True
isLinear (P _ _ _ Linear) = True
isLinear (I _ _ _ Linear) = True
isLinear _ = False

defAtom s t = Atom s t Linear
defVar s t = Var s t Linear
defMonad f m t = M f m t Linear
defPair f g t = P f g t Linear
defImpl f g t = I f g t Linear

changeLinearity :: Linearity -> Formula -> Formula
changeLinearity l (Atom s t _) = Atom s t l
changeLinearity l (Var s t _) = Var s t l
changeLinearity l (M f m t _) = M f m t l
changeLinearity l (P f g t _) = P f g t l
changeLinearity l (I f g t _) = I f g t l

getType :: Formula -> Type
getType (Atom _ t _) = t
getType (Var _ t _) = t
getType (M _ _ t _) = t
getType (I _ _ t _) = t
getType (P _ _ t _) = t

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

instance Traversable BinTree where
  traverse f (Leaf l a) = (Leaf l) <$> f a
  traverse f (Unary l a c) = (Unary l) <$> f a <*> traverse f c
  traverse f (Branch lab l a r) = (Branch lab) <$> traverse f l <*> f a <*> traverse f r

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

-- |Translates a lambda term into an Haskell expression. The output is not meant to be pretty. We could have used Language.Haskell.Syntax but it seems overkill for our purposes
toHaskell :: LambdaTerm -> String
toHaskell (V i) = "__v" ++ (show i) ++ "__"
toHaskell (C s) = s
toHaskell (Lambda x t) = "(\\ " ++ toHaskell x ++ " -> " ++ toHaskell t ++ ")"
toHaskell (App f x) = "(" ++ toHaskell f ++ " " ++ toHaskell x ++ ")"
toHaskell (Pair t u) = "(" ++ toHaskell t ++ "," ++ toHaskell u ++ ")"
toHaskell (FirstProjection p) = "(fst " ++ toHaskell p ++ ")"
toHaskell (SecondProjection p) = "(snd " ++ toHaskell p ++ ")"
toHaskell (Eta t) = "(return " ++ toHaskell t ++ ")"
toHaskell (m :*: k) = "(" ++ toHaskell m ++ " >>= " ++ toHaskell k ++ ")"
