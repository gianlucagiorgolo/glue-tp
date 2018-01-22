-- A module with some code to explore theorems in the monadic lambda calculus
module TP where

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable hiding (concat,any,all)
import Control.Monad.State
import DataTypes

startState :: S
startState = S (-1) Map.empty

-- Util

-- |The 'split' function splits a set (encoded as a list) in all possible ways.
--
-- >>> split [1,2]
-- [([],[1,2]),([1],[2]),([2],[1]),([1,2],[])]
split :: [a] -> [([a],[a])]
split [] = [([],[])]
split [a] = [([],[a]),([a],[])]
split (a : as) = left ++ right where
    left = [(a : l,r) | (l,r) <- rec]
    right = [(l, a : r) | (l,r) <- rec]
    rec = split as

-- |Returns the current state integer and decrease the state by one.
getAndDec :: NonDeterministicState S Int
getAndDec = do
    s <- get
    i <- return $ counter s
    modify (\x -> x{counter = (i-1)})
    return i

-- |Takes a sequent of formulae and generates fresh variables for each formula, wrapping it in a non-deterministic state
toDecorated :: Sequent -> NonDeterministicState S DecoratedSequent
toDecorated (gamma,f) = do
  aux <- return $ \x -> do
           i <- getAndDec
           j <- getAndDec
           return $ DF i (V j) x
  gamma' <- mapM aux gamma
  f' <- aux f
  return (gamma',f')

-- |Takes a decorated sequent and generates fresh variables for each formula, wrapping it in a non-deterministic state and returning a map from the new variables to the original constant terms
toDecoratedWithConstants :: ([(LambdaTerm,Formula)],Formula) -> NonDeterministicState S (DecoratedSequent,Map Int LambdaTerm)
toDecoratedWithConstants (gamma,f) = do
  aux <- return $ \(c,x) -> do
           i <- getAndDec
           j <- getAndDec
           return $ (DF i (V j) x,(i,c))
  gamma' <- mapM aux gamma
  f' <- do
    i <- getAndDec
    j <- getAndDec
    return $ DF i (V j) f
  return ((map fst gamma',f'),Map.fromList $ map snd gamma')

-- |Associates two formulae in the variable-formula binding map in the state
associate :: Formula -> Formula -> NonDeterministicState S ()
associate f g = do
  s <- get
  m <- return $ vars s
  modify (\x -> x{vars = Map.insert f g m})
  return ()

-- |Looks up the binding of a formula in the variable-formula binding map of the state
getBinding :: Formula -> NonDeterministicState S (Maybe Formula)
getBinding f = aux f [f] where
  aux f vs = do
   s <- get
   m <- return $ vars s
   res <- return $ Map.lookup f m
   case res of
     Nothing -> return Nothing
     Just v@(Var _ _ _) -> case Data.List.elem v vs of
                           False -> aux v (v : vs)
                           True -> return $ Just f
     Just f -> return $ Just f

-- |Tries to unify to formulae: returns 'True' in case of success (and associate the unified formulae) and 'False' otherwise (without changing the state)
unify :: Formula -> Formula -> NonDeterministicState S Bool
unify v1@(Var _ t1 _) v2@(Var _ t2 _)
    | t1 == t2 =
        do
          binding1 <- getBinding v1
          binding2 <- getBinding v2
          case binding1 of
            Nothing -> do
              associate v1 v2
              return True
            Just g -> case binding2 of
                        Nothing -> do
                          associate v2 v1
                          return True
                        Just f -> return $ f == g
    | otherwise = return False
unify v@(Var _ t _) f
    | t == (getType f) =
        do
          binding <- getBinding v
          case binding of
            Nothing -> do
              associate v f
              return True
            Just g -> return $ g == f
    | otherwise = return False
unify f v@(Var _ _ _) = unify v f
unify f g = return $ f == g

-- |Returns all the proofs for a given sequent
proofs :: DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
proofs s@(gamma,f) = do
  every $ map (\r -> r s) [iR,mR,tR] ++ map (\(r,g) -> r g (delete g gamma,f))
                                         [(r,g) | r <- [i,iL,mL,tL]
                                         , g <- gamma]


-- |The identity rule
i :: DecoratedFormula -> DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
i a (hyp,a') | not $ any isLinear (map formula hyp) = do
  res <- unify (formula a) (formula a')
  case res of
    False -> failure
    True -> do
             i <- getAndDec
             x <- return $ V i
             return $ Leaf Id ([DF (identifier a) x (formula a)]
                              , DF (identifier a') x (formula a'))
             | otherwise = failure
i _ _ = failure

-- |The left implication rule
iL :: DecoratedFormula -> DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
iL f@(DF _ _ (I a b ty lin)) (gamma,c) = do
  a_id <- getAndDec
  b_id <- getAndDec
  t <- getAndDec >>= \i -> return $ V i
  x <- getAndDec >>= \j -> return $ V j
  splits <- return $ split gamma
  proveChildren <- return $ \(g,g') -> do
    l <- proofs (g,DF a_id t a)
    r <- proofs (DF b_id x b : g',c)
    return (l,r)
  (l,r) <- every $ map proveChildren splits
  (delta,a') <- return $ getVal l
  ((gamma_with_b), c') <- return $ getVal r
  b' <- return $ lookupFormula b_id gamma_with_b
  gamma <- return $ delete b' gamma_with_b
  y <- getAndDec >>= \i -> return $ V i
  return $ Branch ImpL l (DF (identifier f) y (I a b ty lin) : gamma `union` delta
                         ,DF (identifier c') (sub (App y (term a')) (term b') (term c')) (formula c')) r
iL _ _ = failure

-- |The left diamond rule
mL :: DecoratedFormula -> DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
mL ma@(DF _ y (M a m1 _ _)) (gamma, f@(DF j _ (M b m2 tyb lin))) | m1 == m2 = do
  id_a <- getAndDec
  x <- getAndDec >>= \i -> return $ V i
  c <- proofs (DF id_a x a : gamma, f)
  (gamma_and_a,mb) <- return $ getVal c
  a <- return $ lookupFormula id_a gamma_and_a
  gamma <- return $ delete a gamma_and_a
  return $ Unary MonL (ma : gamma, DF j (y :*: (Lambda (term a) (term mb))) (M b m2 tyb lin)) c
                                                                 | otherwise = failure
mL _ _ = failure

-- |The left tensor rule
tL :: DecoratedFormula -> DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
tL ab@(DF _ y (P a b _ _)) (gamma, c) = do
  a_id <- getAndDec
  b_id <- getAndDec
  f <- getAndDec >>= \i -> return $ V i
  g <- getAndDec >>= \i -> return $ V i
  child <- proofs (DF a_id f a : DF b_id g b : gamma,c)
  (gamma_and_a_and_b,c') <- return $ getVal child
  a <- return $ lookupFormula a_id gamma_and_a_and_b
  b <- return $ lookupFormula b_id gamma_and_a_and_b
  gamma <- return $ delete a $ delete b gamma_and_a_and_b
  return $ Unary TensL (ab : gamma, DF (identifier c)
                                      (sub (FirstProjection y)
                                           (term a)
                                           (sub (SecondProjection y)
                                                (term b)
                                                (term c')))
                                                (formula c)) child
tL _ _ = failure

-- |The right implication rule
iR :: DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
iR (gamma, DF i _ f@(I a b _ _)) = do
  a_id <- getAndDec
  b_id <- getAndDec
  x <- getAndDec >>= \i -> return $ V i
  t <- getAndDec >>= \i -> return $ V i
  c <- proofs (DF a_id x a : gamma, DF b_id t b)
  (gamma_and_a,b) <- return $ getVal c
  a <- return $ lookupFormula a_id gamma_and_a
  gamma <- return $ delete a gamma_and_a
  return $ Unary ImpR (gamma, DF i (Lambda (term a) (term b)) f) c
iR _ = failure

-- |The right diamond rule
mR :: DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
mR (gamma,DF i _ ma@(M a _ _ _)) = do
  a_id <- getAndDec
  x <- getAndDec >>= \i -> return $ V i
  c <- proofs (gamma,DF a_id x a)
  (gamma,a) <- return $ getVal c
  return $ Unary MonR (gamma,DF i (Eta (term a)) ma) c
mR _ = failure

-- |The right tensor rule
tR :: DecoratedSequent -> NonDeterministicState S (BinTree DecoratedSequent)
tR (gamma,DF i _ f@(P a b _ _)) = do
  a_id <- getAndDec
  b_id <- getAndDec
  t <- getAndDec >>= \i -> return $ V i
  u <- getAndDec >>= \i -> return $ V i
  splits <- return $ split gamma
  proveChildren <- return $ \(g,g') -> do
     l <- proofs (g,DF a_id t a)
     r <- proofs (g',DF b_id u b)
     return (l,r)
  (l,r) <- every $ map proveChildren splits
  (gamma,a) <- return $ getVal l
  (delta,b) <- return $ getVal r
  return $ Branch TensR l (gamma `union` delta, DF i (Pair (term a) (term b)) f) r
tR _ = failure

-- |This function searches for a formula in a list of formulae by comparing their unique ids.
-- It's meant to be used only by the left implication and left monad rules.
-- Raises an error if no formula with the given id is found
lookupFormula :: Int -> [DecoratedFormula] -> DecoratedFormula
lookupFormula _ [] = error "This will never be reached by the rules"
lookupFormula n (f : rest) | n == (identifier f) = f
                           | otherwise = lookupFormula n rest

-- |Substitute a term for another inside a third term (should be the substitution of a variable with a term)
sub :: LambdaTerm -> -- the new term
       LambdaTerm -> -- the variable/old term
       LambdaTerm -> -- the context
       LambdaTerm    -- the new term
sub _ _ c@(C _) = c
sub new old t@(V _) | t == old = new
                    | otherwise = t
sub new old t@(Lambda v b) | v == old = t
                           | otherwise = Lambda v $ sub new old b
sub new old (App f a) = App (sub new old f) (sub new old a)
sub new old (Eta f) = Eta (sub new old f)
sub new old (m :*: k) = (:*:) (sub new old m) (sub new old k)
sub new old (Pair a b) = Pair (sub new old a) (sub new old b)
sub new old (FirstProjection a) = FirstProjection $ sub new old a
sub new old (SecondProjection a) = SecondProjection $ sub new old a

-- |Collects all variables from a proof
collectVars :: BinTree DecoratedSequent -> Set LambdaTerm
collectVars t = Set.fromList $ foldMap aux t where
  aux = concat . (map f) . (map term) . j
  j (c,f) = f : c
  f v@(V _) = [v]
  f (C _) = []
  f (Lambda v t) = f v ++ f t
  f (App g a) = f g ++ f a
  f (Eta x) = f x
  f (m :*: k) = f m ++ f k
  f (Pair a b) = f a ++ f b
  f (FirstProjection a) = f a
  f (SecondProjection a) = f a

-- |Changes all the negative indices used in the vars to contiguos positive integers
sanitizeVars :: BinTree DecoratedSequent -> BinTree DecoratedSequent
sanitizeVars t = fmap sanitize t where
  sanitize (gamma,f) = (map deepSub gamma,deepSub f)
  deepSub (DF i lt f) = (DF i (zub lt) f)
  zub (V i) = V $ fromJust $ lookup i m
  zub c@(C _) = c
  zub (Lambda x t) = Lambda (zub x) (zub t)
  zub (App f g) = App (zub f) (zub g)
  zub (Eta x) = Eta (zub x)
  zub (m :*: k) = (zub m) :*: (zub k)
  zub (Pair a b) = Pair (zub a) (zub b)
  zub (FirstProjection a) = FirstProjection $ zub a
  zub (SecondProjection a) = SecondProjection $ zub a
  m = zip (map (\(V i) -> i) $ Set.toList $ collectVars t) [0..]

replaceWithConstants :: BinTree DecoratedSequent -> (Map Int LambdaTerm) -> BinTree DecoratedSequent
replaceWithConstants t m = fmap (\n -> replaceWithConstantsInNode n m) t

replaceWithConstantsInNode :: DecoratedSequent -> (Map Int LambdaTerm) -> DecoratedSequent
replaceWithConstantsInNode (gamma,f) m = new where
    new = (map fst gamma', deepSub f)
    gamma' = map replace gamma
    n = map fromJust $ filter isJust $ map snd gamma'
    replace df@(DF i v f) = case Map.lookup i m of
                             Nothing -> (df,Nothing)
                             Just c -> (DF i c f,Just (v,c))
    deepSub (DF i lt f) = (DF i (zub lt) f)
    zub v@(V _) = case lookup v n of
                    Nothing -> v
                    Just c -> c
    zub c@(C _) = c
    zub (Lambda x t) = Lambda (zub x) (zub t)
    zub (App f g) = App (zub f) (zub g)
    zub (Eta x) = Eta (zub x)
    zub (m :*: k) = (zub m) :*: (zub k)
    zub (Pair a b) = Pair (zub a) (zub b)
    zub (FirstProjection a) = FirstProjection $ zub a
    zub (SecondProjection a) = SecondProjection $ zub a



alphaEquivalent :: LambdaTerm -> LambdaTerm -> Map Int Int -> Bool
alphaEquivalent c1@(C _) c2@(C _) _ = c1 == c2
alphaEquivalent (V i) (V j) m = case Map.lookup i m of
        Just h -> j == h
        Nothing -> i == j
alphaEquivalent (Lambda (V i) t) (Lambda (V j) u) m = alphaEquivalent t u (Map.insert i j m)
alphaEquivalent (App t s) (App d z) m = (alphaEquivalent t d m) && (alphaEquivalent s z m)
alphaEquivalent (Eta t) (Eta d) m = alphaEquivalent t d m
alphaEquivalent (t :*: s) (d :*: z) m = (alphaEquivalent t d m) && (alphaEquivalent s z m)
alphaEquivalent (Pair a b) (Pair a' b') m = alphaEquivalent a a' m && alphaEquivalent b b' m
alphaEquivalent (FirstProjection a) (FirstProjection b) m = alphaEquivalent a b m
alphaEquivalent (SecondProjection a) (SecondProjection b) m = alphaEquivalent a b m
alphaEquivalent _ _ _ = False

-- |This function works only under the assumption that all the formulae in the hypothesis are distinct, otherwise the answer is NO!
equivalentDecoratedSequent :: DecoratedSequent -> DecoratedSequent -> Bool
equivalentDecoratedSequent s1 s2 = f1 == f2 && hypEqual && noDuplicates && alphaEquivalent t1 t2 e where
    noDuplicates = (length $ Set.toList $ Set.fromList (map formula hyp1)) == length hyp1 &&
                   (length $ Set.toList $ Set.fromList (map formula hyp2)) == length hyp2
    hyp1 = fst s1
    hyp2 = fst s2
    hypEqual = (Set.fromList (map formula hyp1)) == (Set.fromList (map formula hyp2))
    varId (V i) = i
    varId _ = -1
    m1 = Map.fromList $ map (\x -> (formula x, varId $ term x)) hyp1
    m2 = Map.fromList $ map (\x -> (formula x, varId $ term x)) hyp2
    e = mixMaps m1 m2
    t1 = betaReduce $ monadReduce $ etaReduce $ term $ snd $ s1
    t2 = betaReduce $ monadReduce $ etaReduce $ term $ snd $ s2
    f1 = formula $ snd $ s1
    f2 = formula $ snd $ s2

mixMaps :: Map Formula Int -> Map Formula Int -> Map Int Int
mixMaps m n = Map.fromList $ aux (Map.toList m) where
    aux [] = []
    aux ((f,i) : rest) = (i,n Map.! f) : aux rest

etaReduce :: LambdaTerm -> LambdaTerm
etaReduce c@(C _) = c
etaReduce v@(V _) = v
etaReduce (App f g) = App (etaReduce f) (etaReduce g)
etaReduce (Eta t) = Eta $ etaReduce t
etaReduce (m :*: k) = (etaReduce m) :*: (etaReduce k)
etaReduce (Pair a b) = Pair (etaReduce a) (etaReduce b)
etaReduce (FirstProjection a) = FirstProjection $ etaReduce a
etaReduce (SecondProjection a) = SecondProjection $ etaReduce a
etaReduce (Lambda (V i) (App f (V j))) | i == j = etaReduce f
                                       | otherwise = Lambda (V i) (App (etaReduce f) (V j))
etaReduce (Lambda x t) = let x' = etaReduce x
                             t' = etaReduce t
                         in if t == t' then
                                Lambda x' t'
                            else
                                etaReduce (Lambda x' t')

betaReduce :: LambdaTerm -> LambdaTerm
betaReduce t = aux t Map.empty where
   aux c@(C _) _ = c
   aux v@(V i) m = case Map.lookup i m of
       Nothing -> v
       Just t -> t
   aux (App (Lambda (V i) body) x) m = aux body (Map.insert i x m)
   aux (App f x) m = let f' = aux f m
                     in if f == f' then
                           (App f (aux x m))
                        else
                           aux (App f' x) m
   aux (Lambda x b) m = Lambda (aux x m) (aux b m)
   aux (Eta t) m = Eta $ aux t m
   aux (n :*: k) m = (aux n m) :*: (aux k m)
   aux (Pair a b) m = Pair (aux a m) (aux b m)
   aux (FirstProjection a) m = FirstProjection $ aux a m
   aux (SecondProjection a) m = SecondProjection $ aux a m

monadReduce :: LambdaTerm -> LambdaTerm
monadReduce ((Eta t) :*: u) = App (monadReduce u) (monadReduce t)
monadReduce (t :*: (Lambda (V i) (Eta (V j)))) | i == j = monadReduce t
                                               | otherwise = (monadReduce t) :*: (Lambda (V i) (Eta (V j)))
monadReduce v@(V _) = v
monadReduce c@(C _) = c
monadReduce (App t u) = App (monadReduce t) (monadReduce u)
monadReduce (Lambda x t) = Lambda (monadReduce x) (monadReduce t)
monadReduce (Eta t) = Eta $ monadReduce t
monadReduce (Pair a b) = Pair (monadReduce a) (monadReduce b)
monadReduce (FirstProjection a) = FirstProjection $ monadReduce a
monadReduce (SecondProjection a) = SecondProjection $ monadReduce a
monadReduce (t :*: u) = let t' = monadReduce t
                            u' = monadReduce u
                        in if t == t' && u == u' then
                               t' :*: u'
                           else
                               monadReduce (t' :*: u')
