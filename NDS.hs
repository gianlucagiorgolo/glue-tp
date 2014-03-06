-- Non-deterministic state

module NDS where

data NonDeterministicState s a = NDS { runState :: s -> [(a,s)]}

instance Monad (NonDeterministicState s) where
    return x = NDS $ \s -> [(x,s)]
    m >>= k  = NDS $ \s -> concat $ map (\(a,s) -> (runState $ k a) s) ((runState m) s)

get :: NonDeterministicState s s
get = NDS $ \s -> [(s,s)]

put :: s -> NonDeterministicState s ()
put s = NDS $ \_ -> [((),s)]

modify :: (s -> s) -> NonDeterministicState s ()
modify f = do
  s <- get
  put (f s)

evalState :: NonDeterministicState s a -> s -> [a]
evalState m s = map fst $ (runState m) s

failure :: NonDeterministicState s a
failure = NDS $ \_ -> []

both :: NonDeterministicState s a -> NonDeterministicState s a -> NonDeterministicState s a
both m n = NDS $ \s -> ((runState m) s) ++ ((runState n) s)

every :: [NonDeterministicState s a] -> NonDeterministicState s a
every = foldr both failure


