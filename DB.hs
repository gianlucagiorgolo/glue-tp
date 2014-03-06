module DB where
import TP
import Control.Monad.State
test = evalState (toDecorated ([M (Atom "c" :->: Atom "a") :->: Atom "a",Atom "b" :->: ((Atom "a" :->: Atom "b") :->: (Atom "b" :->: Atom "c")),Atom "b" :->: ((Atom "d" :->: Atom "b") :->: Atom "d"),M ((Atom "b" :->: Atom "b") :->: (Atom "b" :->: Atom "a"))],Atom "b") >>= \s -> proofs s) 0