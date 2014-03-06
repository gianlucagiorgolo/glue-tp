module Txt where

import DataTypes

lambda2text :: LambdaTerm -> String
lambda2text (C c) = c
lambda2text (V n) | n < length sanevars && n >= 0 = sanevars !! n
          | otherwise = "v" ++ show n 
lambda2text (Lambda x b) = "\\" ++ lambda2text x ++ "." ++ lambda2text b
lambda2text (Eta f) = "eta(" ++ lambda2text f ++ ")"
lambda2text (App f@(Lambda _ _) a) = "(" ++ lambda2text f ++ ")(" ++ lambda2text a ++ ")"
lambda2text (App f@(_ :*: _) a) = "(" ++ lambda2text f ++ ")(" ++ lambda2text a ++ ")"
lambda2text (App f a) = lambda2text f ++ "(" ++ lambda2text a ++ ")"
lambda2text (m :*: k) = lambda2text m ++ ">>=" ++ lambda2text k 
lambda2text (Pair a b) = "<" ++ lambda2text a ++ "," ++ lambda2text b ++ ">"
lambda2text (FirstProjection a) = "p1(" ++ lambda2text a ++ ")"
lambda2text (SecondProjection a) = "p2(" ++ lambda2text a ++ ")"

formula2text :: Formula -> String
formula2text (Atom a _) = a
formula2text (Var x _) = x
formula2text (M (Atom a _) _) = "<>" ++ a
formula2text (M (Var x _) _) = "<>" ++ x
formula2text (M f _) = "<>(" ++ formula2text f ++ ")"
formula2text (I (Atom a _) f _) = a ++ " -> " ++ formula2text f
formula2text (I (Var a _) f _) = a ++ " -> " ++ formula2text f
formula2text (I d@(M _ _) f _) = formula2text d ++ " -> " ++ formula2text f
formula2text (I f g _) = "(" ++ formula2text f ++ ") -> " ++ formula2text g
formula2text (P (Atom a _) f _) = a ++ " * " ++ formula2text f
formula2text (P (Var a _) f _) = a ++ " * " ++ formula2text f
formula2text (P d@(M _ _) f _) = formula2text d ++ " * " ++ formula2text f
formula2text (P f g _) = "(" ++ formula2text f ++ ") * " ++ formula2text g
