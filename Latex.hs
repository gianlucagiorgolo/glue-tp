module Latex where

import Data.List
import DataTypes

texheader = "\\usepackage{amsmath,amssymb,bussproofs}\\usepackage[paperwidth=40cm]{geometry}"

proof2tex :: BinTree DecoratedSequent -> String
proof2tex (Leaf lab s) = "\\AxiomC{}" ++ lab2tex lab ++ "\\UnaryInfC{$" ++ decoratedSeq2tex s ++ "$}\n"
proof2tex (Unary lab s t) = proof2tex t ++ lab2tex lab ++ "\\UnaryInfC{$" ++ decoratedSeq2tex s ++ "$}\n"
proof2tex (Branch lab l s r) = proof2tex l ++ proof2tex r ++ lab2tex lab ++ "\\BinaryInfC{$" ++ decoratedSeq2tex s ++ "$}\n"

lab2tex :: Label -> String
lab2tex Id = "\\RightLabel{$id$}"
lab2tex ImpL = "\\RightLabel{$\\multimap L$}"
lab2tex ImpR = "\\RightLabel{$\\multimap R$}"
lab2tex MonL = "\\RightLabel{$\\lozenge L$}"
lab2tex MonR = "\\RightLabel{$\\lozenge R$}"
lab2tex TensL = "\\RightLabel{$\\otimes L$}"
lab2tex TensR = "\\RightLabel{$\\otimes R$}"

lambda2tex :: LambdaTerm -> String
lambda2tex (C c) = "\\mathbf{" ++ c ++ "}"
lambda2tex (V n) | n < length sanevars && n >= 0 = sanevars !! n
                 | otherwise = "v_{" ++ show n ++ "}"
lambda2tex (Lambda x b) = "\\lambda " ++ lambda2tex x ++ " . " ++ lambda2tex b
lambda2tex (Eta f) = "\\eta(" ++ lambda2tex f ++ ")"
lambda2tex (App f@(Lambda _ _) a) = "(" ++ lambda2tex f ++ ")(" ++ lambda2tex a ++ ")"
lambda2tex (App f@(_ :*: _) a) = "(" ++ lambda2tex f ++ ")(" ++ lambda2tex a ++ ")"
lambda2tex (App f a) = lambda2tex f ++ "(" ++ lambda2tex a ++ ")"
lambda2tex (m :*: k) = lambda2tex m ++ "\\star" ++ lambda2tex k
lambda2tex (Pair a b) = "\\langle " ++ lambda2tex a ++ "," ++ lambda2tex b ++ "\\rangle"
lambda2tex (FirstProjection a) = "\\pi_{1}(" ++ lambda2tex a ++ ")"
lambda2tex (SecondProjection a) = "\\pi_{2}(" ++ lambda2tex a ++ ")"

decoratedSeq2tex :: DecoratedSequent -> String
decoratedSeq2tex (gamma,c) = left ++ "\\vdash " ++ f c where
    left = intercalate ", " $ map f gamma
    f (DF _ lt f) = lambda2tex lt ++ " : " ++ formula2latex f

texifySequent :: DecoratedSequent -> String
texifySequent (gamma,c) = left ++ "\\vdash " ++ formula2latex (formula c) where
    left = intercalate ", " $ map (formula2latex . formula) gamma

simpleproof2tex :: BinTree DecoratedSequent -> String
simpleproof2tex (Leaf lab s) = "\\AxiomC{}" ++ lab2tex lab ++ "\\UnaryInfC{$" ++ texifySequent s ++ "$}\n"
simpleproof2tex (Unary lab s t) = simpleproof2tex t ++ lab2tex lab ++ "\\UnaryInfC{$" ++ texifySequent s ++ "$}\n"
simpleproof2tex (Branch lab l s r) = simpleproof2tex l ++ simpleproof2tex r ++ lab2tex lab ++ "\\BinaryInfC{$" ++ texifySequent s ++ "$}\n"


-- |Texifies a formula (now with smart parentheses!)
formula2latex :: Formula -> String
formula2latex (Atom a _) = a
formula2latex (Var x _) = x
formula2latex (M (Atom a _) _) = "\\lozenge " ++ a
formula2latex (M (Var x _) _) = "\\lozenge " ++ x
formula2latex (M f _) = "\\lozenge (" ++ formula2latex f ++ ")"
formula2latex (I (Atom a _) f _) = a ++ " \\multimap " ++ formula2latex f
formula2latex (I (Var a _) f _) = a ++ " \\multimap " ++ formula2latex f
formula2latex (I d@(M _ _) f _) = formula2latex d ++ " \\multimap " ++ formula2latex f
formula2latex (I f g _) = "(" ++ formula2latex f ++ ") \\multimap " ++ formula2latex g
formula2latex (P (Atom a _) f _) = a ++ " \\otimes " ++ formula2latex f
formula2latex (P (Var a _) f _) = a ++ " \\otimes " ++ formula2latex f
formula2latex (P d@(M _ _) f _) = formula2latex d ++ " \\otimes " ++ formula2latex f
formula2latex (P f g _) = "(" ++ formula2latex f ++ ") \\otimes " ++ formula2latex g
