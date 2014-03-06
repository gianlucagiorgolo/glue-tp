module XHTML where

import Text.XHtml
import Data.List
import DataTypes
import Data.Monoid

proof2html :: BinTree DecoratedSequent -> Html 
proof2html (Leaf lab s) = 
		table << ((tr << "") +++ 
			  (tr << ((td << hr) +++ (td << lab2html lab))) +++
			  (tr << td << decoratedSeq2html s))
proof2html (Unary lab s t) = 
		table << ((tr << td << proof2html t) +++
			  (tr << ((td << hr) +++ (td << lab2html lab))) +++
			  (tr << td << decoratedSeq2html s))
proof2html (Branch lab l s r) = 
		table << ((tr << ((td << proof2html l) +++
			    	  (td << proof2html r))) +++
  			  (tr << ((td << hr) ! [intAttr "colspan" 2] +++
				  (td << lab2html lab))) +++
			  (tr << (td << decoratedSeq2html s) ! [intAttr "colspan" 2]))

lab2html :: Label -> Html
lab2html Id = toHtml "id"
lab2html ImpL = primHtml "&rarr;L"
lab2html ImpR = primHtml "&rarr;R"
lab2html MonL = primHtml "&loz;L"
lab2html MonR = primHtml "&loz;R"
lab2html TensL = primHtml "&otimes;L"
lab2html TensR = primHtml "&otimes;R"

lambda2html :: LambdaTerm -> Html
lambda2html (C c) = bold << c
lambda2html (V n) | n < length sanevars && n >= 0 = 
		   toHtml $ sanevars !! n
                  | otherwise = toHtml $ "v" ++ show n
lambda2html (Lambda x b) = 
	primHtml "&lambda;" +++
	lambda2html x +++
	toHtml "." +++
	lambda2html b
lambda2html (Eta f) =
	primHtml "&eta;(" +++
	lambda2html f +++
	toHtml ")"
lambda2html (App f@(Lambda _ _) a) =
	toHtml "(" +++
	lambda2html f +++
	toHtml ")(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (App f@(_ :*: _) a) = 
	toHtml "(" +++
	lambda2html f +++
	toHtml ")(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (App f a) = 
	lambda2html f +++
	toHtml "(" +++
	lambda2html a +++
	toHtml ")"
lambda2html (m :*: k) = 
	lambda2html m +++
	primHtml " &lowast; " +++
	lambda2html k
lambda2html (Pair a b) = 
        primHtml "&lt;" +++
        lambda2html a +++
        toHtml "," +++
        lambda2html b +++
        primHtml "&gt;"
lambda2html (FirstProjection a) = 
        primHtml "&pi;1(" +++
        lambda2html a +++
        toHtml ")"
lambda2html (SecondProjection a) = 
        primHtml "&pi;2(" +++
        lambda2html a +++
        toHtml ")"

decoratedSeq2html :: DecoratedSequent -> Html
decoratedSeq2html (gamma,c) = mconcat left +++ toHtml " => " +++ f c where
    left = intersperse (toHtml ", ") $ map f gamma
    f (DF _ lt f) = lambda2html lt +++ toHtml " : " +++ formula2html f

-- |Texifies a formula (now with smart parentheses!)
formula2html :: Formula -> Html
formula2html (Atom a _) = toHtml a
formula2html (Var x _) = toHtml x
formula2html (M (Atom a _) _) = primHtml "&loz;" +++ a
formula2html (M (Var x _) _) = primHtml "&loz;" +++ x
formula2html (M f _) = primHtml "&loz;(" +++ formula2html f +++ toHtml ")"
formula2html (P (Atom a _) f _) = a +++ primHtml " &otimes; " +++ formula2html f
formula2html (P (Var a _) f _) = a +++ primHtml " &otimes; " +++ formula2html f
formula2html (P d@(M _ _) f _) = formula2html d +++ primHtml " &otimes; " +++ formula2html f
formula2html (P a b _) = toHtml "(" +++ formula2html a +++ primHtml ") &otimes; " +++ formula2html b
formula2html (I (Atom a _) f _) = a +++ primHtml " &rarr; " +++ formula2html f
formula2html (I (Var a _) f _) = a +++ primHtml " &rarr; " +++ formula2html f
formula2html (I d@(M _ _) f _) = formula2html d +++ primHtml " &rarr; " +++ formula2html f
formula2html (I f g _) = 
		toHtml "(" +++
		formula2html f +++
		primHtml ") &rarr; " +++
		formula2html g

