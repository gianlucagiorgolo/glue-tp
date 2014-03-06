module HTML where

import Text.Blaze.Html5 hiding (map)
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes
import Data.List
import DataTypes
import Data.Monoid

proof2html :: BinTree DecoratedSequent -> Html 
proof2html (Leaf lab s) = 
		table $ do
			tr $ toHtml ""
			tr $ do
				td $ hr
				td $ lab2html lab
			tr $ td $ decoratedSeq2html s
proof2html (Unary lab s t) = 
		table $ do
			tr $ td $ proof2html t
			tr $ do
				td $ hr
				td $ lab2html lab
			tr $ td $ decoratedSeq2html s
proof2html (Branch lab l s r) = 
		table $ do
			tr $ do
				td $ proof2html l
				td $ proof2html r
			tr $ do
				(td $ hr) ! (colspan $ toValue "2")
				td $ lab2html lab
			tr $ (td $ decoratedSeq2html s) ! (colspan $ toValue "2")

lab2html :: Label -> Html
lab2html Id = toHtml "id"
lab2html ImpL = preEscapedToHtml "&rarr;L"
lab2html ImpR = preEscapedToHtml "&rarr;R"
lab2html MonL = preEscapedToHtml "&loz;L"
lab2html MonR = preEscapedToHtml "&loz;R"

lambda2html :: LambdaTerm -> Html
lambda2html (C c) = em $ toHtml c
lambda2html (V n) | n < length sanevars && n >= 0 = 
		toHtml $ sanevars !! n
                  | otherwise = toHtml $ "v" ++ show n
lambda2html (Lambda x b) = do 
	preEscapedToHtml "&lambda;"
	lambda2html x 
	toHtml "."
	lambda2html b
lambda2html (Eta f) = do
	preEscapedToHtml "&eta;("
	lambda2html f
	toHtml ")"
lambda2html (App f@(Lambda _ _) a) = do
	toHtml "("
	lambda2html f 
	toHtml ")("
	lambda2html a 
	toHtml ")"
lambda2html (App f@(_ :*: _) a) = do
	toHtml "("
	lambda2html f 
	toHtml ")(" 
	lambda2html a 
	toHtml ")"
lambda2html (App f a) = do
	lambda2html f 
	toHtml "(" 
	lambda2html a 
	toHtml ")"
lambda2html (m :*: k) = do
	lambda2html m 
	preEscapedToHtml " &lowast; "
	lambda2html k

decoratedSeq2html :: DecoratedSequent -> Html
decoratedSeq2html (gamma,c) = mconcat left >> toHtml " => " >> f c where
    left = intersperse (toHtml ", ") $ map f gamma
    f (DF _ lt f) = lambda2html lt >> toHtml " : " >> formula2html f

-- |Texifies a formula (now with smart parentheses!)
formula2html :: Formula -> Html
formula2html (Atom a _) = toHtml a
formula2html (Var x _) = toHtml x
formula2html (M (Atom a _) _) = preEscapedToHtml "&loz;" >> toHtml a
formula2html (M (Var x _) _) = preEscapedToHtml "&loz;" >> toHtml x
formula2html (M f _) = preEscapedToHtml "&loz;(" >> formula2html f >> toHtml ")"
formula2html (I (Atom a _) f _) = toHtml a >> preEscapedToHtml " &rarr; " >> formula2html f
formula2html (I (Var a _) f _) = toHtml a >> preEscapedToHtml " &rarr; " >> formula2html f
formula2html (I d@(M _ _) f _) = formula2html d >> preEscapedToHtml " &rarr; " >> formula2html f
formula2html (I f g _) = do
		toHtml "("
		formula2html f
		preEscapedToHtml ") &rarr; "
		formula2html g

