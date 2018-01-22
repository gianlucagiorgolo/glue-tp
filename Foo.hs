module Main where

import DataTypes
import TP
import Parser
import XHTML
import Data.Monoid
import Text.XHtml

s :: Sequent
s = (read "[<p>s.s, s.s -> <ci>s.s,<p>s.s -> <p>f.f]",read "<p><ci>f.f")

ur :: UnlimitedResources
ur = [(C "d_p_ci", read "<p><ci>X.* -> <ci><p>X.*"),(C "d_ci_p", read "<ci><p>Y.* -> <p><ci>Y.*")]

foo s ur = length $ evaluateState (toDecorated s ur >>= \s' -> proofs $ fst s') startState


main =
  putStrLn $ showHtml $ mconcat $ map proof2html $ evaluateState (toDecorated s ur >>= \s' -> proofs $ fst s') startState
