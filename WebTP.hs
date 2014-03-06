module Main where

import Text.Blaze.Html5 hiding (map)
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes hiding (method,style)
import Happstack.Lite
import DataTypes
import HTML
import Parser
import TP
import NDS
import Data.Monoid
import Data.List
import System.Timeout
import Control.Monad.IO.Class

css_script = "em{font-weight:bold;} div{margin: 20px auto; width: 100%;} td {white-space: nowrap; text-align: center; vertical-align: bottom; padding-left: 5px; padding-right: 5px; font-family: \"Palatino Linotype\", \"Book Antiqua\", Palatino, serif; font-style: italic;} .title{ font-family: \"Lucida Sans Unicode\", \"Lucida Grande\", sans-serif; color: #5E5E5E;font-size: 17px; background-color: #FFFFFF; letter-spacing: 5.8pt;word-spacing: 3pt; line-height: 1.2; padding: 21px;} .verbatim{font-family:\"Lucida Console\", Monaco, monospace}"

conf = ServerConfig { port      = 8105
                    , ramQuota  = 1 * 10^6
                    , diskQuota = 20 * 10^6
                    , tmpDir    = "/tmp/"
                    }

main = serve (Just conf) app

app = do method POST
         seq <- lookText "seq"
         case parseSequent (toString seq) of
               Left s -> ok $ toResponse $ pageTemplate $ toHtml s
               Right s -> do
                 case s of
                   Left s -> printProofs s
                   Right s -> printProofsWithConstants s

toString = reverse . tail . reverse . tail . show 

printProofs s = do
  ps <- liftIO $ timeout 60000000 $ return $ (evalState (toDecorated s >>= \ds -> proofs ds) startState)
  case ps of 
    Just ps -> pproofs ps
    Nothing -> ok $ toResponse $ pageTemplate $ p $ toHtml "This is taking too long..."

printProofsWithConstants s = do
  ps <- return $ (evalState (toDecoratedWithConstants s >>= \(ds,m) -> proofs ds >>= \p -> return $ replaceWithConstants p m) startState)
  pproofs ps

pproofs ps = do
  ps <- return $ map sanitizeVars ps
  ps <- return $ nubByShortest (lambdaTermLength . term . snd . getVal) (\x y -> equivalentDecoratedSequent (getVal x) (getVal y)) ps
  case ps of
    [] -> ok $ toResponse $ pageTemplate $ p $ toHtml "Not a theorem"
    _ -> do
      ps <- return $ map (H.div . proof2html) ps
      ok $ toResponse $ pageTemplate $ mconcat ps

lambdaTermLength :: LambdaTerm -> Int
lambdaTermLength (V _) = 1
lambdaTermLength (C _) = 1
lambdaTermLength (Lambda x t) = lambdaTermLength x + lambdaTermLength t
lambdaTermLength (App f x) = lambdaTermLength f + lambdaTermLength x
lambdaTermLength (Eta t) = 1 + lambdaTermLength t
lambdaTermLength (m :*: k) = lambdaTermLength m + lambdaTermLength k                 
                    

pageTemplate h = do
   html $ do
      H.head $ style $ toHtml css_script
      body $ do
       H.div $ (h1 $ toHtml "Proofs") ! (class_ $ toValue "title")
       h      

nubByShortest :: Eq a => (a -> Int) -> 
                 (a -> a -> Bool) ->
                 [a] -> 
                 [a]
nubByShortest len eq l = aux l [] where
    aux [] acc = acc
    aux (a : as) acc = 
       case find (\x -> eq a x) acc of
         Nothing -> aux as (a : acc)
         Just a' -> case len a < len a' of
                        False -> aux as acc
                        True -> aux as (a : delete a' acc)