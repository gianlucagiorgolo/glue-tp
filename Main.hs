module Main where

import Latex
import Parser
import System.IO
import NDS
import System.Cmd
import TP
import qualified Data.Map as Map
import Data.List
import System.Directory
import System.FilePath
import Txt
import DataTypes
import Control.Monad

data Env = Env { temp_dir :: FilePath 
               , tex_file :: FilePath
               , pdf_file :: FilePath
               , cmd :: Maybe FilePath
               , showAll :: Bool } deriving Show

data Cmd = Seq (Either String (Either Sequent ([(LambdaTerm,Formula)],Formula)))
         | ShowAll
         | ShowEquiv
         | SwitchOutput
         | Help

main = do
  temp_dir <- getTemporaryDirectory
  tex_file <- return $ joinPath [temp_dir,"mgtroofs.tex"]
  pdf_file <- return $ joinPath [temp_dir,"mgtroofs.pdf"]
  cmd1 <- findExecutable "pdflatex"
  cmd2 <- findExecutable "pdflatex.exe"
  cmd <- return $ mplus cmd1 cmd2
  loop $ Env temp_dir tex_file pdf_file cmd False

parseLine :: String -> Cmd
parseLine ":all" = ShowAll
parseLine ":equiv" = ShowEquiv
parseLine ":help" = Help
parseLine ":switch_output" = SwitchOutput
parseLine s = Seq $ parseSequent s

loop env = do
  putStr "Enter sequent > "
  hFlush stdout
  line <- getLine
  case parseLine line of
    Help -> printHelp >> loop env
    ShowAll -> loop $ env{showAll = True}
    ShowEquiv -> loop $ env{showAll = False}
    SwitchOutput -> do
      env' <- case cmd env of 
                Just _ -> return env{cmd=Nothing}
                Nothing -> do
                          cmd1 <- findExecutable "pdflatex"
                          cmd2 <- findExecutable "pdflatex.exe"
                          cmd <- return $ mplus cmd1 cmd2
                          return env{cmd=cmd}
      loop env'
    Seq parse -> case parse of
                   Left s -> do
                              putStrLn s
                              main
                   Right s -> case s of
                                Left s -> do
                                       printProofs s env
                                       loop env
                                Right s -> do
                                       printProofsWithConstants s env
                                       loop env

printHelp = putStrLn ":all - shows all derivations\n:equiv - shows only non-equivalent derivations\n:switch_output - switches between pdf and ASCII\n:help - shows this message\nSEQUENT - tries to prove the sequent"

printProofs :: Sequent -> Env -> IO ()
printProofs s env = do
  ps <- return $ (evalState (toDecorated s >>= \ds -> proofs ds) startState)
  pproofs env ps

printProofsWithConstants :: ([(LambdaTerm,Formula)],Formula) -> Env -> IO ()
printProofsWithConstants s env = do
  ps <- return $ (evalState (toDecoratedWithConstants s >>= \(ds,m) -> proofs ds >>= \p -> return $ replaceWithConstants p m) startState)
  pproofs env ps

printReading :: BinTree DecoratedSequent -> IO ()
printReading t = putStrLn repr where
    repr = hyps ++ " => " ++ concl
    hyps = concat $ intersperse ", " $ map aux (fst s)
    concl = aux (snd s)
    s = getVal t
    aux df = lambda2text (term df) ++ " : " ++ formula2text (formula df)

-- does the actual printing
pproofs :: Env -> [BinTree DecoratedSequent] -> IO ()
pproofs env ps = do
  ps <- return $ map sanitizeVars ps
  ps <- case showAll env of 
          False -> return $ nubBy (\x y -> equivalentDecoratedSequent (getVal x) (getVal y)) ps
          True -> return ps
  case ps of
    [] -> putStrLn "Not a theorem"
    _ -> do
      case cmd env of
        Nothing -> mapM_ printReading ps
        Just cmd -> do
                     body <- return $ concat $ map (\x -> "\\begin{center}" ++ proof2tex x ++ "\\DisplayProof\\end{center}\n") ps
                     doc <- return $ "\\documentclass{article}" ++ texheader ++ "\\begin{document}" ++ body ++ "\\end{document}"
                     writeFile (tex_file env) doc
                     system $ cmd ++ " -output-directory=" ++ (temp_dir env) ++ " " ++ (tex_file env) ++ " > /dev/null 2>&1"
                     system $ "open " ++ (pdf_file env)
                     return ()

printState :: S -> IO ()
printState s = do
  putStrLn $ "Counter: " ++ show (counter s)
  putStr $ "Variables bindings:\n" ++ concatMap (\(x,y) -> " " ++ show x ++ " -> " ++ show y ++ "\n") (Map.toList (vars s))

printStates :: [S] -> IO ()
printStates = mapM_ printState

simpleprintProofs :: Sequent -> FilePath -> IO ()
simpleprintProofs s fp = do
  ps <- return $ (evalState (toDecorated s >>= \ds -> proofs ds) startState)
  ps <- return $ nubBy (\x y -> equivalentDecoratedSequent (getVal x) (getVal y)) ps
  body <- return $ concat $ map (\x -> "\\begin{center}" ++ simpleproof2tex x ++ "\\DisplayProof\\end{center}\n") ps
  doc <- return $ "\\documentclass{article}" ++ texheader ++ "\\begin{document}" ++ body ++ "\\end{document}"
  writeFile fp doc