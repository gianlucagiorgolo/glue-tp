{-# LANGUAGE DoAndIfThenElse #-}

module Parser where

import Text.ParserCombinators.ReadP
import DataTypes
import Data.Char
import Data.List (isPrefixOf, find)

instance Read Formula where
    readsPrec _ = readP_to_S formulaParser

formulaParser :: ReadP Formula
formulaParser = p1 +++ p2 +++ p3 where
    p1 = atom `comb` formulaRest
    p2 = monad `comb` formulaRest
    p3 = (between (skipSpaces >> char '(' >> skipSpaces) 
                  (skipSpaces >> char ')' >> skipSpaces)
                  formulaParser) `comb` formulaRest


comb :: ReadP Formula -> ReadP (Either () (Formula,String)) -> ReadP Formula
comb p q = do
  f <- p
  x <- q
  case x of
    Left _ -> return f
    Right (g,c) -> case c of 
                     "->" -> return $ I f g (TFunctional (getType f) (getType g))
                     "*" -> return $ P f g (TPair (getType f) (getType g))
                     _ -> pfail

atom :: ReadP Formula
atom = p1 +++ p2 where
    p1 = do
      skipSpaces
      c <- satisfy isLower
      name <- munch isAlphaNum
      skipSpaces
      char '.'
      skipSpaces 
      ty <- munch1 isAlphaNum
      skipSpaces
      return $ Atom (c : name) (TAtomic ty)
    p2 = do
      skipSpaces
      c <- satisfy isUpper
      name <- munch isAlphaNum
      skipSpaces
      char '.'
      skipSpaces 
      ty <- munch1 isAlphaNum
      skipSpaces
      return $ Var (c : name) (TAtomic ty) -- clearly variables can have also non-atomic types...

monad :: ReadP Formula
monad = do
  skipSpaces
  string "<>"
  skipSpaces
  next <- look
  if "(" `isPrefixOf` next then do
                             f <- formulaParser
                             skipSpaces
                             return $ M f (TMonadic $ getType f)
  else if "<>" `isPrefixOf` next then do
                                   f <- monad
                                   skipSpaces
                                   return $ M f (TMonadic $ getType f)
  else do
    f <- atom
    skipSpaces
    return $ M f $ TMonadic $ getType f

formulaRest :: ReadP (Either () (Formula,String))
formulaRest = p +++ q where
    p = do
      skipSpaces
      many (satisfy isSpace)
      return $ Left ()
    q = do
      skipSpaces
      c <- string "->" +++ string "*"
      skipSpaces
      f <- formulaParser
      skipSpaces
      return $ Right (f,c)

termAndFormula :: ReadP (LambdaTerm,Formula)
termAndFormula = do
  skipSpaces
  c <- constant
  skipSpaces
  char ':'
  skipSpaces
  f <- formulaParser
  skipSpaces
  return $ (c,f)

constant :: ReadP LambdaTerm
constant = do
  skipSpaces
  name <- munch1 isAlphaNum
  skipSpaces
  return $ C name

sequentParser :: ReadP (Either Sequent ([(LambdaTerm,Formula)],Formula))
sequentParser = p1 +++ p2 where
    p1 = do
      hyps <- sepBy formulaParser (skipSpaces >> char ',' >> skipSpaces)
      skipSpaces
      string "=>"
      skipSpaces
      cons <- formulaParser
      skipSpaces
      return $ Left (hyps,cons)
    p2 = do
      hyps <- sepBy termAndFormula (skipSpaces >> char ',' >> skipSpaces)
      skipSpaces
      string "=>"
      skipSpaces
      cons <- formulaParser
      skipSpaces
      return $ Right (hyps,cons)

parseSequent :: String -> Either String (Either Sequent ([(LambdaTerm,Formula)],Formula))
parseSequent s = aux $ find (\(_,s) -> s=="") $ (readP_to_S sequentParser) s where
    aux Nothing = Left $ "Cannot parse sequent: " ++ s
    aux (Just (s,_)) = Right s