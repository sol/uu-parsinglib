{-# LANGUAGE NoMonomorphismRestriction, RankNTypes, FlexibleContexts #-}

import Control.Monad
import Text.ParserCombinators.UU.Parsing

type Parser a =  P (Str Char) a

expr :: Parser Int
expr = 0 <$ pSym 'x' <|> (+1) <$ pSym '(' <*> expr <* pSym ')'

expr' :: Parser Int
expr' = (+1) <$ pSym '(' <*> expr' <* pSym ')' <|> 0 <$ pSym 'x'

run :: Parser a -> String -> (a, [Error Char Char Int])
run p x = parse ((,) <$> p <*> pEnd) (listToStr x)

succeed0 = run expr ""
succeed1 = run expr "("
succeed2 = run expr "(("
fail3    = run (expr <* pSym 'y')  "(((y"

succeed0'  = run expr' ""
succeed1'  = run expr' "("
succeed2'  = run expr' "(("
succeed3'  = run expr' "((("
succeed30' = run expr' "(((((((((((((((((((((((((((((("
