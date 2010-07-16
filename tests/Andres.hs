{-# LANGUAGE NoMonomorphismRestriction, RankNTypes, FlexibleContexts #-}

import Control.Monad
import Text.ParserCombinators.UU.Parsing

type Parser a = forall st. (Provides st Char Char, Provides st (Char, Char) Char) => P st a

instance MonadPlus (P st) where
 mzero = pFail
 mplus = (<|>)

keywords :: [String]
keywords = ["let", "in", "if", "then", "else"]

{-
ident :: Parser String
ident =
 do
   ys <- pList1 (pSym ('a','z'))
   guard (not (ys `elem` keywords))
   spaces
   return ys
-}

ident ::  Parser String
ident = (pList1 (pSym ('a','z')) `micro` 1) <* spaces
idents = pList1 ident

pTok keyw = pToken keyw <* spaces

spaces :: Parser String
spaces = pList (pSym ' ')

run :: Parser a -> String -> (a, [Error Char Char Int])
run p x = parse ((,) <$> p <*> pEnd) (listToStr x)

failing = pList_ng ident <* pToken "if"

takes_second_alt =   pList ident 
                <|> (\ c t e -> ["IfThenElse"] ++  c   ++  t  ++  e) <$ pTok "if" <*> pList_ng ident <* pTok "then" <*> pList_ng ident <* pTok "else" <*> pList_ng ident  


test = run failing "foo if"
test2 = run takes_second_alt "if a then b else c"
