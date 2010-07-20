{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction#-}

module Text.ParserCombinators.UU.Examples where
import Char
import Text.ParserCombinators.UU

type Parser a = P (Str Char) a 

-- running the parser; if complete input accepted return the result else fail with reporting unconsumed tokens
run :: Show t =>  P (Str Char) t -> String -> IO ()
run p inp = do  let r@(a, errors) =  parse ( (,) <$> p <*> pEnd) (listToStr inp)
                print ("Result: " ++ show a)
                if null errors then  return ()
                               else  print ("With errors: "++ show errors)



lift a = [a]

pa, pb, paz ::Parser [Char] 
pa = lift <$> pSym 'a'
-- | This parser recognises a single character $'a'$, and returns this value as a singleton list.

-- | 
pb = lift <$> pSym 'b'
p <++> q = (++) <$> p <*> q
pa2 =   pa <++> pa
pa3 =   pa <++> pa2

pCount p = (\ a b -> b+1) <$> p <*> pCount p <<|> pReturn 0
pExact 0 p = pReturn []
pExact n p = (:) <$> p <*> pExact (n-1) p

paz = pList (pSym ('a', 'z'))

paz' = pSym (\t -> 'a' <= t && t <= 'z', "'a'..'z'", 'k')

main :: IO ()
main = do run pa "a"
          run pa "b"
          run pa2 "bbab"
          run pa "ba"
          run pa "aa"
          run (do  {l <- pCount pa; pExact l pb}) "aaacabbb"
          run (amb ( (++) <$> pa2 <*> pa3 <|> (++) <$> pa3 <*> pa2))  "aaabaa"
          run paz "ab1z7"
          run paz' "m"
          run paz' ""
          run (pa <|> pb <?> "just a message") "c"
          run parseBoth "(123;456;789)"
          run munch "a^^&&**^^&b"

munch = (,,) <$> pa <*> pMunch ( `elem` "^&*") <*> pb

-- bracketing expressions
pParens p =  pSym '(' *> p <* pSym ')'
pBracks p =  pSym '[' *> p <* pSym ']'
pCurlys p =  pSym '{' *> p <* pSym '}'

-- parsing numbers
pDigit = pSym ('0', '9')
pDigitAsInt = digit2Int <$> pDigit 
pNatural = foldl (\a b -> a * 10 + b ) 0 <$> pList1 pDigitAsInt
digit2Int a =  ord a - ord '0'

-- parsing letters and identifiers
pLower  = pSym ('a','z')
pUpper  = pSym ('A','Z')
pLetter = pUpper <|> pLower
pVarId  = (:) <$> pLower <*> pList pIdChar
pConId  = (:) <$> pUpper <*> pList pIdChar
pIdChar = pLower <|> pUpper <|> pDigit <|> pAnySym "='"

pAnyToken = pAny pToken

-- parsing two alternatives and returning both rsults
pAscii = pSym ('\000', '\254')
pIntList       ::Parser [Int] 
pIntList       =  pParens ((pSym ';') `pListSep` (read <$> pList (pSym ('0', '9'))))
parseIntString :: Parser String
parseIntString = pList (pAscii)

parseBoth = pPair pIntList parseIntString

pPair p q =  amb (Left <$> p <|> Right <$> q)




-- Testing
pTest_MS :: P (Str Char) Char
pTest_MS = id <$ pSym 'u' <*> pSym '2'

pOp (c, op) = op <$ pSym c

sepBy p op = pChainl op p
expr    = term   `sepBy` (pOp ('+', (+)) <|> pOp ('-', (-)))
term    = factor `sepBy` pOp ('*' , (*))
factor  = pNatural <|> pSym '(' *> expr <* pSym ')'

wfp :: Parser Int
wfp = 0 <$ pSym 'x' <|> (+1) <$ pSym '(' <*> wfp <* pSym ')'

expr' :: Parser Int
expr' = (+1) <$ pSym '(' <*> expr' <* pSym ')' <|> 0 <$ pSym 'x'
{-

succeed0 = run expr ""
succeed1 = run expr "("
succeed2 = run expr "(("
fail3    = run (expr <* pSym 'y')  "(((y"

succeed0'  = run expr' ""
succeed1'  = run expr' "("
succeed2'  = run expr' "(("
succeed3'  = run expr' "((("
succeed30' = run expr' "(((((((((((((((((((((((((((((("
-}

ident ::  Parser String
ident = ((:) <$> pSym ('a','z') <*> pMunch (\x -> 'a' <= x && x <= 'z') `micro` 2) <* spaces
idents = pList1 ident

pTok keyw = pToken keyw `micro` 1 <* spaces

spaces :: Parser String
spaces = pMunch (==' ')

failing = pList_ng ident <* pToken "if"

takes_second_alt =   pList ident 
                <|> (\ c t e -> ["IfThenElse"] ++  c   ++  t  ++  e) 
                    <$ pTok "if"   <*> pList_ng ident 
                    <* pTok "then" <*> pList_ng ident
                    <* pTok "else" <*> pList_ng ident  


test = run failing "foo if"
test2 = run takes_second_alt "if a then b else c"
test3 = run takes_second_alt "ifx a then b else c"

