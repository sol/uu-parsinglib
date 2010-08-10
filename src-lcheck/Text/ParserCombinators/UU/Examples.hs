{-# OPTIONS_HADDOCK  ignore-exports #-}
{-# LANGUAGE  FlexibleInstances,
              TypeSynonymInstances,
              MultiParamTypeClasses,
              CPP  #-}

-- | This module contains a lot of examples of the typical use of our parser combinator library. 
--   We strongly encourage you to take a look at the source code
--   At the end you find a @`main`@ function which demonstrates the main characteristics. 
--   Only the @`run`@ function is exported since it may come in handy elsewhere.

module Text.ParserCombinators.UU.Examples (run, demo) where
import Char
import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Derived
-- import Control.Monad

-- | The fuction @`run`@ runs the parser and shows both the result, and the correcting steps which were taken during the parsing process.
run :: Show t =>  Parser t -> String -> IO ()
run  (p@(P _ _ _ _ (_,lr))) inp 
          = if lr then putStrLn "-- > The grammar is left recursive (maybe deep inside)!" else
            do  let r@(a, errors) =  parse ( (,) <$> p <*> pEnd) (listToStr inp (0,0))
                putStrLn "--"
                putStrLn ("-- > Result: " ++ show a)
                if null errors then  return ()
                               else  do putStr ("-- > Correcting steps: \n")
                                        show_errors errors
                putStrLn "-- "


-- | Our first two parsers are simple; one recognises a single 'a' character and the other one a single 'b'. Since we will use them later we 
--   convert the recognsied character into String so they can be easily combined.
pa  ::Parser String 
pa  = lift <$> pSym 'a'
pb  :: Parser String 
pb = lift <$> pSym 'b'
pc  :: Parser String 
pc = lift <$> pSym 'c'
lift a = [a]

-- | We can now run the parser @`pa`@ on input \"a\", which succeeds:
--
-- > run pa "a" 
--
-- > Result: "a"
--

test1 = run pa "a"

-- | If we   run the parser @`pa`@ on the empty input \"\", the expected symbol in inserted, 
--   that the position where it was inserted is reported, and
--   we get information about what was expected at that position: 
--
-- > run pa ""
--
-- > Result: "a"
-- > Correcting steps: 
-- >    Inserted 'a' at position 0 expecting 'a'
-- 

test2 = run pa ""

-- | Now let's see what happens if we encounter an unexpected symbol, as in:
--
-- > run pa "b"
--
-- > Result: "a"
-- > Correcting steps: 
-- >    Deleted  'b' at position 0 expecting 'a'
-- >    Inserted 'a' at position 1 expecting 'a'
-- 

test3 = run pa "b"

-- | The combinator @`<++>`@ applies two parsers sequentially to the input and concatenates their results:
--
-- > run (pa <++> pa) "aa"@:
--
-- > Result: "aa"
-- 


(<++>) :: Parser String -> Parser String -> Parser String
p <++> q = (++) <$> p <*> q
pa2 =   pa <++> pa
pa3 =   pa <++> pa2

test4 = run pa2 "aa"

-- | The function @`pSym`@ is overloaded. The type of its argument determines how to interpret the argument. Thus far we have seen single characters, 
--   but we may pass ranges as well as argument: 
--
-- > run (pList (pSym ('a','z'))) "doaitse"
--
--
-- > Result: "doaitse"
-- 

test5 =  run  (pList (pSym ('a','z'))) "doaitse"
paz = pList (pSym ('a', 'z'))

-- | An even more general instance of @`pSym`@ takes a triple as argument: a predicate, 
--   a string indicating what is expected, 
--   and the value to insert if nothing can be recognised: 
-- 
-- > run (pSym (\t -> 'a' <= t && t <= 'z', "'a'..'z'", 'k')) "1"
--
--
-- > Result: 'k'
-- > Correcting steps: 
-- >    Deleted  '1' at position 0 expecting 'a'..'z'
-- >    Inserted 'k' at position 1 expecting 'a'..'z'
-- 

test6 :: IO ()
test6 = run  paz' "1"
paz' = pSym (\t -> 'a' <= t && t <= 'z', "'a'..'z'", 'k')

-- | The parser `pCount` recognises a sequence of elements, throws away the results of the recognition process (@ \<$ @), and just returns the number of returned elements.
--   The choice combinator @\<\<|>@ indicates that preference is to be given to the left alternative if it can make progress. This enables us to specify greedy strategies:
--
-- > run (pCount pa) "aaaaa"
--
-- > Result: 5
-- 

test7 :: IO ()
test7 = run (pCount pa) "aaaaa"
pCount p = (+1) <$ p <*> pCount p <<|> pReturn 0

-- | The parsers are instance of the class Monad and hence we can use the 
--   result of a previous parser to construct a following one:  
--
-- > run (do  {l <- pCount pa; pExact l pb}) "aaacabbb"
--
-- > Result: ["b","b","b","b"]
-- > Correcting steps: 
-- >    Deleted  'c' at position 3 expecting one of ['a', 'b']
-- >    Inserted 'b' at position 8 expecting 'b'
-- 

test8 :: IO ()
test8 = run (do  {l <- pCount pa; pExact l pb}) "aaacabbb"
pExact 0 p = pReturn []
pExact n p = (:) <$> p <*> pExact (n-1) p


-- | The function @`amb`@ converts an ambigous parser into one which returns all possible parses: 
--
-- > run (amb ( (++) <$> pa2 <*> pa3 <|> (++) <$> pa3 <*> pa2))  "aaaaa"
--
-- > Result: ["aaaaa","aaaaa"]
-- 
test9 :: IO ()
test9 = run (amb ( (++) <$> pa2 <*> pa3 <|> (++) <$> pa3 <*> pa2))  "aaaaa"

-- | The applicative style makes it very easy to merge recognsition and computing a result. 
--   As an example we parse a sequence of nested well formed parentheses pairs and
--   compute the maximum nesting depth with @`wfp`@: 
--
-- > run wfp "((()))()(())" 
--
-- > Result: 3
-- 

wfp :: Parser Int
wfp =  max <$> pParens ((+1) <$> wfp) <*> wfp `opt` 0
test10 = run wfp "((()))()(())"

-- | It is very easy to recognise infix expressions with any number of priorities and operators:
--
-- > operators       = [[('+', (+)), ('-', (-))],  [('*' , (*))], [('^', (^))]]
-- > same_prio  ops  = msum [ op <$ pSym c | (c, op) <- ops]
-- > expr            = foldr pChainl ( pNatural <|> pParens expr) (map same_prio operators) -- 
--
-- which we can call:  
--
-- > run expr "15-3*5+2^5"
--
-- > Result: 32
--
-- Note that also here correction takes place: 
--
-- > run expr "2 + + 3 5"
--
-- > Result: 37
-- > Correcting steps: 
-- >    Deleted  ' ' at position 1 expecting one of ['0'..'9', '^', '*', '-', '+']
-- >    Deleted  ' ' at position 3 expecting one of ['(', '0'..'9']
-- >    Inserted '0' at position 4 expecting '0'..'9'
-- >    Deleted  ' ' at position 5 expecting one of ['(', '0'..'9']
-- >    Deleted  ' ' at position 7 expecting one of ['0'..'9', '^', '*', '-', '+']
-- 


test11 = run expr "15-3*5"
expr :: Parser Int
operators       = [[('+', (+)), ('-', (-))],  [('*' , (*))], [('^', (^))]]
same_prio  ops  = foldr (<|>) empty [ op <$ pSym c | (c, op) <- ops]
expr            = foldr pChainl ( pNatural <|> pParens expr) (map same_prio operators) 


-- | A common case where ambiguity arises is when we e.g. want to recognise identifiers, 
--   but only those which are not keywords. 
--   The combinator `micro` inserts steps with a specfied cost in the result 
--   of the parser which can be used to disambiguate:
--
-- > 
-- > ident ::  Parser String
-- > ident = ((:) <$> pSym ('a','z') <*> pMunch (\x -> 'a' <= x && x <= 'z') `micro` 2) <* spaces
-- > idents = pList1 ident
-- > pKey keyw = pToken keyw `micro` 1 <* spaces
-- > spaces :: Parser String
-- > spaces = pMunch (==' ')
-- > takes_second_alt =   pList ident 
-- >                \<|> (\ c t e -> ["IfThenElse"] ++  c   ++  t  ++  e) 
-- >                    \<$ pKey "if"   <*> pList_ng ident 
-- >                    \<* pKey "then" <*> pList_ng ident
-- >                    \<* pKey "else" <*> pList_ng ident  
--
--  A keyword is followed by a small cost @1@, which makes sure that 
--  identifiers which have a keyword as a prefix win over the keyword. Identifiers are however
--   followed by a cost @2@, with as result that in this case the keyword wins. 
--   Note that a limitation of this approach is that keywords are only recognised as such when expected!
-- 
-- > test13 = run takes_second_alt "if a then if else c"
-- > test14 = run takes_second_alt "ifx a then if else c"
-- 
-- with results for @test13@ and @test14@:
--
-- > Result: ["IfThenElse","a","if","c"]
-- > Result: ["ifx","a","then","if", "else","c"]
-- 

-- | A mistake which is made quite often is to construct  a parser which can recognise a sequence of elements using one of the 
--  derived combinators (say @`pList`@), but where the argument parser can recognise the empty string. 
--  The derived combinators check whether this is the case and terminate the parsing process with an error message:
--
-- > run (pList spaces) ""
-- > Result: *** Exception: The combinator pList
-- >  requires that it's argument cannot recognise the empty string
--
-- > run (pMaybe spaces) " "
-- > Result: *** Exception: The combinator pMaybe
-- > requires that it's argument cannot recognise the empty string


test16 :: IO ()
test16 = run (pList spaces) "  "

ident = ((:) <$> pSym ('a','z') <*> pMunch (\x -> 'a' <= x && x <= 'z') `micro` 2) <* spaces
idents = pList1 ident

pKey keyw = pToken keyw `micro` 1 <* spaces
spaces :: Parser String
spaces = pMunch (`elem` " \n")
 
takes_second_alt =   pList ident 
              <|> (\ c t e -> ["IfThenElse"] ++  c   ++  t  ++  e) 
                  <$ pKey "if"   <*> pList_ng ident 
                  <* pKey "then" <*> pList_ng ident
                  <* pKey "else" <*> pList_ng ident  
test13 = run takes_second_alt "if a then if else c"
test14 = run takes_second_alt "ifx a then if else c"


-- | The function
--
-- > munch =  pMunch ( `elem` "^=*") 
--
--  returns  the longest prefix of the input obeying the predicate:
--
-- > run munch "==^^**rest" 
--
-- > Result: "==^^**"
-- > Correcting steps: 
-- >    The token 'r' was not consumed by the parsing process.
-- >    The token 'e' was not consumed by the parsing process.
-- >    The token 's' was not consumed by the parsing process.
-- >    The token 't' was not consumed by the parsing process.
-- 

munch :: Parser String
munch =  pa *> pMunch ( `elem` "^=*") <* pb

-- | The effect of the combinator `manytill` from Parsec can be achieved:
--
-- > run simpleComment "<!--123$$-->abc"
-- > Result: "123$$"
-- > Correcting steps: 
-- >    The token 'a' was not consumed by the parsing process.
-- >    The token 'b' was not consumed by the parsing process.
-- >    The token 'c' was not consumed by the parsing process.
-- 

pManyTill :: P st a -> P st b -> P st [a]
pManyTill p end = [] <$ end 
                  <<|> 
                  (:) <$> p <*> pManyTill p end
simpleComment   =  string "<!--" 
                   *> 
                   pManyTill pAscii  (string "-->")


string :: String -> Parser String
string = pToken-- bracketing expressions
pParens p =  pSym '(' *> p <* pSym ')'
pBracks p =  pSym '[' *> p <* pSym ']'
pCurlys p =  pSym '{' *> p <* pSym '}'

-- parsing numbers

pDigitAsInt = digit2Int <$> pDigit 
pNatural = foldl (\a b -> a * 10 + b ) 0 <$> pList1 pDigitAsInt
digit2Int a =  ord a - ord '0'

-- parsing letters and identifiers
pAscii = pSym (chr 0, chr 255)
pDigit = pSym ('0', '9')
pLower  = pSym ('a','z')
pUpper  = pSym ('A','Z')
pLetter = pUpper <|> pLower
pVarId  = (:) <$> pLower <*> pList pIdChar
pConId  = (:) <$> pUpper <*> pList pIdChar
pIdChar = pLower <|> pUpper <|> pDigit <|> pAnySym "='"

pAnyToken :: [String] -> Parser String
pAnyToken = pAny pToken

-- parsing two alternatives and returning both rsults
pIntList :: Parser [Int]
pIntList       =  pParens ((pSym ';') `pListSep` (read <$> pList1 (pSym ('0', '9'))))
parseIntString :: Parser [String]
parseIntString =  pParens ((pSym ';') `pListSep` (         pList1 (pSym ('0', '9'))))

#define DEMO(p,i) demo "p" i p

justamessage = "justamessage"

main :: IO ()
main = do DEMO (pa,  "a")
          DEMO (pa,  "b")
          DEMO (((++) <$> pa <*> pa), "bbab")
          DEMO (pa,  "ba")
          DEMO (pa,  "aa")
          DEMO ((let prl = (++) <$> prl <*> pa in prl), "a")
          DEMO ((let prl = (++) <$> prl <*> pa in (++) <$> pa <*> prl), "a")
          DEMO ((do  {l <- pCount pa; pExact l pb}),   "aaacabbbb")
          DEMO ((amb ( (++) <$> pa2 <*> pa3 <|> (++) <$> pa3 <*> pa2)),    "aaaaa")
          DEMO (paz, "ab1z7")
          DEMO ((pa <|> pb <?> justamessage),   "c")
          DEMO ((amb (pEither  parseIntString  pIntList)),   "(123;456;789)")
          DEMO (munch,   "a^=^**^^b")
          demo_merge

-- | For documentation of @`pMerge`@ and @`<||>`@ see the module "Text.ParserCombinators.UU.Merge". Here we just give a @deno_merge@, which
--   should speak for itself. Make sure your parsers are not getting ambiguous. This soon gets very expensive.
--
demo_merge :: IO ()
demo_merge = do DEMO (((,)   `pMerge` (pBetween 2 3 pa <||> pBetween 1 2 pb))                       , "abba")  
                DEMO (((,)   `pMerge` (pBetween 2 3 pa <||> pBetween 1 2 pb))                       , "bba")
                -- run ((,)   `pMerge` (pBetween 2 3 pa <||> pBetween 1 2 pa))                      , "aaa") -- is ambiguous, and thus incorrect
                DEMO ((amb ((,)   `pMerge` (pBetween 2 3 pa <||> pBetween 1 2 pa)))                 , "aaa")
                putStr "The 'a' at the right hand side can b any of the three 'a'-s in the input\n"
                DEMO (((,)   `pMerge` (pAtLeast 3 pa <||> pAtMost 3 pb))                            , "aabbbb")  
                DEMO (((,)   `pMerge` (pSome pa <||> pMany pb))                                     , "abba")       
                DEMO (((,)   `pMerge` (pSome pa <||> pMany pb))                                     , "abba")           
                DEMO (((,)   `pMerge` (pSome pa <||> pMany pb))                                     , "")         
                DEMO (((,)   `pMerge` (pMany pb <||> pSome pc))                                     , "bcbc")          
                DEMO (((,)   `pMerge` (pSome pb <||> pMany pc))                                     , "bcbc")
                DEMO (((,,,) `pMerge` (pSome pa <||> pMany pb <||> pOne pc <||>  pNatural `pOpt` 5)), "babc45" )
                DEMO (((,)   `pMerge` (pMany (pa <|> pb) <||> pSome pNatural))                      , "1ab12aab14")
                DEMO (( (,)  `pMerge` ( ((++) `pSem` (pMany pa <||> pMany pb)) <||> pOne pc))       , "abcaaab")
                DEMO (((((,), pc) `pMergeSep` (pMany pa <||> pMany pb)))                              , "acbcacb")


demo :: Show r => String -> String -> Parser r -> IO ()
demo str  input p= do putStr ("\n===========================================\n>>   run " ++ str ++ "  " ++ show input ++ "\n")
                      run p input


