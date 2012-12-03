{-# LANGUAGE NoMonomorphismRestriction,
             RankNTypes,
             FlexibleContexts,
             CPP  #-}
#define DEMO(p,i) demo "p" i p
#define DEMOG(p,i) demo "p" i (mkParserM (p))
module Text.ParserCombinators.UU.Demo.MergeAndPermute where

import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.MergeAndPermute
import Text.ParserCombinators.UU.BasicInstances hiding (Parser)
import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.Demo.Examples hiding (show_demos)
import qualified Data.ListLike as LL 

type Grammar a =  Gram (P (Str Char String  LineColPos)) a

-- | By running the function `show_demos` you will get a demonstration of the merging parsers.
--
-- >>>   run ((,,) <$> two pA <||> three pB <||> pBetween 2 4 pC )  "cababbcccc"
--  Result: ("aa",("b","b","b"),["c","c","c","c"])
--  Correcting steps: 
--    The token 'c' was not consumed by the parsing process.
-- 
-- >>>   run (amb (mkParserM ((,) <$> pmMany ((,) <$>  pA <*> pC) <||> pmMany pB)))    "aabbcaabbccc"
--  Result: [([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),
--           ([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),
--           ([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),
--           ([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),
--           ([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),
--           ([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"]),([("a","c"),("a","c"),("a","c"),("a","c")],["b","b","b","b"])]
-- 
-- >>>   run (pmMany(pABC))                                                            "a2a1b1b2c2a3b3c1c3"
--  Result: ["2a","1a","3a"]
-- 
-- >>>   run ((,)    <$> pBetween 2 3 pA <||> pBetween 1 2 pB)                         "abba"
--  Result: (["a","a"],["b","b"])
-- 
-- >>>   run ((,)    <$> pBetween 2 3 pA <||> pBetween 1 2 pB)                         "bba"
--  Result: (["a","a"],["b","b"])
--  Correcting steps: 
--    Inserted  'a' at position LineColPos 0 3 3 expecting 'a'
-- 
-- >>>   run (amb (mkParserM( ((,)    <$> pBetween 2 3 pA <||> pBetween 1 2 pA))))      "aaa"
--  Result: [(["a","a"],["a"]),(["a","a"],["a"]),(["a","a"],["a"])]
-- 
-- The 'a' at the right hand side can b any of the three 'a'-s in the input:
--
-- >>>   run ((,)    <$> pAtLeast 3 pA <||> pAtMost 3 pB)                              "ababbb"
--  Result: (["a","a","a"],["b","b","b"])
--  Correcting steps: 
--    Deleted   'b' at position LineColPos 0 5 5 expecting 'a'
--    Inserted  'a' at position LineColPos 0 6 6 expecting 'a'
-- 
-- >>>   run ((,)    <$> pSome pA <||> pMany pB)                                       "abba"
--  Result: (["a","a"],["b","b"])
-- 
-- >>>   run ((,)    <$> pSome pA <||> pMany pB)                                       "abba"
--  Result: (["a","a"],["b","b"])
-- 
-- >>>   run ((,)    <$> pSome pA <||> pMany pB)                                       ""
--  Result: (["a"],[])
--  Correcting steps: 
--    Inserted  'a' at position LineColPos 0 0 0 expecting one of ['a', 'b']
-- 
-- >>>   run ((,)    <$> pMany pB <||> pSome pC)                                       "bcbc"
--  Result: (["b","b"],["c","c"])
-- 
-- >>>   run ((,)    <$> pSome pB <||> pMany pC)                                       "bcbc"
--  Result: (["b","b"],["c","c"])
-- 
-- >>>   run ((,,,)   <$> pSome pA <||> pMany pB <||> pC <||> (pNat `opt` 5) )         "bcab45"
--  Result: (["a"],["b","b"],"c",45)
-- 
-- >>>   run ((,)    <$> pMany (pA <|> pB) <||> pSome  pNat)                           "1ab12aab14"
--  Result: (["a","b","a","a","b"],[1,12,14])
-- 
-- >>>   run ( (,)   <$> ((++) <$> pMany pA <||> pMany pB) <||> pC)                    "abcaaab"
--  Result: (["a","a","a","a","b","b"],"c")
-- 
-- >>>   run (pc `mkParserS` ((,) <$> pMany pA <||> pMany pB))                         "acbcacb"
--  Result: (["a","a"],["b","b"])
-- 

show_demos :: IO ()
show_demos = do DEMOG (((,,) <$> two pA <||> three pB <||> pBetween 2 4 pC ), "cababbcccc")
                DEMO  ((amb (mkParserM ((,) <$> pmMany ((,) <$>  pA <*> pC) <||> pmMany pB)))  , "aabbcaabbccc")
                DEMOG ((pmMany(pABC))                                                          , "a2a1b1b2c2a3b3c1c3")
                DEMOG (((,)    <$> pBetween 2 3 pA <||> pBetween 1 2 pB)                       , "abba")  
                DEMOG (((,)    <$> pBetween 2 3 pA <||> pBetween 1 2 pB)                       , "bba")
                DEMO ((amb (mkParserM( ((,)    <$> pBetween 2 3 pA <||> pBetween 1 2 pA))))    , "aaa")
                putStr "-- The 'a' at the right hand side can b any of the three 'a'-s in the input\n"
                DEMOG (((,)    <$> pAtLeast 3 pA <||> pAtMost 3 pB)                            , "ababbb")  
                DEMOG (((,)    <$> pSome pA <||> pMany pB)                                     , "abba")       
                DEMOG (((,)    <$> pSome pA <||> pMany pB)                                     , "abba")           
                DEMOG (((,)    <$> pSome pA <||> pMany pB)                                     , "")         
                DEMOG (((,)    <$> pMany pB <||> pSome pC)                                     , "bcbc")          
                DEMOG (((,)    <$> pSome pB <||> pMany pC)                                     , "bcbc")
                DEMOG (((,,,)   <$> pSome pA <||> pMany pB <||> pC <||> (pNat `opt` 5) )       , "bcab45" )
                DEMOG (((,)    <$> pMany (pA <|> pB) <||> pSome  pNat)                         , "1ab12aab14")
                DEMOG (( (,)   <$> ((++) <$> pMany pA <||> pMany pB) <||> pC)                  , "abcaaab")
                DEMO  ((pc `mkParserS` ((,) <$> pMany pA <||> pMany pB))                       , "acbcacb")

pA, pB, pC:: Grammar String
pA   = mkGram pa
pB   = mkGram pb
pC   = mkGram (lift <$> pSym 'c')


pNat ::  Grammar Int
pNat = mkGram pNatural


pDigit' = mkGram pDigit

-- | `two` recognises two instance of p as part of the input sequence
two :: Applicative f => f [a] -> f [a]
two p = (++) <$> p <*> p
-- | `three` recognises two instance of p as part of the input sequence and concatenates the results
three :: Applicative f => f a-> f (a,a,a)
three p = (,,) <$> p <*> p <*> p

-- | `pABC` minimcs a series of events (here an @a@, a @b@ and a @c@), which belong to the same transaction. 
--   The transaction is identified by a digit: hence a full transaction is a string like \"a5b5c5\". 
--   The third element in the body of `show_demos` below shows how the different transactions can be recovered from  
--   a log-file which contains all events generated by a collection of concurrently running transactions.
{-
pABC :: Grammar Char
pABC = mkGram (pa *> pDigit ) >>= (\ d ->  mkGram (pb *> pSym d) *> mkGram (pc *> pSym d))
-}
pABC =    do  d <- mkGram (pa *> pDigit ) 
              mkGram (pb *> pSym d) *> mkGram (pc *> pSym d)

pABC' :: Grammar String	
pABC' = (\ a d -> d:a) <$> pA <*> (pDigit' >>= \d ->  pB *> mkGram (pSym d) *> pC *> mkGram (pSym d))




