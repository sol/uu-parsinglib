{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.ParserCombinators.UU.Demo.MergeAndPermute where

import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.Demo.Examples
import Text.ParserCombinators.UU.MergeAndPermute

-- pa' :: Gram (P state) token
pa' = mkGram pa
pb' = mkGram pb
pc' = mkGram (lift <$> pSym 'c')
two p = (++) <$> p <*> p
pDigit' = mkGram (pSym (\t -> '0' <= t && t <= '9', "'0'..'9'", '5'))

three p = (,,) <$> p <*> p <*> p

test = run (mkParserM ((,,) <$> two pa' <||> three pb' <||> pBetween 2 4 pc' )) "cababbcccc"

pmMany p = let pm = (:) <$> p <<||> pm <|> pure [] in pm

mtest2 = run (amb(mkParserM ((,) <$> pmMany ((,) <$>  pa' <*> pc') <||> pmMany pb'))) "aabbcaabbccc"

pABC = (\ a d -> d:a) <$> pa' <*> (pDigit' >>= \d ->  pb' *> mkGram (pSym d) *> pc' *> mkGram (pSym d))

mtest3 = run (mkParserM (pmMany(pABC))) "a1a2b1b2c2a3b3c1c3"


pExactly :: (IsParser f) => Int -> f a -> f [a]
pExactly n p | n == 0 = pure []
             | n >  0 = (:) <$> p <*> pExactly (n-1) p

-- pBetween :: (IsParser f) => Int -> Int -> f a -> f [a]
pBetween m n p |  n < 0 || m <0 =  error "negative arguments to pBwteeen"
               |  m > n         =  empty
               |  otherwise     =  (++) <$> pExactly m p <*> pAtMost (n-m) p

pAtLeast ::  (IsParser f) => Int -> f a -> f [a]
pAtLeast n p  = (++) <$> pExactly n p <*> pList p

pAtMost ::  (IsParser f) => Int -> f a -> f [a]
pAtMost n p | n > 0  = (:) <$> p <*> pAtMost (n-1) p `opt`  []
            | n == 0 = pure []

pSome :: (IsParser f) => f a -> f [a]
pSome p = (:) <$> p <*> pList p

pMany p = pList p

pOne p = p
pSem = ($)

{-
-- | For documentation of @`pMerge`@ and @`<||>`@ see the module "Text.ParserCombinators.UU.Merge". Here we just give a @deno_merge@, which
--   should speak for itself. Make sure your parsers are not getting ambiguous. This soon gets very expensive.
--
demo_merge :: IO ()
demo_merge = do DEMO (((,)    <$> pBetween 2 3 pa' <||> pBetween 1 2 pb')                       , "abba")  
                DEMO (((,)    <$> pBetween 2 3 pa' <||> pBetween 1 2 pb')                       , "bba")
                -- run ((,)   <$>` (pBetween 2 3 pa' <||> pBetween 1 2 pa'))                      , "aaa") -- is ambiguous, and thus incorrect
 --               DEMO ((amb ((,)    <$> pBetween 2 3 pa' <||> pBetween 1 2 pa'))                 , "aaa")
                putStr "The 'a' at the right hand side can b any of the three 'a'-s in the input\n"
                DEMO (((,)    <$> pAtLeast 3 pa' <||> pAtMost 3 pb')                            , "aabbbb")  
                DEMO (((,)    <$> pSome pa' <||> pMany pb')                                     , "abba")       
                DEMO (((,)    <$> pSome pa' <||> pMany pb')                                     , "abba")           
                DEMO (((,)    <$> pSome pa' <||> pMany pb')                                     , "")         
                DEMO (((,)    <$> pMany pb' <||> pSome pc')                                     , "bcbc")          
                DEMO (((,)    <$> pSome pb' <||> pMany pc')                                     , "bcbc")
                DEMO (((,,,)  <$> pSome pa' <||> pMany pb' <||> pOne pc' <||>  (pNatural `opt` 5)), "babc45" )
                DEMO (((,)    <$> pMany (pa' <|> pb') <||> pSome pNatural)                      , "1ab12aab14")
                DEMO (( (,)   <$> ((++) `pSem` (pMany pa' <||> pMany pb')) <||> pOne pc')       , "abcaaab")
--                DEMO (((((,), pc) `pMergeSep` (pMany pa <||> pMany pb)))                              , "acbcacb")
-}

