{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction #-}

-- | This module contains a large variety of combinators for list-lile structures. the extension @_ng@ indiactes that 
--   that variant is the non-greedy variant.
--   See the "Text.ParserCombinators.UU.Examples" module for some exmaples of their use.

module Text.ParserCombinators.UU.Derived where
import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.Interface

import Control.Monad

-- * Some common combinators for oft occurring constructs

-- | @`pReturn`@ is defined for upwards comptaibility
--
pReturn :: Appplicative p => a -> p str a
pReturn  = pure

-- | @`pFail`@ is defined for upwards comptaibility, and is the unit for @<|>@
--
pFail :: Alternative p => p str a
pFail    = empty


infixl 2 `opt`

-- | Optionally recognize parser 'p'.
-- 
-- If 'p' can be recognized, the return value of 'p' is used. Otherwise,
-- the value 'v' is used. Note that opt is greedy, if you do not want
-- this use @... <|> pure v@  instead. Furthermore, 'p' should not
-- recognise the empty string, since this would make your parser ambiguous!!
opt ::  (IsParser p, IsCheckable p)  => p st a -> a -> p st a
p `opt` v       = must_be_non_empty "opt" p (p <<|> pure v) 

-- | @pMaybe@ greedily recognises its argument. If not @Nothing@ is returned.
pMaybe ::  (IsParser p, IsCheckable p) => p st a -> p st (Maybe a)
pMaybe p = must_be_non_empty "pMaybe" p (Just <$> p `opt` Nothing) 

-- | @pEither@ recognises either one of its arguments.
pEither :: (IsParser p, IsCheckable p) => p str a -> p str b -> p str (Either a b)
pEither p q = Left <$> p <|> Right <$> q
                                                
-- | @<$$>@ is the version of @<$>@ which maps on its second argument 
(<$$>)    ::  (a -> b -> c) -> P st b -> P st (a -> c)
f <$$> p  =  flip f <$> p

-- | @<??>@ parses an optional postfix element and applies its result to its left hand result
infixl 4  <??>
(<??>) :: (IsParser p, IsCheckable p) => p st a -> p st (a -> a) -> p st a
p <??> q        = must_be_non_empty "<??>" q (p <**> (q `opt` id)) -- the <**> comes form the "Control.Applicative" module


-- | @`pPacked`@ surrounds its third parser with the first and the second one, while only keeping only the middle result
pPacked :: P st b1 -> P st b2 -> P st a -> P st a
pPacked l r x   =   l *>  x <*   r

-- * The collection of iterating combinators, all in a greedy (default) and a non-greedy variant

pFoldr    :: (IsParser p, IsCheckable p) => (a -> a1 -> a1, a1) -> p st a -> p st a1
pFoldr         alg@(op,e)     p =  must_be_non_empty "pFoldr" p pfm
                                   where pfm = (op <$> p <*> pfm) `opt` e

pFoldr_ng ::  (IsParser p, IsCheckable p) => (a -> a1 -> a1, a1) -> p st a -> p st a1
pFoldr_ng      alg@(op,e)     p =  must_be_non_empty "pFoldr_ng" p pfm 
                                   where pfm = (op <$> p <*> pfm)  <|> pure e


pFoldr1    :: (IsParser p, IsCheckable p) => (v -> b -> b, b) -> p st v -> p st b
pFoldr1        alg@(op,e)     p =  must_be_non_empty "pFoldr1"    p (op <$> p <*> pFoldr     alg p) 

pFoldr1_ng ::  (IsParser p, IsCheckable p) => (v -> b -> b, b) -> p st v -> p st b
pFoldr1_ng     alg@(op,e)     p =  must_be_non_empty "pFoldr1_ng" p (op <$> p <*> pFoldr_ng  alg p)

pFoldrSep    :: (IsParser p, IsCheckable p) => (v -> b -> b, b) -> p st a -> p st v -> p st b
pFoldrSep      alg@(op,e) sep p =  must_be_non_empties "pFoldrSep" sep   p
                                   (op <$> p <*> pFoldr    alg sepp `opt` e)
                                   where sepp = sep *> p
pFoldrSep_ng :: (IsParser p, IsCheckable p) => (v -> b -> b, b) -> p st a -> p st v -> p st b
pFoldrSep_ng   alg@(op,e) sep p =  must_be_non_empties "pFoldrSep" sep   p
                                   (op <$> p <*> pFoldr_ng alg sepp <|>  pure e)
                                   where sepp = sep *> p

pFoldr1Sep    ::  (IsParser p, IsCheckable p) => (a -> b -> b, b) -> p st a1 -> p st a -> p st b
pFoldr1Sep     alg@(op,e) sep p =  must_be_non_empties "pFoldr1Sep"    sep   p pfm
                                   where pfm = op <$> p <*> pFoldr    alg (sep *> p)
pFoldr1Sep_ng ::   (a -> b -> b, b) -> P st a1 ->P st a -> P st b
pFoldr1Sep_ng  alg@(op,e) sep p =  must_be_non_empties "pFoldr1Sep_ng" sep   p pfm 
                                   where pfm = op <$> p <*> pFoldr_ng alg (sep *> p)

list_alg :: (a -> [a] -> [a], [a1])
list_alg = ((:), [])

pList    ::    (IsParser p, IsCheckable p) => p st a -> p st [a]
pList         p =  must_be_non_empty "pList"    p (pFoldr        list_alg   p)
pList_ng ::   (IsParser p, IsCheckable p) => p st a -> p st [a]
pList_ng      p =  must_be_non_empty "pList_ng" p (pFoldr_ng     list_alg   p)

pList1    ::   (IsParser p, IsCheckable p) => p st a -> p st [a]
pList1         p =  must_be_non_empty "pList"    p (pFoldr1       list_alg   p)
pList1_ng ::   (IsParser p, IsCheckable p) => p st a -> p st [a]
pList1_ng      p =  must_be_non_empty "pList_ng" p (pFoldr1_ng    list_alg   p)


pListSep    :: (IsParser p, IsCheckable p) => p st a1 -> p st a -> p st [a]
pListSep      sep p = must_be_non_empties "pListSep"    sep   p (pFoldrSep     list_alg sep p)
pListSep_ng :: (IsParser p, IsCheckable p) => p st a1 -> p st a -> p st [a]
pListSep_ng   sep p = must_be_non_empties "pListSep_ng" sep   p pFoldrSep_ng  list_alg sep p

pList1Sep    :: (IsParser p, IsCheckable p) => p st a1 -> p st a -> p st [a]
pList1Sep     s p =  must_be_non_empties "pListSep"    s   p (pFoldr1Sep    list_alg s p)
pList1Sep_ng :: (IsParser p, IsCheckable p) => p st a1 -> p st a -> p st [a]
pList1Sep_ng  s p =  must_be_non_empties "pListSep_ng" s   p (pFoldr1Sep_ng list_alg s p)

pChainr    :: (IsParser p, IsCheckable p) =>p st (c -> c -> c) -> p st c -> p st c
pChainr    op x    =   must_be_non_empties "pChainr"    op   x r where r = x <??> (flip <$> op <*> r)
pChainr_ng :: (IsParser p, IsCheckable p) =>p st (c -> c -> c) -> p st c -> p st c
pChainr_ng op x    =   must_be_non_empties "pChainr_ng" op   x r where r = x <**> ((flip <$> op <*> r)  <|> pure id)

pChainl    :: (IsParser p, IsCheckable p) =>p st (c -> c -> c) -> p st c -> p st c
pChainl   op x    =  must_be_non_empties "pChainl"    op   x (f <$> x <*> pList (flip <$> op <*> x)) 
                    where  f x [] = x
                           f x (func:rest) = f (func x) rest
pChainl_ng ::(IsParser p, IsCheckable p) => p st (c -> c -> c) -> p st c -> p st c
pChainl_ng op x    = must_be_non_empties "pChainl_ng" op   x (f <$> x <*> pList_ng (flip <$> op <*> x))
                     where f x [] = x
                           f x (func:rest) = f (func x) rest

-- | Build a parser for each element in its argument list and tries them all.
pAny :: (IsParser p, IsCheckable p) => (a -> p st a1) -> [a] -> p st a1
pAny  f l =  foldr (<|>) pFail (map f l)

-- | Parses any of the symbols in 'l'.
pAnySym :: (IsParser p, Provides st s s) => [s] -> p st s
pAnySym = pAny pSym 



