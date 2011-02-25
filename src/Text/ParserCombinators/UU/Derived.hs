{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction #-}

module Text.ParserCombinators.UU.Derived where
import Text.ParserCombinators.UU.Core
import Control.Monad

-- | This module contains a large variety of combinators for list-lile structures. the extension @_ng@ indiactes that 
--   that variant is the non-greedy variant.
--   See the "Text.ParserCombinators.UU.Examples" module for some exmaples of their use.

-- * Some common combinators for oft occurring constructs

-- | @`pReturn`@ is defined for upwards comptaibility
--
pReturn :: Applicative p => a -> p  a
pReturn  = pure

-- | @`pFail`@ is defined for upwards comptaibility, and is the unit for @<|>@
--
pFail :: Alternative  p => p  a
pFail    = empty

infixl 4  <??>

-- | @pMaybe@ greedily recognises its argument. If not @Nothing@ is returned.
--
pMaybe :: IsParser p => p a -> p (Maybe a)
pMaybe p = must_be_non_empty "pMaybe" p (Just <$> p `opt` Nothing) 

-- | @pEither@ recognises either one of its arguments.
--
pEither :: IsParser p => p a -> p b -> p (Either a b)
pEither p q = Left <$> p <|> Right <$> q
                                                
-- | @<$$>@ is the version of @<$>@ which maps on its second argument 
--
(<$$>)    ::  IsParser p => (a -> b -> c) -> p b -> p (a -> c)
f <$$> p  =  flip f <$> p

-- | @<??>@ parses an optional postfix element and applies its result to its left hand result
--
(<??>) :: IsParser p => p a -> p (a -> a) -> p a
p <??> q        = must_be_non_empty "<??>" q (p <**> (q `opt` id))

-- | @`pPackes`@ surrounds its third parser with the first and the seond one, keeping only the middle result
pPacked :: IsParser p => p b1 -> p b2 -> p a -> p a
pPacked l r x   =   l *>  x <*   r

-- * The collection of iterating combinators, all in a greedy (default) and a non-greedy variant

pFoldr    :: IsParser p => (a -> a1 -> a1, a1) -> p a -> p a1
pFoldr         alg@(op,e)     p =  must_be_non_empty "pFoldr" p pfm
                                   where pfm = (op <$> p <*> pfm) `opt` e

pFoldr_ng ::  IsParser p => (a -> a1 -> a1, a1) -> p a -> p a1
pFoldr_ng      alg@(op,e)     p =  must_be_non_empty "pFoldr_ng" p pfm 
                                   where pfm = (op <$> p <*> pfm)  <|> pure e


pFoldr1    :: IsParser p => (v -> b -> b, b) -> p v -> p b
pFoldr1        alg@(op,e)     p =  must_be_non_empty "pFoldr1"    p (op <$> p <*> pFoldr     alg p) 

pFoldr1_ng ::  IsParser p => (v -> b -> b, b) -> p v -> p b
pFoldr1_ng     alg@(op,e)     p =  must_be_non_empty "pFoldr1_ng" p (op <$> p <*> pFoldr_ng  alg p)

pFoldrSep    ::  IsParser p => (v -> b -> b, b) -> p a -> p v -> p b
pFoldrSep      alg@(op,e) sep p =  must_be_non_empties "pFoldrSep" sep   p
                                   (op <$> p <*> pFoldr    alg sepp `opt` e)
                                   where sepp = sep *> p
pFoldrSep_ng ::  IsParser p => (v -> b -> b, b) -> p a -> p v -> p b
pFoldrSep_ng   alg@(op,e) sep p =  must_be_non_empties "pFoldrSep" sep   p
                                   (op <$> p <*> pFoldr_ng alg sepp <|>  pure e)
                                   where sepp = sep *> p

pFoldr1Sep    ::   IsParser p => (a -> b -> b, b) -> p a1 ->p a -> p b
pFoldr1Sep     alg@(op,e) sep p =  must_be_non_empties "pFoldr1Sep"    sep   p pfm
                                   where pfm = op <$> p <*> pFoldr    alg (sep *> p)
pFoldr1Sep_ng ::   IsParser p => (a -> b -> b, b) -> p a1 ->p a -> p b
pFoldr1Sep_ng  alg@(op,e) sep p =  must_be_non_empties "pFoldr1Sep_ng" sep   p pfm 
                                   where pfm = op <$> p <*> pFoldr_ng alg (sep *> p)

list_alg :: (a -> [a] -> [a], [a1])
list_alg = ((:), [])

pList    ::    IsParser p => p a -> p [a]
pList         p =  must_be_non_empty "pList"    p (pFoldr        list_alg   p)
pList_ng ::    IsParser p => p a -> p [a]
pList_ng      p =  must_be_non_empty "pList_ng" p (pFoldr_ng     list_alg   p)

pList1    ::  IsParser p =>  p a -> p [a]
pList1         p =  must_be_non_empty "pList"    p (pFoldr1       list_alg   p)
pList1_ng ::   IsParser p => p a -> p [a]
pList1_ng      p =  must_be_non_empty "pList_ng" p (pFoldr1_ng    list_alg   p)


pListSep    :: IsParser p => p a1 -> p a -> p [a]
pListSep      sep p = must_be_non_empties "pListSep"    sep   p (pFoldrSep     list_alg sep p)
pListSep_ng :: IsParser p => p a1 -> p a -> p [a]
pListSep_ng   sep p = must_be_non_empties "pListSep_ng" sep   p pFoldrSep_ng  list_alg sep p

pList1Sep    :: IsParser p => p a1 -> p a -> p [a]
pList1Sep     s p =  must_be_non_empties "pListSep"    s   p (pFoldr1Sep    list_alg s p)
pList1Sep_ng :: IsParser p => p a1 -> p a -> p [a]
pList1Sep_ng  s p =  must_be_non_empties "pListSep_ng" s   p (pFoldr1Sep_ng list_alg s p)

pChainr    :: IsParser p => p (c -> c -> c) -> p c -> p c
pChainr    op x    =   must_be_non_empties "pChainr"    op   x r where r = x <??> (flip <$> op <*> r)
pChainr_ng :: IsParser p => p (c -> c -> c) -> p c -> p c
pChainr_ng op x    =   must_be_non_empties "pChainr_ng" op   x r where r = x <**> ((flip <$> op <*> r)  <|> pure id)

pChainl    :: IsParser p => p (c -> c -> c) -> p c -> p c
pChainl   op x    =  must_be_non_empties "pChainl"    op   x (f <$> x <*> pList (flip <$> op <*> x)) 
                    where  f x [] = x
                           f x (func:rest) = f (func x) rest
pChainl_ng :: IsParser p => p (c -> c -> c) -> p c -> p c
pChainl_ng op x    = must_be_non_empties "pChainl_ng" op   x (f <$> x <*> pList_ng (flip <$> op <*> x))
                     where f x [] = x
                           f x (func:rest) = f (func x) rest

-- | Build a parser for each elemnt in its argument list and tries them all.
pAny :: IsParser p => (a -> p a1) -> [a] -> p a1
pAny  f l =  foldr (<|>) pFail (map f l)

-- | Parses any of the symbols in 'l'.
pAnySym :: Provides st s s => [s] -> P st s
pAnySym = pAny pSym 

instance (IsParser p, Monad p) => MonadPlus (p) where
  mzero = pFail
  mplus = (<|>)
