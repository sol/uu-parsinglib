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

pReturn  = pure
pFail    = empty

infixl 4  <??>
infixl 2 `opt`

-- | Optionally recognize parser 'p'.
-- 
-- If 'p' can be recognized, the return value of 'p' is used. Otherwise,
-- the value 'v' is used. Note that opt is greedy, if you do not want
-- this use @... <|> pure v@  instead. Furthermore, 'p' should not
-- recognise the empty string, since this would make your parser ambiguous!!

opt ::  P st a -> a -> P st a
p `opt` v       =  p <<|> pure v 

pMaybe :: P st a -> P st (Maybe a)
pMaybe p = Just <$> p `opt` Nothing 

pEither p q = Left <$> p <|> Right <$> q
                                                
(<$$>)    ::  (a -> b -> c) -> P st b -> P st (a -> c)
f <$$> p  =  flip f <$> p

(<??>) :: P st a -> P st (a -> a) -> P st a
p <??> q        = p <**> (q `opt` id)

-- | This can be used to parse 'x' surrounded by 'l' and 'r'.
-- 
-- Example:
--
-- > pParens = pPacked pOParen pCParen
pPacked :: P st b1 -> P st b2 -> P st a -> P st a
pPacked l r x   =   l *>  x <*   r

-- =======================================================================================
-- ===== Iterating ps ===============================================================
-- =======================================================================================
pFoldr    :: (a -> a1 -> a1, a1) -> P st a -> P st a1
pFoldr_ng ::  (a -> a1 -> a1, a1) -> P st a -> P st a1
pFoldr         alg@(op,e)     p = pfm where pfm = (op <$> p <*> pfm) `opt` e
pFoldr_ng      alg@(op,e)     p = pfm where pfm = (op <$> p <*> pfm)  <|> pure e


pFoldr1    :: (v -> b -> b, b) -> P st v -> P st b
pFoldr1_ng ::  (v -> b -> b, b) -> P st v -> P st b
pFoldr1        alg@(op,e)     p = op <$> p <*> pFoldr  alg p
pFoldr1_ng     alg@(op,e)     p = op <$> p <*> pFoldr_ng  alg p

pFoldrSep    ::  (v -> b -> b, b) -> P st a -> P st v -> P st b
pFoldrSep_ng ::  (v -> b -> b, b) -> P st a -> P st v -> P st b
pFoldrSep      alg@(op,e) sep p = op <$> p <*> pFoldr    alg sepp `opt` e
                                  where sepp = sep *> p
pFoldrSep_ng   alg@(op,e) sep p = op <$> p <*> pFoldr_ng alg sepp <|>  pure e
                                  where sepp = sep *> p

pFoldr1Sep    ::   (a -> b -> b, b) -> P st a1 ->P st a -> P st b
pFoldr1Sep_ng ::   (a -> b -> b, b) -> P st a1 ->P st a -> P st b
pFoldr1Sep     alg@(op,e) sep p = pfm where pfm = op <$> p <*> pFoldr    alg (sep *> p)
pFoldr1Sep_ng  alg@(op,e) sep p = pfm where pfm = op <$> p <*> pFoldr_ng alg (sep *> p)

list_alg :: (a -> [a] -> [a], [a1])
list_alg = ((:), [])

pList    ::    P st a -> P st [a]
pList_ng ::    P st a -> P st [a]
pList         p = pFoldr        list_alg   p
pList_ng      p = pFoldr_ng     list_alg   p

pList1    ::   P st a -> P st [a]
pList1_ng ::   P st a -> P st [a]
pList1         p = pFoldr1       list_alg   p
pList1_ng      p = pFoldr1_ng    list_alg   p


pListSep    :: P st a1 -> P st a -> P st [a]
pListSep_ng :: P st a1 -> P st a -> P st [a]
pListSep      sep p = pFoldrSep     list_alg sep p
pListSep_ng   sep p = pFoldrSep_ng  list_alg sep p

pList1Sep    :: P st a1 -> P st a -> P st [a]
pList1Sep_ng :: P st a1 -> P st a -> P st [a]
pList1Sep     s p = pFoldr1Sep    list_alg s p
pList1Sep_ng  s p = pFoldr1Sep_ng list_alg s p

pChainr    :: P st (c -> c -> c) -> P st c -> P st c
pChainr_ng :: P st (c -> c -> c) -> P st c -> P st c
pChainr    op x    =  r where r = x <??> (flip <$> op <*> r)
pChainr_ng op x    =  r where r = x <**> ((flip <$> op <*> r)  <|> pure id)

pChainl    :: P st (c -> c -> c) -> P st c -> P st c
pChainl_ng :: P st (c -> c -> c) -> P st c -> P st c
pChainl   op x    = f <$> x <*> pList (flip <$> op <*> x) 
                    where  f x [] = x
                           f x (func:rest) = f (func x) rest
pChainl_ng op x    = f <$> x <*> pList_ng (flip <$> op <*> x) 
                     where f x [] = x
                           f x (func:rest) = f (func x) rest

-- | Parses using any of the parsers in the list 'l'.

pAny :: (a -> P st a1) -> [a] -> P st a1
pAny  f l =  foldr (<|>) pFail (map f l)

-- | Parses any of the symbols in 'l'.
pAnySym :: Provides st s s => [s] -> P st s
pAnySym = pAny pSym 

{-
-- more efficient version has been defined in the module BasicInstances
pToken :: Provides st s s => [s] -> P st [s]
pToken []     = pure []
pToken (a:as) = (:) <$> pSym a <*> pToken as


pAnyToken ::  Provides st s s => [[s]] -> P st [s]
pAnyToken = pAny pToken
-}
