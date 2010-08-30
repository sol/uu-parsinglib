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
pReturn :: a -> P str a
pReturn  = pure

-- | @`pFail`@ is defined for upwards comptaibility, and is the unit for @<|>@
--
pFail :: P str a
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
p `opt` v       = must_be_non_empty "opt" p (p <<|> pure v) 

-- | @pMaybe@ greedily recognises its argument. If not @Nothing@ is returned.
--
pMaybe :: P st a -> P st (Maybe a)
pMaybe p = must_be_non_empty "pMaybe" p (Just <$> p `opt` Nothing) 

-- | @pEither@ recognises either one of its arguments.
--
pEither :: P str a -> P str b -> P str (Either a b)
pEither p q = Left <$> p <|> Right <$> q
                                                
-- | @<$$>@ is the version of @<$>@ which maps on its second argument 
--
(<$$>)    ::  (a -> b -> c) -> P st b -> P st (a -> c)
f <$$> p  =  flip f <$> p

-- | @<??>@ parses an optional postfix element and applies its result to its left hand result
--
(<??>) :: P st a -> P st (a -> a) -> P st a
p <??> q        = must_be_non_empty "<??>" q (p <**> (q `opt` id))

-- | @`pPackes`@ surrounds its third parser with the first and the seond one, keeping only the middle result
pPacked :: P st b1 -> P st b2 -> P st a -> P st a
pPacked l r x   =   l *>  x <*   r

-- * The collection of iterating combinators, all in a greedy (default) and a non-greedy variant

pFoldr    :: (a -> a1 -> a1, a1) -> P st a -> P st a1
pFoldr         alg@(op,e)     p =  must_be_non_empty "pFoldr" p pfm
                                   where pfm = (op <$> p <*> pfm) `opt` e

pFoldr_ng ::  (a -> a1 -> a1, a1) -> P st a -> P st a1
pFoldr_ng      alg@(op,e)     p =  must_be_non_empty "pFoldr_ng" p pfm 
                                   where pfm = (op <$> p <*> pfm)  <|> pure e


pFoldr1    :: (v -> b -> b, b) -> P st v -> P st b
pFoldr1        alg@(op,e)     p =  must_be_non_empty "pFoldr1"    p (op <$> p <*> pFoldr     alg p) 

pFoldr1_ng ::  (v -> b -> b, b) -> P st v -> P st b
pFoldr1_ng     alg@(op,e)     p =  must_be_non_empty "pFoldr1_ng" p (op <$> p <*> pFoldr_ng  alg p)

pFoldrSep    ::  (v -> b -> b, b) -> P st a -> P st v -> P st b
pFoldrSep      alg@(op,e) sep p =  must_be_non_empties "pFoldrSep" sep   p
                                   (op <$> p <*> pFoldr    alg sepp `opt` e)
                                   where sepp = sep *> p
pFoldrSep_ng ::  (v -> b -> b, b) -> P st a -> P st v -> P st b
pFoldrSep_ng   alg@(op,e) sep p =  must_be_non_empties "pFoldrSep" sep   p
                                   (op <$> p <*> pFoldr_ng alg sepp <|>  pure e)
                                   where sepp = sep *> p

pFoldr1Sep    ::   (a -> b -> b, b) -> P st a1 ->P st a -> P st b
pFoldr1Sep     alg@(op,e) sep p =  must_be_non_empties "pFoldr1Sep"    sep   p pfm
                                   where pfm = op <$> p <*> pFoldr    alg (sep *> p)
pFoldr1Sep_ng ::   (a -> b -> b, b) -> P st a1 ->P st a -> P st b
pFoldr1Sep_ng  alg@(op,e) sep p =  must_be_non_empties "pFoldr1Sep_ng" sep   p pfm 
                                   where pfm = op <$> p <*> pFoldr_ng alg (sep *> p)

list_alg :: (a -> [a] -> [a], [a1])
list_alg = ((:), [])

pList    ::    P st a -> P st [a]
pList         p =  must_be_non_empty "pList"    p (pFoldr        list_alg   p)
pList_ng ::    P st a -> P st [a]
pList_ng      p =  must_be_non_empty "pList_ng" p (pFoldr_ng     list_alg   p)

pList1    ::   P st a -> P st [a]
pList1         p =  must_be_non_empty "pList"    p (pFoldr1       list_alg   p)
pList1_ng ::   P st a -> P st [a]
pList1_ng      p =  must_be_non_empty "pList_ng" p (pFoldr1_ng    list_alg   p)


pListSep    :: P st a1 -> P st a -> P st [a]
pListSep      sep p = must_be_non_empties "pListSep"    sep   p (pFoldrSep     list_alg sep p)
pListSep_ng :: P st a1 -> P st a -> P st [a]
pListSep_ng   sep p = must_be_non_empties "pListSep_ng" sep   p pFoldrSep_ng  list_alg sep p

pList1Sep    :: P st a1 -> P st a -> P st [a]
pList1Sep     s p =  must_be_non_empties "pListSep"    s   p (pFoldr1Sep    list_alg s p)
pList1Sep_ng :: P st a1 -> P st a -> P st [a]
pList1Sep_ng  s p =  must_be_non_empties "pListSep_ng" s   p (pFoldr1Sep_ng list_alg s p)

pChainr    :: P st (c -> c -> c) -> P st c -> P st c
pChainr    op x    =   must_be_non_empties "pChainr"    op   x r where r = x <??> (flip <$> op <*> r)
pChainr_ng :: P st (c -> c -> c) -> P st c -> P st c
pChainr_ng op x    =   must_be_non_empties "pChainr_ng" op   x r where r = x <**> ((flip <$> op <*> r)  <|> pure id)

pChainl    :: P st (c -> c -> c) -> P st c -> P st c
pChainl   op x    =  must_be_non_empties "pChainl"    op   x (f <$> x <*> pList (flip <$> op <*> x)) 
                    where  f x [] = x
                           f x (func:rest) = f (func x) rest
pChainl_ng :: P st (c -> c -> c) -> P st c -> P st c
pChainl_ng op x    = must_be_non_empties "pChainl_ng" op   x (f <$> x <*> pList_ng (flip <$> op <*> x))
                     where f x [] = x
                           f x (func:rest) = f (func x) rest

-- | Build a parser for each elemnt in its argument list and tries them all.
pAny :: (a -> P st a1) -> [a] -> P st a1
pAny  f l =  foldr (<|>) pFail (map f l)

-- | Parses any of the symbols in 'l'.
pAnySym :: Provides st s s => [s] -> P st s
pAnySym = pAny pSym 

instance MonadPlus (P st) where
  mzero = pFail
  mplus = (<|>)

-- * Merging parsers

infixl 3 <||>
data Freq p =   AtLeast Int     p
              | AtMost  Int     p
              | Between Int Int p
              | One             p
              | Many            p
              | Opt             p
              | Never           p

instance Functor Freq where
   fmap f (AtLeast n     p)    = AtLeast n   (f p)
   fmap f (AtMost  n     p)    = AtMost  n   (f p)
   fmap f (Between  n m  p)    = Between n m (f p)
   fmap f (One           p)    = One         (f p)
   fmap f (Many          p)    = Many        (f p)
   fmap f (Opt           p)    = Opt         (f p)
   fmap f (Never         p)    = Never       (f p)

canBeEmpty (AtLeast _    p)  = False
canBeEmpty (AtMost  _    p)  = True
canBeEmpty (Between n m  p)  = if n==0 then error "wrong use of Between" else False -- safety check
canBeEmpty (One          p)  = False
canBeEmpty (Many         p)  = True
canBeEmpty (Opt          p)  = True
canBeEmpty (Never        p)  = True

split :: [Freq p] -> ([Freq p] -> [Freq p]) -> [(p, [Freq p])]
split []     _ = []
split (x:xs) f = oneAlt (x, f xs): split xs (f.(x:))
                 where oneAlt  (AtLeast 1   p, others)   = (p, Many                p : others)
                       oneAlt  (AtLeast n   p, others)   = (p, AtLeast  (n-1)      p : others)
                       oneAlt  (AtMost  1   p, others)   = (p,                         others)
                       oneAlt  (AtMost  n   p, others)   = (p, AtMost   (n-1)      p : others)
                       oneAlt  (Between 1 1 p, others)   = (p,                         others)
                       oneAlt  (Between 1 m p, others)   = (p, AtMost        (m-1) p : others)
                       oneAlt  (Between n m p, others)   = (p, Between (n-1) (m-1) p : others)
                       oneAlt  (One         p, others)   = (p,                         others)
                       oneAlt  (Many        p, others)   = (p, Many                p : others)
                       oneAlt  (Opt         p, others)   = (p,                         others)

toParser :: [ Freq (P st (d -> d)) ] -> P st d -> P st d
toParser []    units  =  units
toParser alts  units  =  let palts = [p <*> toParser  ps units | (p,ps) <- split alts id]
                         in if and (map canBeEmpty alts) 
                            then foldr (<|>) units palts
                            else foldr1 (<|>) palts

toParserSep alts sep  units  =  let palts = [p <*> toParser  (map (fmap (sep *>)) ps) units | (p,ps) <- split alts id]
                                in if   and (map canBeEmpty alts) 
                                   then foldr  (<|>) units palts
                                   else foldr1 (<|>) palts

newtype MergeSpec p = MergeSpec p

(<||>) ::  MergeSpec (c,     [Freq (P st (d     -> d)    )],  e -> f     -> g) 
        -> MergeSpec (h,     [Freq (P st (i     -> i)    )],  g -> j     -> k) 
        -> MergeSpec ((c,h), [Freq (P st ((d,i) -> (d,i)))],  e -> (f,j) -> k)

MergeSpec (pe, pp, punp) <||> MergeSpec (qe, qp, qunp)
 = MergeSpec ( (pe, qe)
             , map (fmap (mapFst <$>)) pp ++  map (fmap (mapSnd <$>)) qp
             , \f (x, y) -> qunp (punp f x) y
             )
f `pSem` MergeSpec (units, alts, unp) = MergeSpec  (units, alts, \ g arg -> g ( unp f arg))

pMerge ::  c -> MergeSpec (d, [Freq (P st (d -> d))], c -> d -> e) -> P st e
sem `pMerge` MergeSpec (units, alts, unp) =  unp sem <$> toParser alts (pure units)

pMergeSep ::  (c, P st a)  -> MergeSpec (d, [Freq (P st (d -> d))], c -> d -> e) -> P st e
(sem, sep) `pMergeSep` MergeSpec (units, alts, unp) =  unp sem <$> toParserSep alts sep (pure units)

pBetween  n m p = must_be_non_empty "pOpt"  p 
                 (if m <n || m <= 0 then         (MergeSpec ([]       ,[                           ], id)) 
                  else if n==0 then              (MergeSpec ([]       ,[AtMost  m     ((:)   <$> p)], id)) 
                  else                           (MergeSpec ([]       ,[Between n m   ((:)   <$> p)], id)))
pAtMost   n   p = must_be_non_empty "pOpt"  p
                 (if n <= 0         then         (MergeSpec ([]       ,[                           ], id))
                                    else         (MergeSpec ([]       ,[AtMost  n     ((:)   <$> p)], id)))
pAtLeast  n   p = must_be_non_empty "pOpt"  p
                 (if n <= 0         then         (MergeSpec ([]       ,[Many          ((:)   <$> p)], id))
                                    else         (MergeSpec ([]       ,[AtLeast n     ((:)   <$> p)], id)))
pMany p        = must_be_non_empty "pMany" p     (MergeSpec ([]       ,[Many          ((:)   <$> p)], id))
pOpt  p v      = must_be_non_empty "pOpt"  p     (MergeSpec (v        ,[Opt           (const <$> p)], id))
pSome p        = must_be_non_empty "pSome" p     (MergeSpec ([]       ,[AtLeast 1     ((:)   <$> p)], id))
pOne  p        = must_be_non_empty "pOne"  p     (MergeSpec (undefined,[One           (const <$> p)], id))

mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)

