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
infixl 2 `opt`

-- | Optionally recognize parser 'p'.
-- 
-- If 'p' can be recognized, the return value of 'p' is used. Otherwise,
-- the value 'v' is used. Note that opt is greedy, if you do not want
-- this use @... <|> pure v@  instead. Furthermore, 'p' should not
-- recognise the empty string, since this would make your parser ambiguous!!

opt ::  (IsParser p, ExtAlternative p) => p a -> a -> p a
p `opt` v       = must_be_non_empty "opt" p (p <<|> pure v) 

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

{-
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

canBeEmpty :: Freq t -> Bool
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

toIsParser' :: [ Freq (p (d -> d)) ]  -> p (d -> d)
toIsParser' []      =  pure id
toIsParser' alts    =  let palts = [(.) <$> p <*> toIsParser'  ps  | (p,ps) <- split alts id]
                     in if and (map canBeEmpty alts) 
                        then foldr (<|>) (pure id) palts
                        else foldr1 (<|>) palts

toIsParser :: [ Freq (p (d -> d)) ] -> p d -> p d
toIsParser []    units  =  units
toIsParser alts  units  =  let palts = [p <*> toIsParser  ps units | (p,ps) <- split alts id]
                         in if and (map canBeEmpty alts) 
                            then foldr (<-|->) units palts
                            else foldr1 (<-|->) palts


toIsParserSep :: [Freq (p (b -> b))] -> p a -> p b -> p b
toIsParserSep alts sep  units  =  let palts = [p <*> toIsParser  (map (fmap (sep *>)) ps) units | (p,ps) <- split alts id]
                                in if   and (map canBeEmpty alts) 
                                   then foldr  (<-|->) units palts
                                   else foldr1 (<-|->) palts

newtype MergeSpec p = MergeSpec p

(<||>) ::  MergeSpec (d,     [Freq (p (d     -> d)    )],  e -> d     -> g) 
        -> MergeSpec (i,     [Freq (p (i     -> i)    )],  g -> i     -> k) 
        -> MergeSpec ((d,i), [Freq (p ((d,i) -> (d,i)))],  e -> (d,i) -> k)

MergeSpec (pe, pp, punp) <||> MergeSpec (qe, qp, qunp)
 = MergeSpec ( (pe, qe)
             , map (fmap (mapFst <$>)) pp ++  map (fmap (mapSnd <$>)) qp
             , \f (x, y) -> qunp (punp f x) y
             )

pSem :: t -> MergeSpec (t1, t2, t -> t3 -> t4)
          -> MergeSpec (t1, t2, (t4 -> t5) -> t3 -> t5)
f `pSem` MergeSpec (units, alts, unp) = MergeSpec  (units, alts, \ g arg -> g ( unp f arg))

pMerge ::  c -> MergeSpec (d, [Freq (p (d -> d))], c -> d -> e) -> p e
sem `pMerge` MergeSpec (units, alts, unp) =  unp sem <$> toIsParser alts (pure units)

pMergeSep ::  (c, p a)  -> MergeSpec (d, [Freq (p (d -> d))], c -> d -> e) -> p e
(sem, sep) `pMergeSep` MergeSpec (units, alts, unp) =  unp sem <$> toIsParserSep alts sep (pure units)

pBetween :: Int -> Int -> P t t1 -> MergeSpec ([a], [Freq (P t ([t1] -> [t1]))], a1 -> a1)
pBetween  n m p = must_be_non_empty "pOpt"  p 
                 (if m <n || m <= 0 then         (MergeSpec ([]       ,[                           ], id)) 
                  else if n==0 then              (MergeSpec ([]       ,[AtMost  m     ((:)   <$> p)], id)) 
                  else                           (MergeSpec ([]       ,[Between n m   ((:)   <$> p)], id)))

pAtMost :: Int -> P t t1 -> MergeSpec ([a], [Freq (P t ([t1] -> [t1]))], a1 -> a1)
pAtMost   n   p = must_be_non_empty "pOpt"  p
                 (if n <= 0         then         (MergeSpec ([]       ,[                           ], id))
                                    else         (MergeSpec ([]       ,[AtMost  n     ((:)   <$> p)], id)))

pAtLeast :: Int -> P t t1 -> MergeSpec ([a], [Freq (P t ([t1] -> [t1]))], a1 -> a1)
pAtLeast  n   p = must_be_non_empty "pOpt"  p
                 (if n <= 0         then         (MergeSpec ([]       ,[Many          ((:)   <$> p)], id))
                                    else         (MergeSpec ([]       ,[AtLeast n     ((:)   <$> p)], id)))

pMany :: P t t1 -> MergeSpec ([a], [Freq (P t ([t1] -> [t1]))], a1 -> a1)
pMany p        = must_be_non_empty "pMany" p     (MergeSpec ([]       ,[Many          ((:)   <$> p)], id))

pOpt :: P t t1 -> t11 -> MergeSpec (t11, [Freq (P t (b -> t1))], a -> a)
pOpt  p v      = must_be_non_empty "pOpt"  p     (MergeSpec (v        ,[Opt           (const <$> p)], id))

pSome :: P t t1 -> MergeSpec ([a], [Freq (P t ([t1] -> [t1]))], a1 -> a1)
pSome p        = must_be_non_empty "pSome" p     (MergeSpec ([]       ,[AtLeast 1     ((:)   <$> p)], id))

pOne :: P t t1 -> MergeSpec (a, [Freq (P t (b -> t1))], a1 -> a1)
pOne  p        = must_be_non_empty "pOne"  p     (MergeSpec (undefined,[One           (const <$> p)], id))

mapFst :: (t -> t2) -> (t, t1) -> (t2, t1)
mapFst f (a, b) = (f a, b)

mapSnd :: (t1 -> t2) -> (t, t1) -> (t, t2)
mapSnd f (a, b) = (a, f b)
-}

