module Text.ParserCombinators.UU.MergingParsers 
      ((<||>), pSem, pMerge, pMergeSep, pBetween, pAtMost, pAtLeast, pMany, pSome, pOne, pOpt) where

import Text.ParserCombinators.UU.Interface

-- * Merging parsers

infixl 3 <||>
data Freq p =   AtLeast Int     p
              | AtMost  Int     p
              | Between Int Int p
              | One             p
              | Opt             p

instance Functor Freq where
   fmap f (AtLeast n     p)    = AtLeast n   (f p)
   fmap f (AtMost  n     p)    = AtMost  n   (f p)
   fmap f (Between  n m  p)    = Between n m (f p)
   fmap f (One           p)    = One         (f p)
   fmap f (Opt           p)    = Opt         (f p)

canBeEmpty (AtLeast n    p)  = n == 0
canBeEmpty (AtMost  _    p)  = True
canBeEmpty (Between n m  p)  = if n==0 then error "wrong use of Between" else False -- safety check
canBeEmpty (One          p)  = False
canBeEmpty (Opt          p)  = True

split :: [Freq p] -> ([Freq p] -> [Freq p]) -> [(p, [Freq p])]
split []     _ = []
split (x:xs) f = oneAlt (x, f xs): split xs (f.(x:))
                 where oneAlt  (AtLeast 0   p, others)   = (p, AtLeast  0          p : others)
                       oneAlt  (AtLeast n   p, others)   = (p, AtLeast  (n-1)      p : others)
                       oneAlt  (AtMost  1   p, others)   = (p,                         others)
                       oneAlt  (AtMost  n   p, others)   = (p, AtMost   (n-1)      p : others)
                       oneAlt  (Between 1 1 p, others)   = (p,                         others)
                       oneAlt  (Between 1 m p, others)   = (p, AtMost        (m-1) p : others)
                       oneAlt  (Between n m p, others)   = (p, Between (n-1) (m-1) p : others)
                       oneAlt  (One         p, others)   = (p,                         others)
                       oneAlt  (Opt         p, others)   = (p,                         others)

toParser :: (IsParser  p, IsCheckable (p d)) => [ Freq (p (d -> d)) ] -> p d -> p d
toParser []    units  =  units
toParser alts  units  =  let palts = [p <*> noChecking (toParser  ps units) | (p,ps) <- split alts id]
                         in if and (map canBeEmpty alts) 
                            then foldr (<|>) units palts
                            else foldr1 (<|>) palts

toParserSep alts sep  units  =  let palts = [p <*> noChecking (toParser  (map (fmap (sep *>)) ps) units) | (p,ps) <- split alts id]
                                in if   and (map canBeEmpty alts) 
                                   then foldr  (<|>) units palts
                                   else foldr1 (<|>) palts

data MergeSpec p = MergeSpec p Status

instance IsCheckable (MergeSpec p)  where
  noChecking                   (MergeSpec p q ) = MergeSpec p []
  reportMistake  comb message  (MergeSpec p q ) = MergeSpec p [LeafLocation comb message]
  getMistakes                  (MergeSpec _ es) = es
  addMistake  _ _ _                             = error "no addmistake defined for MergeSpec p"


(<||>) :: IsParser p =>   MergeSpec (c,      [Freq (p (d     -> d)    )],  e -> f     -> g) 
                     ->   MergeSpec (h,      [Freq (p (i     -> i)    )],  g -> j     -> k) 
                     ->   MergeSpec ((c,h),  [Freq (p ((d,i) -> (d,i)))],  e -> (f,j) -> k)

MergeSpec (pe, pp, punp) le <||> MergeSpec (qe, qp, qunp) re
 = MergeSpec ( (pe, qe)
             , map (fmap (mapFst <$>)) pp ++  map (fmap (mapSnd <$>)) qp
             , \f (x, y) -> qunp (punp f x) y
             ) (combineErrors "<||>" le re)
   where mapFst f (a, b) = (f a, b)
         mapSnd f (a, b) = (a, f b)

pSem :: t  -> MergeSpec (d, [Freq (p (d -> d))], t          -> d -> t4)
           -> MergeSpec (d, [Freq (p (d -> d))], (t4 -> t5) -> d -> t5)

f `pSem` MergeSpec (units, alts, unp) e = MergeSpec  (units, alts, \ g arg -> g ( unp f arg)) (propErrors "pSem" e)

pMerge ::  (IsParser p, IsCheckable (p d), IsCheckable (p e)) => c -> MergeSpec (d, [Freq (p (d -> d))], c -> d -> e) -> p e
sem `pMerge` MergeSpec (units, alts, unp) e = addMistake "pMerge" e (unp sem <$> toParser alts (pure units))

pMergeSep ::  (IsParser p, IsCheckable (p d), IsCheckable (p e)) => (c, p a)  -> MergeSpec (d, [Freq (p (d -> d))], c -> d -> e) -> p e
(sem, sep) `pMergeSep` MergeSpec (units, alts, unp) e =  addMistake "pMerge" e (unp sem <$> toParserSep alts sep (pure units))

pBetween :: IsParser p => Int -> Int -> p a -> MergeSpec ([a], [Freq (p ([a] -> [a]))], b -> b)
pBetween  n m p = must_be_non_empty "pOpt"  p 
                 (if      m <n || m <= 0 then    (MergeSpec ([]       ,[                                  ], id) []) 
                  else if n==0           then    (MergeSpec ([]       ,[AtMost  m            ((:)   <$> p)], id) []) 
                  else                           (MergeSpec ([]       ,[Between n m          ((:)   <$> p)], id) []))

pAtMost :: IsParser p => Int -> p a -> MergeSpec ([a], [Freq (p ([a] -> [a]))], b -> b)
pAtMost   n   p = must_be_non_empty "pAtMost"  p
                 (if n <= 0         then         (MergeSpec ([]       ,[                                  ], id) [])
                                    else         (MergeSpec ([]       ,[AtMost  n            ((:)   <$> p)], id) []))

pAtLeast :: IsParser p => Int -> p a -> MergeSpec ([a], [Freq (p ([a] -> [a]))], b -> b)
pAtLeast n p = must_be_non_empty "pAtLeast" p    (MergeSpec ([]       ,[AtLeast (n `max` 0)  ((:)   <$> p)], id) [])

pMany :: IsParser p => p a -> MergeSpec ([a], [Freq (p ([a] -> [a]))], b -> b)
pMany      p = must_be_non_empty "pMany"    p    (MergeSpec ([]       ,[AtLeast 0            ((:)   <$> p)], id) [])

pSome::  IsParser p => p a -> MergeSpec ([a], [Freq (p ([a] -> [a]))], b -> b)
pSome      p = must_be_non_empty "pSome"    p    (MergeSpec ([]       ,[AtLeast 1            ((:)   <$> p)], id) [])

pOne::   IsParser p => p a ->  MergeSpec (a, [Freq (p (a -> a))], b -> b)
pOne       p = must_be_non_empty "pOne"     p    (MergeSpec (undefined,[One                  (const <$> p)], id) [])

pOpt ::  IsParser p => p a -> a -> MergeSpec (a, [Freq (p (a -> a))], b -> b)
pOpt    p  v = must_be_non_empty "pOpt"     p    (MergeSpec (v        ,[Opt                  (const <$> p)], id) [])


