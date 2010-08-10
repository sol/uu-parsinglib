{-# LANGUAGE ExistentialQuantification,
             MultiParamTypeClasses,
             FlexibleInstances,
             GADTs #-}
module Text.ParserCombinators.UU.Merge where

import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.Derived
import Text.ParserCombinators.UU.BasicInstances 
import Text.ParserCombinators.UU.Examples
import Char

data Repeat st r = forall t . (Freq t st, Functor t) => Repeat {unRepeat :: (t r)}

instance Functor  (Repeat st) where
  fmap f (Repeat tr) = Repeat (fmap f tr)


class Freq f st where
  oneAlt     ::              f  r    -> (P st (r -> r), [Repeat st r])
  canBeEmpty ::              f  r    -> Bool
  startValue ::              f  r    -> r


data One st r  = One  (P st r)
instance Functor (One st) where
  fmap f (One p) = One (f <$> p)
instance Freq (One st) st where
   oneAlt     (One p)    = (const <$> p, [])
   canBeEmpty (One p)    = False
   startValue (One p)    = undefined


data Opt st  r where
   Opt :: (P st r) -> r -> Opt st r
instance Functor (Opt st) where
  fmap f (Opt p v) = Opt (f <$> p) (f v)
instance Freq (Opt st) st where
   oneAlt     (Opt p r)  = (const <$> p, [])
   canBeEmpty (Opt p r)  = True
   startValue (Opt p r)  = r


data Many st r  where
   Many :: P st r -> Many st [r]
--instance Functor (Many st) where
--  fmap f (Many p) = Many (f <$> p)
instance Freq (Many st) st where
   oneAlt     (Many p)  = ((:) <$> p, [Repeat (Many p)])
   canBeEmpty (Many p)  = True
   startValue (Many p)  = []
{-

data Some st r  = Some (P st r)
instance Functor (Some st) where
  fmap f (Some p) = Some (f p)
instance Freq (Some st) st where
   oneAlt     (Some p)  = ((:) <$> p, [Repeat (Many p)])
   canBeEmpty (Some p)  = False
   startValue (Some p)  = []

data Tree p = Tree [(p, Tree p)] Bool

toTree :: [Repeat p] -> Tree p

split []     _ = [[]]
split (x:xs) f = (x, f xs): split xs (f.(x:))

toTree  alts = Tree [(p, toTree (f others))  
                    | (x, others) <-  (split alts id), (p, f) <- (oneAlt . unRepeat) x]
                    (or . map (canBeEmpty.unRepeat) alts)

toParser :: Tree (P st (d -> d)) -> d -> P st d
toParser (Tree []   _)  units = pure units
toParser (Tree alts b)  units = foldr (<|>) (if b then pure units else empty)  
                                [p <*> toParser ps units | (p,ps) <- alts]


(<||>) ::  (c,     [Freq (P st (d     -> d)    )],  e -> f     -> g) 
        -> (h,     [Freq (P st (i     -> i)    )],  g -> j     -> k) 
        -> ((c,h), [Freq (P st ((d,i) -> (d,i)))],  e -> (f,j) -> k)

(pe, pp, punp) <||> (qe, qp, qunp)
 =( (pe, qe)
  , map (fmap (mapFst <$>)) pp ++  map (fmap (mapSnd <$>)) qp
  , \f (x, y) -> qunp (punp f x) y
  )

pMerge ::  c -> (d, [Freq (P st (d -> d))], c -> d -> e) -> P st e
sem `pMerge` (units, alts, unp) =  unp sem <$> toParser (toTree alts) units

many :: P st c -> ([d],[Freq (P st ([c] -> [c]))],e -> e)
many p   = ([]       ,[Many ((:)   <$> p)], id)
prob p v = (v        ,[Opt  (const <$> p)], id)
some p   = ([]       ,[Some ((:)   <$> p)], id)
one p    = (undefined,[One  (const <$> p)], id)

mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)



pa  ::Parser String 
pa  = lift <$> pSym 'a'
pb  :: Parser String 
pb = lift <$> pSym 'b'
pc  :: Parser String 
pc = lift <$> pSym 'c'
lift a = [a]

pDigitAsInt = digit2Int <$> pDigit 
pNatural = foldl (\a b -> a * 10 + b ) 0 <$> pList1 pDigitAsInt
digit2Int a =  ord a - ord '0'

-- parsing letters and identifiers
pDigit :: Parser Char
pDigit  = pSym ('0', '9')

-- the proof is in the eating

t = (,,,) `pMerge` (some pa <||> many pb <||> one pc <||> prob pNatural 5)

runt = run t "abbac45ac"

-}
