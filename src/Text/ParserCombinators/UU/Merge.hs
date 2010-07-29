module Text.ParserCombinators.UU.Merge((<||>), pMerged, list_of) where

import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.Derived
import Text.ParserCombinators.UU.BasicInstances

-- | Often one wants to read a sequence of elements of different types, 
--   where the actual order doe not matter. For the semantic processing however
--   it would be nice to get the elemnts of each type collected together: 
-- 
-- >    chars_digs = cat3 `pMerged` (list_of pDig <||> list_of pL <||> list_of pU)
-- 
--  parsing \"12abCD1aV\" now returns \"121abaCDV\"; so the sequence of
--  recognised elements is stored in three lists, which are then passed 
--  to @cat3 :: [a] -> [a] -> [a] -> [a]@ which concatenates the lists again

(<||>) ::  (c,     P st (d     -> d),     e -> f     -> g) 
        -> (h,     P st (i     -> i),     g -> j     -> k) 
        -> ((c,h), P st ((d,i) -> (d,i)), e -> (f,j) -> k)

(pe, pp, punp) <||> (qe, qp, qunp)
 =( (pe, qe)
  , mapFst <$> pp <|>  mapSnd <$> qp
  , \f (x, y) -> qunp (punp f x) y
  )

pMerged ::  c -> (d, P st (d -> d), c -> d -> e) -> P st e
sem `pMerged` (units, alts, unp)
 = let pres = alts <*> pres `opt` units in unp sem <$> pres

list_of :: P st c -> ([d], P st ([c] -> [c]),e -> e)
list_of p = ([], (:) <$> p, id)

mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)



