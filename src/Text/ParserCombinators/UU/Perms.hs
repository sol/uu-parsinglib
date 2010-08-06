{-# LANGUAGE ExistentialQuantification,
             ScopedTypeVariables #-}
-- | This module contains the combinators for building permutation phrases as described in. 
-- They differ from the version found in Control.Applicative in that elements may recognise the empty string too. 
-- In addition we provide a combinator which allows separators between the elements of the permutation.
-- For an example of their use see the end of the @`main`@ function in "Text.ParserCombinators.UU.Examples"
--
-- @
--      \@article{1030338,
--	Address = {New York, NY, USA},
--	Author = {Baars, Arthur I. and L{\"o}h, Andres and Swierstra, S. Doaitse},
--	Date-Modified = {2008-12-01 21:44:00 +0100},
--	Doi = {http://dx.doi.org/10.1017/S0956796804005143},
--	Issn = {0956-7968},
--	Journal = {J. Funct. Program.},
--	Number = {6},
--	Pages = {635--646},
--	Publisher = {Cambridge University Press},
--	Title = {Parsing permutation phrases},
--	Volume = {14},
--	Year = {2004}}
-- @
--

module Text.ParserCombinators.UU.Perms 
      {-# DEPRECATED "Use equivalent functionality from Text.ParserCombinators.UU.Derived instead" #-}
  (Perms(), pPerms, pPermsSep, succeedPerms, (~*~), (~$~)) where
import Text.ParserCombinators.UU.Core
import Data.Maybe

-- =======================================================================================
-- ===== PERMUTATIONS ================================================================
-- =======================================================================================

newtype Perms st a = Perms (Maybe (P st a), [Br st a])
data Br st a = forall b. Br (Perms st (b -> a)) (P st b)

instance Functor (Perms st) where
  fmap f (Perms (ma, brs)) = Perms (fmap (f <$>) ma, (map (fmap f) brs))

instance  Functor (Br st) where
  fmap f (Br perm p) = Br (fmap (f.) perm) p 

(~*~) ::  Perms st (a -> b) -> P st a -> Perms st b
perms ~*~ p = perms `add` (getZeroP p, getOneP p)

(~$~) ::  (a -> b) -> P st a -> Perms st b
f     ~$~ p = succeedPerms f ~*~ p

succeedPerms ::  a -> Perms st a
succeedPerms x = Perms (Just (pure x), []) 

add ::  Perms st (a -> b) -> (Maybe (P st a),Maybe (P st a)) -> Perms st b
add b2a@(Perms (eb2a, nb2a)) bp@(eb, nb)
 =  let changing ::  (a -> b) -> Perms st a -> Perms st b
        f `changing` Perms (ep, np) = Perms (fmap (f <$>) ep, [Br ((f.) `changing` pp) p | Br pp p <- np])
    in Perms
      ( do { f <- eb2a
           ; x <- eb
           ; return (f <*>  x)
           }
      ,  (case nb of
          Nothing     -> id
          Just pb     -> (Br b2a  pb:)
        )[ Br ((flip `changing` c) `add`  bp) d |  Br c d <- nb2a]
      )

pPerms ::  Perms st a -> P st a 
pPerms (Perms (empty,nonempty))
 = foldl (<|>) (fromMaybe pFail empty) [ (flip ($)) <$> p <*> pPerms pp
                                       | Br pp  p <- nonempty
                                       ]

pPermsSep ::  P st x -> Perms st a -> P st a
pPermsSep (sep :: P st z) perm = p2p (pure ()) perm
 where  p2p :: P st x -> Perms st a -> P st a
        p2p fsep (Perms (mbempty, nonempties)) = 
                let empty          = fromMaybe  pFail mbempty
                    pars (Br t p)  = flip ($) <$ fsep <*> p <*> p2p sep t
                in foldr (<|>) empty (map pars nonempties)              
        p2p_sep =  p2p sep 

pFail :: P st a
pFail = empty                  
