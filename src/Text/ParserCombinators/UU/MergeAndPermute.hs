{-# LANGUAGE GADTs,
             KindSignatures, 
             FlexibleContexts,
             LiberalTypeSynonyms #-}

module Text.ParserCombinators.UU.MergeAndPermute where
import Text.ParserCombinators.UU
infixl 4  <||> 

data Gram f a =  Gram  [Alt f a]  (Maybe a) 

data Alt  f a =  forall b . Seq  (f (b -> a)) (Gram f b)
              |             Elem (f       a)  

instance Functor f => Functor (Gram f) where
  fmap f (Gram alts e) = Gram (map (fmap f) alts) (fmap f e)

instance Functor f => Functor (Alt f) where
  fmap a2c (fb2a `Seq` fb) = fmap (a2c .) fb2a `Seq` fb
  fmap a2c (Elem fa      ) = Elem (a2c <$> fa)

instance Functor f => Alternative (Gram f) where
  empty                     = Gram [] Nothing
  Gram ps pe <|> Gram qs qe = Gram (ps++qs) (pe <|> qe)

instance Functor f => Applicative (Gram f) where
  pure            a         = Gram [] (Just a)
  Gram l le  <*> ~rg@(Gram r re) 
    =   Gram  ((map (`fwdby` rg) l) ++ maybe [] (\e -> map (fmap e) r) le) (le <*> re)
        where  (f `Seq` q) `fwdby` r  = fmap uncurry f `Seq` (fmap (,) q <*> r)
               Elem    fa  `fwdby` r  = fa `Seq` r

(<||>):: Functor f => Gram f (b->a) -> Gram f b -> Gram f a
pg@(Gram pl pe) <||> qg@(Gram ql qe)
   = Gram ([ fmap uncurry p                        `Seq` ((,) <$> pp <||> qg) | p `Seq` pp <- pl]
     ++    [ fmap (\qv( pv, qqv) -> pv (qv qqv)) q `Seq` ((,) <$> pg <||> qq) | q `Seq` qq <- ql]
     ++    [ p `Seq` qg                                                       | Elem p     <- pl]
     ++    [ fmap (flip ($)) q `Seq` pg                                       | Elem q     <- ql]
          ) (pe <*> qe)                                         

mkParserG :: (Applicative f, ExtAlternative f) => Gram f a -> f a
mkParserG (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <*> mkParserG pp
         mkParserAlt (Elem p    ) = p
 
instance Functor f => ExtAlternative (Gram f) where
  Gram ps pe <-|-> Gram qs qe = Gram (ps++qs) (pe <|> qe)


instance IsParser f => IsParser (Gram f) where
  must_be_non_empty msg (Gram _ (Just _)) _
    = error ("The combinator " ++ msg ++  " requires that it's argument cannot recognise the empty string\n")
  must_be_non_empty _ _  q  = q
  must_be_non_empties  msg (Gram _ (Just _)) (Gram _ (Just _)) _ 
    = error ("The combinator " ++ msg ++  " requires that not both arguments can recognise the empty string\n")
  must_be_non_empties  msg _  _ q = q

