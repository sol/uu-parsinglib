{-# LANGUAGE ExistentialQuantification #-}

module Text.ParserCombinators.UU.MergeAndPermute where
import Text.ParserCombinators.UU.Core
infixl 4  <||> 

data Gram f a =             Gram  [Alt f a]  (Maybe a) 
data Alt  f a =  forall b . Seq   (f b)      (Gram f (b -> a))  

mkGram p = must_be_non_empty "mkGram" p (Gram [p `Seq` Gram  [] (Just id)] Nothing)

instance Functor f => Functor (Gram f) where
  fmap f (Gram alts e) = Gram (map (f <$>) alts) (f <$> e)

instance Functor f => Functor (Alt f) where
  fmap a2c (fb `Seq` fb2a) = fb `Seq` ( (a2c .) <$> fb2a)

instance Functor f => Alternative (Gram f) where
  empty                     = Gram [] Nothing
  Gram ps pe <|> Gram qs qe = Gram (ps++qs) (pe <|> qe)

instance Functor f => ExtAlternative (Gram f) where
  Gram ps pe <-|-> Gram qs qe = Gram (ps++qs) (pe <|> qe)
  p <<|> q                    = p <|> q


instance Functor f => Applicative (Gram f) where
  pure a = Gram [] (Just a)
  Gram l le  <*> ~rg@(Gram r re) 
    =   Gram  ((map (`fwdby` rg) l) ++ maybe [] (\e -> map (e <$>) r) le) (le <*> re)
        where (f `Seq` q) `fwdby` r = f `Seq` (flip <$> q <*> r)


instance IsParser f => IsParser (Gram f) where
  must_be_non_empty msg (Gram _ (Just _)) _
    = error ("The combinator " ++ msg ++  " requires that it's argument cannot recognise the empty string\n")
  must_be_non_empty _ _  q  = q
  must_be_non_empties  msg (Gram _ (Just _)) (Gram _ (Just _)) _ 
    = error ("The combinator " ++ msg ++  " requires that not both arguments can recognise the empty string\n")
  must_be_non_empties  msg _  _ q = q

(<||>):: Functor f => Gram f (b->a) -> Gram f b -> Gram f a
pg@(Gram pl pe) <||> qg@(Gram ql qe)
   = Gram (   [ p `Seq` (flip  <$> pp <||> qg)| p `Seq` pp <- pl]
           ++ [ q `Seq` ((.)   <$> pg <||> qq)| q `Seq` qq <- ql]
          )   (pe <*> qe)                                         


mkParserM :: (Applicative f, ExtAlternative f) => Gram f a -> f a
mkParserM (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <**> mkParserM pp
 

mkParserS :: (Applicative f, ExtAlternative f) => f b -> Gram f a -> f a
mkParserS sep (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <**> mkParserP sep pp

mkParserP :: (Applicative f, ExtAlternative f) => f b -> Gram f a -> f a
mkParserP sep (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = sep *> p <**> mkParserP sep pp



