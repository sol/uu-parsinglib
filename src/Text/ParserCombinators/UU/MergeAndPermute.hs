{-# LANGUAGE ExistentialQuantification #-}

module Text.ParserCombinators.UU.MergeAndPermute where
import Text.ParserCombinators.UU.Core
infixl 4  <||>, <<||> 

data Gram f a =             Gram  [Alt f a]  (Maybe a) 
data Alt  f a =  forall b . Seq   (f b)      (Gram f (b -> a)) 
              |  forall b.  Bind  (f b)      (b -> Gram f a) 

mkGram p = must_be_non_empty "mkGram" p (Gram [p `Seq` Gram  [] (Just id)] Nothing)

instance Functor f => Functor (Gram f) where
  fmap f (Gram alts e) = Gram (map (f <$>) alts) (f <$> e)

instance Functor f => Functor (Alt f) where
  fmap a2c (fb `Seq` fb2a) = fb `Seq` ( (a2c .) <$> fb2a)
  fmap a2c (fb `Bind` b2fa) = fb `Bind` (\b -> fmap a2c (b2fa b))

instance Functor f => Alternative (Gram f) where
  empty                     = Gram [] Nothing
  Gram ps pe <|> Gram qs qe = Gram (ps++qs) (pe <|> qe)

instance Functor f => ExtAlternative (Gram f) where
  Gram ps pe <-|-> Gram qs qe = Gram (ps++qs) (pe <|> qe)
  p <<|> q                    = p <|> q
  must_be_non_empty msg (Gram _ (Just _)) _
    = error ("The combinator " ++ msg ++  " requires that it's argument cannot recognise the empty string\n")
  must_be_non_empty _ _  q  = q
  must_be_non_empties  msg (Gram _ (Just _)) (Gram _ (Just _)) _ 
    = error ("The combinator " ++ msg ++  " requires that not both arguments can recognise the empty string\n")
  must_be_non_empties  msg _  _ q = q


instance Functor f => Applicative (Gram f) where
  pure a = Gram [] (Just a)
  Gram l le  <*> ~rg@(Gram r re) 
    =   Gram  ((map (`fwdby` rg) l) ++ maybe [] (\e -> map (e <$>) r) le) (le <*> re)
        where (f `Seq` q) `fwdby` r = f `Seq` (flip <$> q <*> r)
              (fb `Bind` b2fa) `fwdby` r = fb `Bind` (\b -> (b2fa b) <*> r)

instance  Monad (Gram f) where
  return a = Gram [] (Just a)
  Gram ps pe >>= a2qs = 
     let bindto :: Alt f b -> (b -> Gram f a) -> Alt f a
         (b `Seq` b2a)  `bindto` a2c = b `Bind` (\b -> b2a >>= (\b2a -> a2c (b2a b)))
         (b `Bind` b2a) `bindto` a2c = b `Bind` (\b -> b2a b >>= a2c)
         psa2qs = (map (`bindto` a2qs) ps)
     in case pe of
        Nothing -> Gram psa2qs Nothing
        Just a  -> let Gram qs qe = a2qs a
                   in  Gram (psa2qs ++ qs) qe

instance Functor f => IsParser (Gram f)
  

(<||>):: Functor f => Gram f (b->a) -> Gram f b -> Gram f a
pg@(Gram pl pe) <||> qg@(Gram ql qe)
   = Gram (   [ p `Seq` (flip  <$> pp <||> qg)     | p `Seq` pp <- pl      ]
           ++ [ q `Seq` ((.)   <$> pg <||> qq)     | q `Seq` qq <- ql      ]
           ++ [ fc `Bind` (\c -> c2fb2a c <||> qg) | fc `Bind` c2fb2a <- pl]
           ++ [ fc `Bind` (\c -> pg <||> c2fb c)   | fc `Bind` c2fb   <- ql]
          )   (pe <*> qe)                                         

(<<||>):: Functor f => Gram f (b->a) -> Gram f b -> Gram f a
pg@(Gram pl pe) <<||> ~qg@(Gram ql qe)
   = Gram (   [ p `Seq` (flip  <$> pp <||> qg)| p `Seq` pp <- pl]
          )   (pe <*> qe)


mkParserM :: (Monad f, Applicative f, ExtAlternative f) => Gram f a -> f a
mkParserM (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <**> mkParserM pp
         mkParserAlt (fc `Bind` c2fa) = fc >>=  (mkParserM . c2fa)
 


mkParserS :: (Monad f, Applicative f, ExtAlternative f) => f b -> Gram f a -> f a
mkParserS sep (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <**> mkParserP sep pp
         mkParserAlt (fc `Bind` c2fa) = fc >>=  (mkParserS sep . c2fa)

mkParserP :: (Monad f, Applicative f, ExtAlternative f) => f b -> Gram f a -> f a
mkParserP sep (Gram ls le) = foldr (<-|->) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = sep *> p <**> mkParserP sep pp
         mkParserAlt (fc `Bind` c2fa) = fc >>=  (mkParserP sep . c2fa)



