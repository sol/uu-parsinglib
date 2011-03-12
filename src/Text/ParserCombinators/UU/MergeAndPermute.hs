{-# LANGUAGE ExistentialQuantification #-}

-- | This module contains the additional data types, instance definitions and functions to run parsers in an interleaved way.
--   If all the interlevaed parsers recognise a single connected piece of the input text this incorporates the permutation parsers.
--   For some examples see the module "Text.ParserCombinators.UU.Demo.MergeAndpermute"

module Text.ParserCombinators.UU.MergeAndPermute where
import Text.ParserCombinators.UU.Core
import Control.Applicative

infixl 4  <||>, <<||> 



-- * The data type `Gram`
-- | Since we want to get access to the individial parsers which recognise a consecutive piece of the input text we
--   define a new data type, which lifts the underlying parsers to the grammatical level, so they can be transformed, manipulated, and run in a piecewise way.
--   `Gram` is defined in such a way that we can always access the first parsers to be ran from such a structure.
--   We require that all the `Alt`s do not recognise the empty string. These should be covered by the `Maybe` in the `Gram` constructor.
data Gram f a =             Gram  [Alt f a]  (Maybe a) 
data Alt  f a =  forall b . Seq   (f b)      (Gram f (b -> a)) 
              |  forall b.  Bind  (f b)      (b -> Gram f a)

instance (Show a) => Show (Gram f a) where
  show (Gram l ma) = "Gram " ++ show  (length l) ++ " " ++ show ma 

-- | The function `mkGram` splits a simple parser into the possibly empty part and the non-empty part.
--   The non-empty part recognises a consecutive part of the input.
--   Here we use the function `getOneP` and `getZeroP` which are provided in the uu-parsinglib package,
--   but they could easily be provided by other packages too.

mkGram :: P t a -> Gram (P t) a
mkGram p =  case getOneP p of
            Just p -> Gram [p `Seq` Gram  [] (Just id)] (getZeroP p)
            Nothing -> Gram [] (getZeroP p)

-- * Class instances for Gram
-- | We define instances for the data type `Gram` for `Functor`, `Applicative`,  `Alternative` and `ExtAlternative`
instance Functor f => Functor (Gram f) where
  fmap f (Gram alts e) = Gram (map (f <$>) alts) (f <$> e)

instance Functor f => Functor (Alt f) where
  fmap a2c (fb `Seq`  fb2a) = fb `Seq` ( (a2c .) <$> fb2a)
  fmap a2c (fb `Bind` b2fa) = fb `Bind` (\b -> fmap a2c (b2fa b))

-- | The left hand side operand is gradually transformed so we get access to its first component
instance Functor f => Applicative (Gram f) where
  pure a = Gram [] (Just a)
  Gram l le  <*> ~rg@(Gram r re) 
    =   Gram  ((map (`fwdby` rg) l) ++ maybe [] (\e -> map (e <$>) r) le) (le <*> re)
        where (fb `Seq`  fb2c2a) `fwdby` fc = fb  `Seq`  (flip <$> fb2c2a <*> fc)
              (fb `Bind` b2fc2a) `fwdby` fc = fb  `Bind` ((<*> fc) . b2fc2a)

instance  Functor f => Alternative (Gram f) where
  empty                     = Gram [] Nothing
  Gram ps pe <|> Gram qs qe = Gram (ps++qs) (pe <|> qe)

instance Functor f => ExtAlternative (Gram f) where
  p <<|> q                    = p <|> q
  p <?> s                     = error "No <?> defined for Grammars yet. If you need ask for it"
  must_be_non_empty msg (Gram _ (Just _)) _
    = error ("The combinator " ++ msg ++  " requires that it's argument cannot recognise the empty string\n")
  must_be_non_empty _ _  q  = q
  must_be_non_empties  msg (Gram _ (Just _)) (Gram _ (Just _)) _ 
    = error ("The combinator " ++ msg ++  " requires that not both arguments can recognise the empty string\n")
  must_be_non_empties  msg _  _ q = q


-- * `Gram` is a `Monad`
instance  Monad (Gram f) where
  return a = Gram [] (Just a)
  Gram ps pe >>= a2qs = 
     let bindto :: Alt f b -> (b -> Gram f a) -> Alt f a
         (b `Seq` b2a)  `bindto` a2c = b `Bind` (\b -> b2a >>= ((\b2a -> a2c (b2a b))))
         (b `Bind` b2a) `bindto` a2c = b `Bind` (\b -> b2a b >>= a2c)
         psa2qs = (map (`bindto` a2qs) ps)
     in case pe of
        Nothing -> Gram psa2qs Nothing
        Just a  -> let Gram qs qe = a2qs a
                   in  Gram (psa2qs ++ qs) qe

instance Functor f => IsParser (Gram f)
  
-- | The function `<||>` is the merging equivalent of `<*>`. Instead of running its two arguments consecutively, 
--   the input is split into parts which serve as input for the left operand and parts which are served to the right operand. 
(<||>):: Functor f => Gram f (b->a) -> Gram f b -> Gram f a
pg@(Gram pl pe) <||> qg@(Gram ql qe)
   = Gram (   [ p `Seq` (flip  <$> pp <||> qg)     | p `Seq` pp <- pl      ]
           ++ [ q `Seq` ((.)   <$> pg <||> qq)     | q `Seq` qq <- ql      ]
           ++ [ fc `Bind` (\c -> c2fb2a c <||> qg) | fc `Bind` c2fb2a <- pl]
           ++ [ fc `Bind` (\c -> pg <||> c2fb c)   | fc `Bind` c2fb   <- ql]
          )   (pe <*> qe)                                         

-- |  The function `<<||>` is a special version of `<||>`, whch only starts a new instance of its right operand when the left operand cannot proceed.
--   This is used in the function pmMany, where we want to merge as many instances of its argument, but not more than that.
pg@(Gram pl pe) <<||> ~qg@(Gram ql qe)
   = Gram (   [ p `Seq` (flip  <$> pp <||> qg)| p `Seq` pp <- pl]
          )   (pe <*> qe)


-- | `mkPaserM` converts a `Gram`mar beack into a parser, which can subsequenly be run.
mkParserM :: (Monad f, Applicative f, ExtAlternative f) => Gram f a -> f a
mkParserM (Gram ls le) = foldr (\ p pp -> doNotInterpret p <|> pp) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <**> mkParserM pp
         mkParserAlt (fc `Bind` c2fa) = fc >>=  (mkParserM . c2fa)
 

-- | `mkParserS` is like `mkParserM`, with the additional feature that we allow seprators between the components. Only useful in the permuting case.
mkParserS :: (Monad f, Applicative f, ExtAlternative f) => f b -> Gram f a -> f a
mkParserS sep (Gram ls le) = foldr  (\ p pp -> doNotInterpret p <|> pp) (maybe empty pure le) (map mkParserAlt ls)
   where mkParserAlt (p `Seq` pp) = p <**> mkParserP sep pp
         mkParserAlt (fc `Bind` c2fa) = fc >>=  (mkParserS sep . c2fa)
         mkParserP :: (Monad f, Applicative f, ExtAlternative f) => f b -> Gram f a -> f a
         mkParserP sep (Gram ls le) = foldr (\ p pp -> doNotInterpret p <|> pp) (maybe empty pure le) (map mkParserAlt ls)
             where mkParserAlt (p `Seq` pp) = sep *> p <**> mkParserP sep pp
                   mkParserAlt (fc `Bind` c2fa) = fc >>=  (mkParserP sep . c2fa)

-- | Run a sufficient number of  @p@'s in a merged fashion, but not more than necessary!!
pmMany :: Functor f => Gram f a -> Gram f [a]
pmMany p = let pm = (:) <$> p <<||> pm <|> pure [] in pm



