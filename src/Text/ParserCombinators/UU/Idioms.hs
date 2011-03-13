{-# LANGUAGE RankNTypes,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             UndecidableInstances,
             FlexibleContexts,
             CPP #-}

module Text.ParserCombinators.UU.Idioms where

import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.Demo.Examples hiding (show_demos)
import qualified Data.ListLike as LL
import Control.Applicative 


-- | The  `Ii` is to be pronounced as @stop@
data Ii = Ii 

-- | The function `iI` is to be pronounced as @start@
iI :: Idiomatic  (Str Char state loc) (a -> a) g => g
iI = idiomatic (pure id)

class Idiomatic st f g  | g -> f st  where
    idiomatic :: P st f -> g
instance  Idiomatic (Str Char state loc) x  (Ii -> P  (Str Char state loc) x) where
    idiomatic ix Ii = ix
instance (Idiomatic  (Str Char state loc) f g, IsLocationUpdatedBy loc Char, LL.ListLike state Char) 
       => Idiomatic  (Str Char state loc) (a -> f) (P  (Str Char state loc) a -> g) where
    idiomatic isf is = idiomatic (isf <*> is)
instance (Idiomatic  (Str Char state loc) f g, IsLocationUpdatedBy loc Char, LL.ListLike state Char) 
       => Idiomatic  (Str Char state loc) f (String -> g) where
    idiomatic isf str = idiomatic (isf <* pToken str)
instance  (Idiomatic (Str Char state loc) f g, IsLocationUpdatedBy loc Char, LL.ListLike state Char) 
      =>   Idiomatic (Str Char state loc) f (Char -> g) where
    idiomatic isf c = idiomatic (isf <* pSym c)
instance Idiomatic st f g => Idiomatic st ((a -> b) -> f)  ((a -> b) -> g) where
    idiomatic isf f = idiomatic (isf <*> (pure f))

-- | The idea of the Idiom concept is that  sequential composition operators can be inferred from the type 
--   of the various operands
--
-- >>> run (iI (+) '(' pNatural "+"  pNatural ')' Ii) "(2+3"
--   Result: 5
--    Correcting steps: 
--      Inserted  ')' at position LineColPos 0 4 4 expecting one of [')', Whitespace, '0'..'9']
--
test :: Parser Int
test = iI (+) '(' pNatural "+" pNatural ')' Ii

#define DEMO(p,i) demo "p" i p

show_demos =  demo "(iI (+) '(' pNatural \"+\" pNatural ')' Ii)::Parser Int" "(2+3)" ((iI (+) '(' pNatural "+" pNatural ')' Ii)::Parser Int)
