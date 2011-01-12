{-# LANGUAGE  FlexibleInstances,
              MultiParamTypeClasses,
              FlexibleContexts,
              RankNTypes #-}

module Text.ParserCombinators.UU.BasicInstances.List (
   Parser,
   createStr,
   
   -- From BasicInstances
   pToken,
   pTokenCost,
   pMunch,
   show_errors,
   show_expecting
   ) where

import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Core
import qualified Data.List as L

instance Stream [a] a where
   uncons (x:xs) = Just (x, xs)
   uncons _      = Nothing
   null          = L.null
   head          = L.head
   tail          = L.tail
   span          = L.span
   stripPrefix   = L.stripPrefix

-- | Abstract type of a parser with input stream @a@, return type @b@ and location representation @c@.
-- Can be @Parser String Char (Int, Int)@ for example
type Parser a b c = Stream a d => P (Str d a c) b

-- | @`createStr`@ creates a @`Str`@ state from a list and a location representation.
createStr :: Stream [t] t => [t] -> loc -> Str t [t] loc
createStr ls initloc = Str ls [] initloc True
