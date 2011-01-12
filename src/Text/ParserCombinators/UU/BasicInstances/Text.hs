{-# LANGUAGE  FlexibleInstances,
              MultiParamTypeClasses,
              FlexibleContexts,
              RankNTypes #-}

module Text.ParserCombinators.UU.BasicInstances.Text (
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
import qualified Data.Text as T

instance Stream T.Text Char where
   uncons      = T.uncons
   null        = T.null
   head        = T.head
   tail        = T.tail
   span        = ((\(x,y) -> (T.unpack x, y)).) . T.span
   stripPrefix = T.stripPrefix . T.pack

-- | Basic type of a parser with returntype @a@.
type Parser a = P (Str Char T.Text (Int, Int)) a

-- | @`createStr`@ creates a @`Str`@ state from a @Data.Text@.
createStr :: T.Text -> Str Char T.Text (Int, Int)
createStr bs = Str bs [] (0,0) True
