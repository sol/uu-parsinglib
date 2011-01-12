{-# LANGUAGE  FlexibleContexts,
              RankNTypes #-}

module Text.ParserCombinators.UU.BasicInstances.String (
   Parser,
   createStr,
   
   -- From BasicInstances
   pToken,
   pTokenCost,
   pMunch,
   show_errors,
   show_expecting
   ) where

import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.BasicInstances
import qualified Text.ParserCombinators.UU.BasicInstances.List as BL

-- | Basic type of a parser with returntype @a@.
type Parser a = P (Str Char String (Int, Int)) a

-- | @`createStr`@ creates a @`Str`@ state from a @String@.
createStr :: String -> Str Char String (Int, Int)
createStr ls = BL.createStr ls (0,0)
