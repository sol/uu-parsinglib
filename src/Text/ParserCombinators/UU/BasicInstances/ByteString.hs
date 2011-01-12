{-# LANGUAGE  FlexibleInstances,
              MultiParamTypeClasses,
              FlexibleContexts,
              RankNTypes #-}

module Text.ParserCombinators.UU.BasicInstances.ByteString (
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
import Data.Word
import qualified Data.ByteString as B

instance Stream B.ByteString Word8 where
   uncons      = B.uncons
   null        = B.null
   head        = B.head
   tail        = B.tail
   span        = ((\(x,y) -> (B.unpack x, y)).) . B.span
-- stripPrefix = Not implemented in bytestring

instance IsLocationUpdatedBy Int Word8 where
   advance i _ = i + 1

-- | Basic type of a parser with returntype @a@.
type Parser a = P (Str Word8 B.ByteString Int) a

-- | @`createStr`@ creates a @`Str`@ state from a @ByteString@.
createStr :: B.ByteString -> Str Word8 B.ByteString Int
createStr bs = Str bs [] 0 True
