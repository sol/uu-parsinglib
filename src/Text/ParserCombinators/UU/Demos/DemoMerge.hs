{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.ParserCombinators.UU.Demo.DemoMerge where

import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.Examples
import Text.ParserCombinators.UU.MergeAndPermute

lift x = [x]
pa = lift <$> pSym 'a'
pb = lift <$> pSym 'b'

-- pa' :: Gram (P state) token
pa' = mkGram pa
pb' = mkGram pb
pc' = mkGram (lift <$> pSym 'c')
two p = (++) <$> p <*> p

three p = (,,) <$> p <*> p <*> p

pExact 0 p = pure []
pExact n p = (:) <$> p <*> pExact (n-1) p


test = run (mkParserM ((,,) <$> two pa' <||> three pb' <||> pExact 1 pc' )) "cabcabb"


