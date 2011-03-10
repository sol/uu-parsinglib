-- | The 'uu-parsinglib' library provides a very powerful and general set
--   of parser combinators, but they're really pretty raw and low-level.
--
--   This module provides some higher-level types and infrastructure to
--   make it easier to use.
--
--   It includes our versions of the useful parts of:
--
--   * Text.ParserCombinators.UU.BasicInstances
--   * Text.ParserCombinators.UU.Examples
--

{-# LANGUAGE PatternGuards, ScopedTypeVariables, NoMonomorphismRestriction,FlexibleInstances,  FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
-- {-# LANGUAGE  MultiParamTypeClasses, TypeSynonymInstances, FlexibleContexts #-}

module Text.ParserCombinators.UU.Utils (
   -- * Single-char parsers
  pCR
{-
pLF,
  pLower,
  pUpper,
  pLetter,
  pAscii,
  pDigit,
  pDigitAsNum,

  -- * Whitespace and comments (comments - not yet supported)
  pSpaces, -- This should not be used very often. In general
           -- you may want to use it to skip initial whitespace
           -- at the start of all input, but after that you
           -- should rely on Lexeme parsers to skip whitespace
           -- as needed. (This is the same as the strategy used
           -- by Parsec).

  -- * Lexeme parsers (as opposed to 'Raw' parsers)
  lexeme,
  pDot,
  pComma,
  pDQuote,
  pLParen,
  pRParen,
  pLBracket,
  pRBracket,
  pLBrace,
  pRBrace,
  pSymbol,

  -- * Raw parsers for numbers
  pNaturalRaw,
  pIntegerRaw,
  pDoubleRaw,

  -- * Lexeme parsers for numbers
  pNatural,
  pInteger,
  pDouble,

  -- * Parsers for Enums
  pEnumRaw,
  pEnum,
  pEnumStrs,

  -- * Parser combinators
  pCount,
  pExact,
  pParens,
  pBraces,
  pBrackets,
  listParser,
  tupleParser,
  pTuple,

  -- * Lexeme parsers for Dates
  pDay,
  pDayMonthYear,

  -- * Lexeme parser for quoted Strings
  pQuotedString,
  pParentheticalString,

  -- * Read-compatability
  parserReadsPrec,
-}
)
where

import Data.Char
import Data.List
import Data.Time
import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.BasicInstances hiding (Parser)
import Text.ParserCombinators.UU.Derived
import Control.Applicative
import Text.Printf

------------------------------------------------------------------------

-- Single Char parsers

type Parser a  =  Provides state   Char       Char  => P state a
-- | A parser for a single characater
type CParser a =  Provides state   Char       Char  => P state a
-- | A parser for a range of characters
type RParser a =  Provides state  (Char,Char) Char  => P state a


pCR :: CParser Char
pCR       = pSym '\r'

pLF :: CParser Char
pLF       = pSym '\n'

pDigit :: RParser Char
pDigit  = pSym ('0','9')

pLower :: RParser Char
pLower  = pSym ('a','z')

pUpper :: RParser Char
pUpper  = pSym ('A','Z')

pLetter:: RParser Char
pLetter = pUpper <|> pLower

pAscii :: RParser Char
pAscii = pSym ('\000', '\254')

pDigitAsNum :: (Provides state (Char,Char) Char, Num a) => P state a
pDigitAsNum =
  digit2Int <$> pDigit
  where
  digit2Int a = fromInteger $ toInteger $ ord a - ord '0'


------------------------------------------------------------------------
-- Whitespace

--pSpaces :: Parser String
pSpaces = pList $ pAnySym " \r\n\t" <?> "Whitespace"


------------------------------------------------------------------------
-- Lexeme Parsers skip trailing whitespace (this terminology comes from Parsec)

--lexeme :: Provides state Char Char => P state a -> P state a
lexeme p = p <* pSpaces

pDot      = lexeme $ pSym '.'
pComma    = lexeme $ pSym ','
pDQuote   = lexeme $ pSym '"'
pLParen   = lexeme $ pSym '('
pRParen   = lexeme $ pSym ')'
pLBracket = lexeme $ pSym '['
pRBracket = lexeme $ pSym ']'
pLBrace   = lexeme $ pSym '{'
pRBrace   = lexeme $ pSym '}'
pSymbol   = lexeme . pToken


------------------------------------------------------------------------
-- Raw (non-Lexeme) Parsers for Numbers

pNaturalRaw :: (Num a, Provides state (Char, Char) Char) => P state a
pNaturalRaw = foldl (\a b -> a * 10 + b) 0 <$> pList1 pDigitAsNum <?> "Natural"


pIntegerRaw :: (Num a, Provides state Char token, Provides state (Char, Char) Char) => P state a
pIntegerRaw = pSign <*> pNaturalRaw <?> "Integer"

pDoubleRaw
  :: (Read a,
      Provides state Char Char,
      Provides state (Token Char) [Char],
      Provides state (Char, Char) Char) => P state a
pDoubleRaw = read <$> pDoubleStr

pDoubleStr
  :: (Provides state (Token Char) [Char],
      Provides state (Char, Char) Char,
      Provides state Char Char) =>
     P state [Char]
pDoubleStr = pOptSign <*> (pToken "Infinity" <|> pPlainDouble)
             <?> "Double (eg -3.4e-5)"
  where
    pPlainDouble = (++) <$> ((++) <$> pList1 pDigit <*> (pFraction `opt` [])) <*> pExponent
    pFraction = (:) <$> pSym '.' <*> pList1 pDigit
    pExponent = ((:) <$> pAnySym "eE" <*> (pOptSign <*> pList1 pDigit)) `opt` []
    pOptSign = ((('+':) <$ (pSym '+')) <|> (('-':) <$ (pSym '-'))) `opt` id

-- | NB - At present this is /not/ a lexeme parser, hence we don't
--   support @- 7.0@, @- 7@, @+ 7.0@ etc.
--   It's also currently private - ie local to this module.
pSign :: (Num a, Provides state Char token) => P state (a -> a)
pSign = (id <$ (pSym '+')) <|> (negate <$ (pSym '-')) `opt` id

pPercentRaw
  :: (Provides state Char Char,
      Provides state (Token Char) [Char],
      Provides state (Char, Char) Char) => P state Double
pPercentRaw = (/ 100.0) . read <$> pDoubleStr <* pSym '%' <?> "Double%"

pPctOrDbl = pPercentRaw <|> pDoubleRaw

------------------------------------------------------------------------
-- Lexeme Parsers for Numbers

{-
pPercentRaw
  :: (Num a,
      Provides state Char Char,
      Provides state (Token Char) [Char],
      Provides state (Char, Char) Char) => P state a
-}
pNatural = lexeme pNaturalRaw

-- pInteger :: Num a => Parser a
pInteger = lexeme pIntegerRaw

-- pDouble :: Parser Double
pDouble = lexeme pDoubleRaw

-- pPercent :: Parser Double
pPercent = lexeme pPctOrDbl


------------------------------------------------------------------------
-- Parsers for Enums

pEnumRaw :: forall a state. (Enum a, Show a,  Provides state (Token Char) String) => P state a
pEnumRaw = foldr (\ c r -> c <$ pToken (show c) <|> r) pFail enumerated
           <?> (printf "Enum (eg %s or ... %s)" (show (head enumerated)) (show (last enumerated)))
            -- unless it is an empty data decl we will always have a head/last (even if the same)
            -- if it is empty, you cannot use it anyhow...
  where
    enumerated :: [a]
    enumerated = [toEnum 0..] 
--    pToken :: Provides st s s => [s] -> P st [s]
--    pToken []     = pure []
--    pToken (a:as) = (:) <$> pSym a <*> pToken as

pEnum ::  (Enum a, Show a, Provides state Char Char, Provides state (Token Char) String) => P state a
pEnum = lexeme pEnumRaw

pEnumStrs
  :: (Show a,
      Provides state (Token a) token,
      Provides state Char Char) => [[a]] -> P state token
pEnumStrs xs = pAny (\t -> pSpaces *> pToken t <* pSpaces) xs <?> "enumerated value in " ++ show xs


-- Parser combinats
pParens :: Provides state Char Char => P state b -> P state b
pParens p = pLParen *> p <* pRParen

pBraces :: Provides state Char Char => P state b -> P state b
pBraces p = pLBrace *> p <* pRBrace

pBrackets :: Provides state Char Char => P state b -> P state b
pBrackets p = pLBracket *> p <* pRBracket

-- | eg [1,2,3]
listParser :: Provides state Char Char => P state a -> P state [a]
listParser = pBrackets . pListSep pComma


-- | eg (1,2,3)
-- tupleParser :: Parser a -> Parser [a]
tupleParser = pParens . pListSep pComma

pTuple :: Provides st Char Char => [P st a] -> P st [a]
pTuple []     = [] <$ pParens pSpaces
pTuple (p:ps) = pParens $ (:) <$> lexeme p <*> mapM ((pComma *>) . lexeme) ps


------------------------------------------------------------------------
-- Lexeme parsers for Dates

data Month = Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sep | Oct | Nov | Dec
           deriving (Enum, Bounded, Eq, Show, Ord)

pDayMonthYear :: (Num d, Num y, Provides state Char Char 
                              , Provides state (Char, Char) Char
                              , Provides state (Token Char) String) => P state (d, Int, y)
pDayMonthYear = lexeme $
                (,,) <$> pDayNum <*> (pSym '-' *> pMonthNum) <*> (pSym '-' *> pYearNum)
  where
    pMonthNum = ((+1) . (fromEnum :: Month -> Int)) <$> pEnumRaw <?> "Month (eg Jan)"
    pDayNum   = pNaturalRaw <?> "Day (1-31)"
    pYearNum  = pNaturalRaw <?> "Year (eg 2019)"

pDay :: (Provides state (Char, Char) Char,
         Provides state (Token Char) String,
         Provides state Char Char) => P state Day

pDay = (\(d,m,y) -> fromGregorian y m d) <$> pDayMonthYear


------------------------------------------------------------------------
-- Quoted Strings

pParentheticalString
  :: (Provides state Char Char,
      Provides state (Char -> Bool, [Char], Char) token) => Char -> P state [token]

pParentheticalString d = lexeme $ pSym d *> pList pNonQuoteVChar <* pSym d
  where
    pNonQuoteVChar = pSym (\c -> visibleChar c && c /= d, 
                          "Character in a string set off from main text by delimiter, e.g. double-quotes or comment token", 'y')
    -- visibleChar :: Char -> Bool
    visibleChar c = '\032' <= c && c <= '\126'

pQuotedString
  :: (Provides state (Char -> Bool, [Char], Char) token,
      Provides state Char Char) =>
     P state [token]
pQuotedString = pParentheticalString '"'

------------------------------------------------------------------------
-- Read-compatability

-- | Converts a UU Parser into a read-style one.
--
-- This is intended to facilitate migration from read-style
-- parsers to UU-based ones.
parserReadsPrec :: Parser a -> Int -> ReadS a
parserReadsPrec p _ s = [parse ((,) <$> p <*> pMunch (const True)) . createStr $ s]

------------------------------------------------------------------------
-- Running parsers

type TriplePos = (Int, Int, Int)
-- | The lower-level interface. (Returns all errors).
execParser :: Parser a -> String -> (a, [Error TriplePos])
execParser p = parse ((,) <$> p <*> pEnd) . createStr

-- | The higher-level interface. (Calls 'error' with a simplified
-- error).  running the parser; if complete input accepted return the
-- result else fail with reporting unconsumed tokens
runParser :: String -> Parser a -> String -> a
runParser inputName p s | (a,b) <- execParser p s =
    if null b
    then a
    else error (printf "Failed parsing '%s' :\n%s\n" inputName (pruneError s b))
         -- We do 'pruneError' above because otherwise you can end
         -- up reporting huge correction streams, and that's
         -- generally not helpful... but the pruning does discard info...

-- | Produce a single simple, user-friendly error message
pruneError :: String -> [Error TriplePos] -> String
pruneError _ [] = ""
pruneError _ (DeletedAtEnd x     : _) = printf "Unexpected '%s' at end." x
pruneError s (Inserted _ pos exp : _) = prettyError s exp pos
pruneError s (Deleted  _ pos exp : _) = prettyError s exp pos

prettyError :: String -> [String] -> TriplePos -> String
prettyError s exp p@(line, c, abs) = printf "Expected %s at %s :\n%s\n%s\n%s\n"
                                    (show_expecting exp)
                                    (show p)
                                    aboveString
                                    inputFrag
                                    belowString
  where
    s' = map (\c -> if c=='\n' || c=='\r' || c=='\t' then ' ' else c) s
    aboveString = replicate 30 ' ' ++ "v"
    belowString = replicate 30 ' ' ++ "^"
    inputFrag   = replicate (30 - c) ' ' ++ (take 71 $ drop (c - 30) s')
