{- Fast, Error Correcting Parser Combinators; Version: see Version History in same directory.
 - Copyright:  S. Doaitse Swierstra
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT 
               the Netherlands
               doaitse@swierstra.net
-}

{- A parser for BibTeX using the parsing combinators from the package uu-parsinglib
   Piet van Oostrum, Atze Dijkstra, Doaitse Swierstra (April 22, 2001)
   Adapted for uu-parsinglib, March 21, 2011 
-}
module Language.Bibtex.UU where
import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.BasicInstances hiding (Parser)
import Text.ParserCombinators.UU.Utils

import Data.Char

type Parser a = P (Str Char String LineCol) a

parsebib filename = do  putStrLn "Starting BibTeX"
                        input <- readFile filename
                        let r =  parse (pBibData <* pEnd) (createStr (LineCol 1 0) input)
                        mapM_ (\(i, (v,err)) -> if null err
                                                then print v
                                                else do putStrLn ("Errors found in record :" ++ show i)
                                                        mapM_ (putStrLn.show) err 
                                                        print v                 
                             ) (zip [1..] r)
                        putStrLn ("Result:" ++ show (length r) ++ " BibTex items were parsed\n")
-- =======================================================================================
-- ===== DATA TYPES ======================================================================
-- =======================================================================================
type BibData  = [(BibEntry, Error LineCol)]

data BibEntry = Entry     String  (String, [Field])  -- kind keyword fieldlist
	      | Comment   String
	      | Preamble  [ValItem]
	      | StringDef Field
              deriving Show

type Field    = (String, [ValItem])

data ValItem  = StringVal String          
	      | IntVal    Int
	      | NameUse   String
	      deriving Show
-- =======================================================================================
-- ===== PARSERS =========================================================================
-- =======================================================================================
pBibData    = pChainr ((\ entry  _ right -> entry:right) <$> pBibEntry)
                      ( [] <$ pSkipUntilIn "@")

pBibEntry :: Parser (BibEntry, [Error LineCol])
pBibEntry   
 =  (  Entry     <$ pAt <*>  micro pName 1   <*> pOpenClose ((pKeyName <* pSpec ',') <+> pListSep_ng pComma pField) <* (pComma `opt` ' ')
    <|> Comment   <$ pAt <*  pKey "comment"  <*> pString
    <|> Preamble  <$ pAt <*  pKey "preamble" <*> pOpenClose pValItems 
    <|> StringDef <$ pAt <*  pKey "string"   <*> pOpenClose pField
    ) 
    <+> pErrors

pField     =  (pName <* pSpec '=') <+> pValItems

pValItems  =  pList1Sep (pSpec '#') (   StringVal   <$> pString 
	                            <|> int_or_name <$> pName
                                    )
              where int_or_name s = if all isDigit s
                                    then IntVal.(read::String->Int) $ s
                                    else NameUse s
-- =======================================================================================
-- ===== LEXICAL STUFF ===================================================================
-- =======================================================================================
pSpec c = lexeme (pSym c)

pOpenClose  p = pParens p <|> pBraces p 
pAt           = pSpec '@'

pSkipUntilIn :: String -> Parser String
pSkipUntilIn     chars = pMunch (not.(`elem` chars))
pSkipWhenUntil :: (Char -> Bool) -> String -> Parser String
pSkipWhenUntil p chars = pMunch  (\ c -> p c && not( c `elem` chars))

pName     = lexeme (pList1 (pLower <|> pUpper <|> pDigit  <|> pAnySym "-_/"))  
pKeyName  = lexeme (pSkipWhenUntil  (\c -> chr 33 <= c && c <=  chr 127) ",=@")

pKey [s]     = (:[]) <$> (pSym s <|> pSym (toUpper s)) <*  pSpaces
pKey (s:ss)  = (:)  <$> (pSym s <|> pSym (toUpper s)) <*> pKey ss
pKey []      = error "Scanner: You cannot have empty reserved words!"

pString 
 = let  curlyString   = (\c -> '{':c++"}") <$> pBraces (pConc pStringWord)
        pStringWordDQ = pMunch1  (not.(`elem` "\"{}")) (Insertion "StringCharDQ" ' ' 5)  <|> curlyString 
        pStringWord   = pMunch1  (not.(`elem`   "{}")) (Insertion "StringChar  " ' ' 5)  <|> curlyString
        pConc         = pFoldr ((++),[]) 
   in (    pSym '"' *> pConc pStringWordDQ <* pSym '"'
      <|>  pBraces (pConc pStringWord)
      ) <* pSpaces

p <+> q = (,) <$> p <*> q

pMunch1 p i= (:) <$> pSatisfy p i <*> pMunch p
