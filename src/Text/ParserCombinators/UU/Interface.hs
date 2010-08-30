module Text.ParserCombinators.UU.Interface ( module Text.ParserCombinators.UU.Interface
                                           , module Control.Applicative
                                           ) where
import Control.Applicative --  (Applicative, Alternative, (<$>))

-- *  @IsParser@
-- | We introduce the class IsParser which collects all functionality we expect from a parser
--
class (Applicative p, Alternative p) => Isparser p


-- ** `Provides'

-- | The function `splitState` playes a crucial role in splitting up the state. The `symbol` parameter tells us what kind of thing, and even which value of that kind, is expected from the input.
--   The state  and  and the symbol type together determine what kind of token has to be returned. Since the function is overloaded we do not have to invent 
--   all kind of different names for our elementary parsers.

class  Provides state symbol token | state symbol -> token  where
       splitState   ::  symbol -> (token -> state  -> Steps a) -> state -> Steps a

-- ** `Eof'

class Eof state where
       eof          ::  state   -> Bool
       deleteAtEnd  ::  state   -> Maybe (Cost, state)

-- ** `Location` 
-- | The input state may contain a location which can be used in error messages. Since we do not want to fix our input to be just a @String@ we provide an interface
--   which can be used to advance the location by passing its information in the function splitState

class Show loc => loc `IsLocationUpdatedBy` str where
    advance::loc -> str -> loc

--  ** An extension to @`Alternative`@ which indicates a biased choice
-- | In order to be able to describe greedy parsers we introduce an extra operator, which indicates a biased choice
class ExtAlternative p where
  (<<|>) :: p a -> p a -> p a


data Report   = FromLeft   String Report
              | FromRight  String Report
              | FromSingle String Report
              | LeafLocation String String -- name of combinator and error message

type Status = [Report] 

combineErrors loc l r  = map (FromLeft loc) l ++ map (FromRight loc) r 
class (Applicative p, Alternative p) => IsParser p where
  acceptsEpsilon :: p a -> Bool

propErrors loc e = map (FromSingle loc) e

class IsCheckable p where
  noChecking     :: p  -> p 
  reportMistake  :: String -> String -> p  -> p 
  addMistake     :: String -> Status -> p  -> p
  getMistakes    :: p  -> Status
  noChecking     = id
  getMistakes  p = []


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Auxiliary Functions and Types        %%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- * Auxiliary functions and types
-- ** Checking for non-sensical combinations: @`must_be_non_empty`@ and @`must_be_non_empties`@
-- | The function checks wehther its second argument is a parser which can recognise the mety sequence. If so an error message is given
--   using the name of the context. If not then the third argument is returned. This is useful in testing for loogical combinations. For its use see
--   the module Text>parserCombinators.UU.Derived

must_be_non_empty :: (IsParser p, IsCheckable q) => [Char] -> p x -> q -> q
must_be_non_empty msg p r 
   = if acceptsEpsilon p 
     then reportMistake   msg  " requires that it's argument cannot recognise the empty string" r
     else r



-- | This function is similar to the above, but can be used in situations where we recognise a sequence of elements separated by other elements. This does not 
--   make sense if both parsers can recognise the empty string. Your grammar is then highly ambiguous.

must_be_non_empties :: (IsParser p, IsCheckable q) =>  [Char] -> p  x -> p  y -> q  -> q 
must_be_non_empties  msg p q r
            = if acceptsEpsilon p && acceptsEpsilon q 
              then reportMistake msg " requires that not both arguments can recognise the empty string" r
              else r


