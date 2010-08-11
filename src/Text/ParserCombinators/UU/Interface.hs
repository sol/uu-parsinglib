module Text.ParserCombinators.UU.Interface ( module Text.ParserCombinators.UU.Interface
                                           , module Control.Applicative
                                           ) where
import Control.Applicative --  (Applicative, Alternative, (<$>))

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


