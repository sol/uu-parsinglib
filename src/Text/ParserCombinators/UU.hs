-- | The non-exported module "Text.ParserCombinators.UU.Examples" contains a list of examples of how to use the main functionality of this library: it demonstrates:
--
-- * how to write basic parsers
--
-- * how to to write ambiguous parsers
--
-- * how the error correction works
--
-- * how to fine tune your parsers to get rid of ambiguities
--
-- * how to use the monadic interface
--
-- * what kind of error messages you can get if you write erroneous parsers
--

module Text.ParserCombinators.UU ( module Text.ParserCombinators.UU.Core
                                 , module Text.ParserCombinators.UU.BasicInstances
                                 , module Text.ParserCombinators.UU.Derived
                                 , module Text.ParserCombinators.UU.Merge) where
import Text.ParserCombinators.UU.Core
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Derived
import Text.ParserCombinators.UU.Merge

