 
{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction #-}


-- | The module `Core` contains the basic functionality of the parser library. 
--   It  uses the  breadth-first module  to realise online generation of results, the error
--   correction administration, dealing with ambigous grammars; it defines the types  of the elementary  parsers
--   and  recognisers involved.For typical use cases of the libray see the module @"Text.ParserCombinators.UU.Examples"@

module Text.ParserCombinators.UU.Core ( module Text.ParserCombinators.UU.Core
                                      , module Control.Applicative
                                      , module Text.ParserCombinators.UU.BreadthFirstSearch) where
import Control.Applicative  hiding  ((<$), many, some, optional)
import Text.ParserCombinators.UU.BreadthFirstSearch
import Char
import Debug.Trace
import Maybe

-- * The Classes Defining the Interface
-- ** `IsParser`

-- | This class collects a number of classes which together defines what a `Parser` should provide. 
-- Since it is just a predicate we have prefixed the name by the phrase `Is'

class    (Applicative p, ExtApplicative p, Alternative p)    => IsParser p where
instance (Applicative p, ExtApplicative p, Alternative p)    => IsParser p where

infixl  4  <$
infix   2  <?>

-- ** `ExtApplicative'
-- | The module "Control.Applicative" contains the definition for `<$` which cannot be changed . 
-- Since we want to give optimised implementations of this combinator, we hide its definition, and define a class containing its signature.

class  ExtApplicative p where
  (<$)      ::  a               -> p b   ->   p  a

-- ** `Symbol'
-- | Many parsing libraries do not make a distinction between the terminal symbols of the language recognised and the 
-- tokens actually constructed from the  input. This happens e.g. if we want to recognise an integer or an identifier: we are also interested in which integer occurred in the input, 
-- or which identifier. 

-- ^ The function `pSym` takes as argument a value of some type `symbol', and returns a value of type `token'. The parser will in general depend on some 
--   state which is maintained holding the input. The functional dependency fixes the `token` type, based on the `symbol` type and the type of the parser `p`.
--   Since `pSym' is overloaded both the type and the value of symbol determine how to decompose the input in a `token` and the remaining input.
--   `pSymExt` is the actual function, which takes two extra parameters: one describing the minimal numer of tokens recognised, 
--   and the second whether the symbol can recognise the empty string and the value which is to be returned in that case

class  Symbol p  symbol token | p symbol -> token where
  -- | The first parameter to `pSymExt` is a `Nat` which describes the minimal numer of tokens accepted by this parser. It is used in the abstract interpretation
  --   which computes this property for each parser. It's main use is in choosinga non-recursive alternative in case a non-terminal has to be inserted.
  --   The second parameter indicates whether this parser can also skip recognising anything and just return a value of type a, hence a `Maybe a`
  
  pSymExt ::  Nat -> Maybe token -> symbol -> p token
  pSym    ::                        symbol -> p token
  pSym  s   = pSymExt (Succ Zero) Nothing s 

-- ** `Provides'

-- | The function `splitStae` playes a crucial role in splitting up the state. The `symbol` parameter tells us what kind of thing, and even which value of that kind, is expected from the input.
--   The state  and  and the symbol type together determine what kind of token has to be returned. Since the function is overloaded we do not have to invent 
--   all kind of different names for our elementary parsers.
class  Provides state symbol token | state symbol -> token  where
       splitState   ::  symbol -> (token -> state  -> Steps a) -> state -> Steps a

-- ** `Eof'

class Eof state where
       eof          ::  state   -> Bool
       deleteAtEnd  ::  state   -> Maybe (Cost, state)



-- * The type  describing parsers: @`P`@
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Parsers     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- do not change into data, or be prepared to add ~ at subtle places !!
data  P   st  a =  P  (forall r . (a  -> st -> Steps r)  -> st -> Steps       r  ) --  history parser
                      (forall r . (      st -> Steps r)  -> st -> Steps   (a, r) ) --  future parser
                      (forall r . (      st -> Steps r)  -> st -> Steps       r  ) --  recogniser
                      Nat                                                          --  minimal length
                      (Maybe a)                                                    --  possibly empty with value     

-- ** Parsers are functors:  @`fmap`@
instance   Functor (P  state) where 
  fmap f   (P   ph pf pr l me)   =  P  ( \  k -> ph ( k .f ))
                                       ( \  k ->  pushapply f . pf k) -- pure f <*> pf
                                       (pr) 
                                       l
                                       (fmap f me)

-- ** Parsers are Applicative:  @`<*>`@,  @`<*`@,  @`*>`@ and  @`pure`@
instance   Applicative (P  state) where
  P ph pf pr pl pe <*> ~(P qh qf qr ql qe)  =  P  ( \  k -> ph (\ pr -> qh (\ qr -> k (pr qr))))
                                                  ((apply .) . (pf .qf))
                                                  ( pr . qr)
                                                  (nat_add pl ql)
                                                  (pe <*> qe)
  P ph pf pr pl pe <*  ~(P _  _  qr ql qe)   = P  ( ph. (qr.))  (pf. qr)   (pr . qr)
                                                  (nat_add pl ql) 
                                                  (case qe of Nothing -> Nothing ; _ -> pe)
  P _  _  pr pl pe *>  ~(P qh qf qr ql qe)   = P ( pr . qh  )  (pr. qf)    (pr . qr)           
                                                 (nat_add pl ql) (case pe of Nothing -> Nothing ; _ -> qe) 
  pure a                                     =  P  ($a) ((push a).) id Zero (Just a)


-- ** Parsers are Alternative:  @`<|>`@ and  @`empty`@ 
instance   Alternative (P   state) where 
  P ph pf pr pl pe <|> P qh qf qr ql qe 
    =  let (rl, b) = nat_min pl ql
           bestx :: Steps a -> Steps a -> Steps a
           bestx = if b then flip best else best 
       in    P (\  k inp  -> ph k inp `bestx` qh k inp)
               (\  k inp  -> pf k inp `bestx` qf k inp)
               (\  k inp  -> pr k inp `bestx` qr k inp)
               rl
               (case (pe, qe)  of
                 (Nothing, _      ) -> qe
                 (_      , Nothing) -> pe
                 (_      , _      ) -> error "ambiguous parser because two sides of choice can be empty")
  empty                =  P  ( \  k inp  ->  noAlts)
                             ( \  k inp  ->  noAlts)
                             ( \  k inp  ->  noAlts)
                             Infinite
                             Nothing

-- ** Parsers can recognise single tokens:  @`pSym`@ and  @`pSymExt`@
instance  ( Provides state symbol token) => Symbol (P  state) symbol token where
  pSymExt l e a  = P ( \ k inp -> splitState a k inp)
                     ( \ k inp -> splitState a (\ t inp' -> push t (k inp')) inp)
                     ( \ k inp -> splitState a (\ _ inp' -> k inp') inp)
                     l
                     e

-- ** Parsers are Monads:  @`>>=`@ and  @`return`@

unParser_h (P  h   _  _  _ _)  =  h
unParser_f (P  _   f  _  _ _)  =  f
unParser_r (P  _   _  r  _ _)  =  r
          

instance  Monad (P st) where
       P  ph pf pr pl pe >>=  a2q = 
                P  (  \k -> ph (\ a -> unParser_h (a2q a) k))
                   (  \k -> ph (\ a -> unParser_f (a2q a) k))
                   (  \k -> ph (\ a -> unParser_r (a2q a) k))
                   (nat_add pl (error "cannot compute minimal length of right hand side of monadic parser"))
                   (case pe of
                    Nothing -> Nothing
                    Just a -> let (P _ _ _ _ a2qv) = a2q a in a2qv)
       return  = pure 

-- * Additional useful combinators
-- ** Controlling the text of error reporting:  @`<?>`@
-- | The parsers build a list of symbols which are expected at a specific point. 
--   This list is used to report errors.
--   Quite often it is more informative to get e.g. the name of the non-terminal. 
--   The @`<?>`@ combinator replaces this list of symbols by it's righ-hand side argument.

(<?>) :: P state a -> String -> P state a
P  ph  pf  pr  pl pe <?> label = P ( \ k inp -> replaceExpected  ( ph k inp))
                                   ( \ k inp -> replaceExpected  ( pf k inp))
                                   ( \ k inp -> replaceExpected  ( pr k inp))
                                   pl
                                   pe
                           where replaceExpected (Fail _ c) = (Fail [label] c)
                                 replaceExpected others     = others


-- ** An alternative for the Alternative, which is greedy:  @`<<|>`@
-- | `<<|>` is the greedy version of `<|>`. If its left hand side parser can make some progress that alternative is comitted. Can be used to make parsers faster, and even
--   get a complete Parsec equivalent behaviour, with all its (dis)advantages. use with are!

P ph pf pr pl pe <<|> P qh qf qr ql qe 
    = let (rl, b) = nat_min pl ql
          bestx = if b then flip best else best
      in   P ( \ k st  -> norm (ph k st) `bestx` norm (qh k st))
             ( \ k st  -> norm (pf k st) `bestx` norm (qf k st))
             ( \ k st  -> norm (pr k st) `bestx` norm (qr k st))
             rl
             (case (pe, qe)  of
                 (Nothing, _      ) -> qe
                 (_      , Nothing) -> pe
                 (_      , _      ) -> error "ambiguous parser because two sides of choice can be empty")

-- ** Parsers can be disambiguated using micro-steps:  @`micro`@
-- | `micro` inserts a `Cost` step into the sequence representing the progress the parser is making; for its use see `Text.ParserCombinators.UU.Examples` 
P ph pf pr pl pe `micro` i = P ( \ k st -> ph (\ a st -> Cost i (k a st)) st)
                               ( \ k st -> pf (Cost i .k) st)
                               ( \ k st -> pr (Cost i .k) st)
                               pl
                               pe 

-- ** Dealing with (non-empty) Ambigous parsers: @`amb`@ 
--   For the precise functionng of the combinators we refer to the technical report mentioned in the README file
--   @`amb`@ converts an ambiguous parser into a parser which returns a list of possible recognitions.
amb :: P st a -> P st [a]

amb (P ph pf pr pl pe) = P ( \k     ->  removeEnd_h . ph (\ a st' -> End_h ([a], \ as -> k as st') noAlts))
                           ( \k inp ->  combinevalues . removeEnd_f $ pf (\st -> End_f [k st] noAlts) inp)
                           ( \k     ->  removeEnd_h . pr (\ st' -> End_h ([undefined], \ _ -> k  st') noAlts))
                           pl
                           (fmap pure pe)



combinevalues  :: Steps [(a,r)] -> Steps ([a],r)
combinevalues lar           =   Apply (\ lar -> (map fst lar, snd (head lar))) lar

       
-- ** Parse errors can be retreived from the state: @`pErrors`@
-- | `getErrors` retreives the correcting steps made since the last time the function was called. The result can, 
--   using a monad, be used to control how to--    proceed with the parsing process.

class state `Stores`  error | state -> error where
  getErrors    ::  state   -> ([error], state)

pErrors :: Stores st error => P st [error]
pErrors = P ( \ k inp -> let (errs, inp') = getErrors inp in k    errs    inp' )
            ( \ k inp -> let (errs, inp') = getErrors inp in push errs (k inp'))
            ( \ k inp -> let (errs, inp') = getErrors inp in            k inp' )
            Zero       -- this parser does not consume input
            (Just [])  -- the errors consumed cannot be determined statically! Hence we assume none.

-- ** Starting and finalise the parsing process: @`pEnd`@ and @`parse`@
-- | The function `pEnd` should be called at the end of the parsing process. It deletes any unsonsumed input, and reports its preence as an eror.

pEnd    :: (Stores st error, Eof st) => P st [error]
pEnd    = P ( \ k inp ->   let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in k  finalerrors finalstate
                                                    Just (i, inp') -> Fail []  [const (i,  deleterest inp')]
                           in deleterest inp)
            ( \ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in push finalerrors (k finalstate)
                                                    Just (i, inp') -> Fail [] [const ((i, deleterest inp'))]
                           in deleterest inp)
            ( \ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in  (k finalstate)
                                                    Just (i, inp') -> Fail [] [const (i, deleterest inp')]
                           in deleterest inp)
            Zero
            (error "Unforeseen use of pEnd function; pEnd should only be used in function running the actual parser")


-- The function @`parse`@ shows the prototypical way of running a parser on a some specific input
-- By default we use the future parser, since this gives us access to partal result; future parsers are expected to run in less space
parse :: (Eof t) => P t a -> t -> a
parse   (P _  pf _ _ _)  = fst . eval . pf  (\ rest   -> if eof rest then succeedAlways        else error "pEnd missing?")
parse_h (P ph _  _ _ _)  = fst . eval . ph  (\ a rest -> if eof rest then push a failAlways else error "pEnd missing?") 

-- ** The state may be temporarily change type: @`pSwitch`@
-- | `pSwitch` takes the current state and modifies it to a different type of state to which its argument parser is applied. 
--   The second component of the result is a function which  converts the remaining state of this parser back into a valuee of the original type.

pSwitch :: (st1 -> (st2, st2 -> st1)) -> P st2 a -> P st1 a
pSwitch split (P ph pf pr pl pe)    = P (\ k st1 ->  let (st2, back) = split st1
                                                     in ph (\ a st2' -> k a (back st2')) st2)
                                        (\ k st1 ->  let (st2, back) = split st1
                                                     in pf (\st2' -> k (back st2')) st2)
                                        (\ k st1 ->  let (st2, back) = split st1
                                                     in pr (\st2' -> k (back st2')) st2)
                                        pl
                                        pe 


-- ** A more efficient version for @`<$`@ from the module @`Control.Applicative`@
-- | In the new module `Control.Applicative' the operator `<$` is still hard coded. 
--   We hide this import and provide an implementation using a class, which can be redfined when needed.

instance ExtApplicative (P st)  where
  f                <$   (P _  _  qr ql qe)   
    = P ( qr . ($f)) (\ k st -> push f (qr k st)) qr  ql  (case qe of Nothing -> Nothing; _ -> Just f)

-- * Auxiliary functions and types
-- ** Checking for non-sensical combinations: @`must_be_non_empty`@ and @`must_be_non_empties`@
-- | The function checks wehther its second argument is a parser which can recognise the mety sequence. If so an error message is given
--   using the name of the context. If not then the third argument is returned. This is useful in testing for loogical combinations. For its use see
--   the module Text>parserCombinators.UU.Derived

must_be_non_empty :: [Char] -> P t t1 -> t2 -> t2
must_be_non_empty msg p@(P _ _ _ _ (Just _ )) _ 
            = error ("The combinator " ++ msg ++ "\n" ++
                     "    requires that it's argument cannot recognise the empty string\n")
must_be_non_empty _ _  q  = q

-- | This function is similar to the above, but can be used in situations where we recognise a sequence of elements separated by other elements. This does not 
--   make sense if both parsers can recognise the empty string. Your grammar is then highly ambiguous.

must_be_non_empties :: [Char] -> P t1 t -> P t3 t2 -> t4 -> t4
must_be_non_empties  msg (P _ _ _ _ (Just _ )) (P _ _ _ _ (Just _ )) _ 
            = error ("The combinator " ++ msg ++ "\n" ++
                     "    requires that not both arguments can recognise the empty string\n")
must_be_non_empties  msg _  _ q = q

-- ** The type @`Nat`@ for describing the minimal number of tokens consumed
-- | The data type @`Nat`@ is used to represent the minimal length of a parser.
--   Care should be taken in order to not evaluate the right hand side of the binary functions @`nat_min`@ and @`nat-add`@ more than necesssary.

data Nat = Zero
         | Succ Nat
         | Infinite
         deriving  Show

nat_min Zero       _          = trace' "Left Zero in nat_min\n"     (Zero, True)
nat_min Infinite   r          = trace' "Left Infinite in nat_min\n" (r,    False) 
nat_min l          Infinite   = trace' "Right Zero in nat_min\n"    (l,    True)
nat_min _          Zero       = trace' "Right Zero in nat_min\n"    (Zero, False) 
nat_min (Succ ll)  (Succ rr)  = trace' "Succs in nat_min\n"         (let (v, b) = ll `nat_min` rr in (Succ v, b))

nat_add Infinite  _ = trace' "Infinite in add\n" Infinite
nat_add Zero      r = trace' "Zero in add\n"     r
nat_add (Succ l)  r = trace' "Succ in add\n"     (Succ (nat_add l r))

get_length (P _ _ _ l _) = l



