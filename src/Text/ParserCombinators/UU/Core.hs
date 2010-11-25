{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies #-}

-- | The module `Core` contains the basic functionality of the parser library. 
--   It  uses the  breadth-first module  to realise online generation of results, the error
--   correction administration, dealing with ambigous grammars; it defines the types  of the elementary  parsers
--   and  recognisers involved.For typical use cases of the libray see the module @"Text.ParserCombinators.UU.Examples"@

module Text.ParserCombinators.UU.Core ( module Text.ParserCombinators.UU.Core
                                      , module Control.Applicative) where
import Control.Applicative  hiding  (many, some, optional)
import Char
import Debug.Trace
import Maybe


infix   2  <?>    -- should be the last element in a sequence of alternatives
infixl  3  <<|>   -- intended use p <<|> q <<|> r <|> x <|> y <?> z


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
-- | In order to be able to describe greedy parsers we introduce an extra operator, whch indicates a biased choice
class ExtAlternative p where
  (<<|>) :: p a -> p a -> p a
     

-- * The  triples containg a  history, a future parser and a recogniser: @`T`@
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Triples     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- actual parsers
data T st a  = T  (forall r . (a  -> st -> Steps r)  -> st -> Steps       r  ) --  history parser
                  (forall r . (      st -> Steps r)  -> st -> Steps   (a, r) ) --  future parser
                  (forall r . (      st -> Steps r)  -> st -> Steps       r  ) --  recogniser

instance Functor (T st) where
  fmap f (T ph pf pr) = T  ( \  k -> ph ( k .f ))
                           ( \  k ->  pushapply f . pf k) -- pure f <*> pf
                           pr
  f <$ (T _ _ pr)     = T  ( pr . ($f)) 
                           ( \ k st -> push f ( pr k st)) 
                           pr

-- ** Triples are Applicative:  @`<*>`@,  @`<*`@,  @`*>`@ and  @`pure`@
instance   Applicative (T  state) where
  T ph pf pr  <*> ~(T qh qf qr)  =  T ( \  k -> ph (\ pr -> qh (\ qr -> k (pr qr))))
                                      ((apply .) . (pf .qf))
                                      ( pr . qr)
  T ph pf pr  <*  ~(T _  _  qr)   = T ( ph. (qr.))  (pf. qr)   (pr . qr)
  T _  _  pr  *>  ~(T qh qf qr )  = T ( pr . qh  )  (pr. qf)    (pr . qr)            
  pure a                          = T ($a) ((push a).) id 

instance   Alternative (T  state) where 
  T ph pf pr  <|> T qh qf qr  =   T (\  k inp  -> ph k inp `best` qh k inp)
                                    (\  k inp  -> pf k inp `best` qf k inp)
                                    (\  k inp  -> pr k inp `best` qr k inp)
  empty                =  T  ( \  k inp  ->  noAlts) ( \  k inp  ->  noAlts) ( \  k inp  ->  noAlts)

{-
-- instance ExtAlternative (T st) where 
-- unfortunatelythis is not possible since we have to make the choice for swapping elsewhere
-}


instance ExtAlternative Maybe where
  Nothing <<|> r        = r
  l       <<|> Nothing  = l 
  l       <<|> r        = l -- choosing the high priority alternative ? is this the right choice?


-- * The  descriptor @`P`@ of a parser, including the tupled parser corresponding to this descriptor
--
data  P   st  a =  P  (T  st a)         --   actual parsers
                      (Maybe (T st a))  --   non-empty parsers; Nothing if  they are absent
                      Nat               --   minimal length
                      (Maybe a)         --   possibly empty with value 

instance Show (P st a) where
  show (P _ nt n e) = "P _ " ++ maybe "Nothing" (const "(Just _)") nt ++ " (" ++ show n ++ ") " ++ maybe "Nothing" (const "(Just _)") e

getOneP :: P a b -> Maybe (P a b)
getOneP (P _ (Just _)  Zero _ )    =  error "The element is a special parser which cannot be combined"
getOneP (P _ Nothing   l    _ )    =  Nothing
getOneP (P _ onep      l    ep )   =  Just( P (mkParser onep Nothing)  onep l Nothing)

getZeroP :: P t a -> Maybe (P st a)
getZeroP (P _ _ l Nothing)         =  Nothing
getZeroP (P _ _ l pe)              =  Just (P (mkParser Nothing pe) Nothing l pe) -- TODO check for erroneous parsers

mkParser :: Maybe (T st a) -> Maybe a -> T st a
mkParser np@Nothing   ne@Nothing   =  empty           
mkParser np@(Just nt) ne@Nothing   =  nt              
mkParser np@Nothing   ne@(Just a)  =          (pure a)        
mkParser np@(Just nt) ne@(Just a)  =  (nt <|> pure a) 

-- combine creates the non-empty parser 
combine :: (Alternative f) => Maybe t1 -> Maybe t2 -> t -> Maybe t3
        -> (t1 -> t -> f a) -> (t2 -> t3 -> f a) -> Maybe (f a)
combine Nothing   Nothing  _  _     _   _   = Nothing      -- this Parser always fails
combine (Just p)  Nothing  aq _     op1 op2 = Just (p `op1` aq) 
combine (Just p)  (Just v) aq nq    op1 op2 = case nq of
                                              Just nnq -> Just (p `op1` aq <|> v `op2` nnq)
                                              Nothing  -> Just (p `op1` aq                ) -- rhs contribution is just from empty alt
combine Nothing   (Just v) _  nq    _   op2 = case nq of
                                              Just nnq -> Just (v `op2` nnq)  -- right hand side has non-empty part
                                              Nothing  -> Nothing             -- neither side has non-empty part

-- ** Parsers are functors:  @`fmap`@
instance   Functor (P  state) where 
  fmap f   (P  ap np l me)   =  let nnp =  fmap (fmap     f)  np
                                    nep =  f <$> me                                    
                                in  P (mkParser nnp nep) nnp l nep
  f <$     (P  ap np l me)   =  let nnp =  fmap (f <$)        np
                                    nep =  f <$   me                                    
                                in  P (mkParser nnp  nep) nnp l nep


-- ** Parsers are Applicative:  @`<*>`@,  @`<*`@,  @`*>`@ and  @`pure`@
instance   Applicative (P  state) where
  P ap np  pl pe <*> ~(P aq nq  ql qe)  =  let newnp = combine np pe aq nq (<*>) (<$>)
                                               newlp = nat_add pl ql
                                               newep = pe <*> qe
                                           in  P (mkParser newnp newep) newnp newlp newep
  P ap np pl pe  <*  ~(P aq nq  ql qe)   = let newnp = combine np pe aq nq (<*) (<$)
                                               newlp = nat_add pl ql
                                               newep = pe <* qe
                                           in  P (mkParser newnp newep) newnp newlp newep
  P ap np  pl pe  *>  ~(P aq nq ql qe)   = let newnp = combine np pe aq nq (*>)  (flip const)
                                               newlp = nat_add pl ql
                                               newep = pe *> qe
                                           in  P (mkParser newnp newep) newnp newlp newep
  pure a                                 = P (pure a) Nothing Zero (Just a)


 
-- ** Parsers are Alternative:  @`<|>`@ and  @`empty`@ 
instance   Alternative (P   state) where 
  P ap np  pl pe <|> P aq nq ql qe 
    =  let (rl, b) = trace' "calling natMin from <|>" (nat_min pl ql 0)
           Nothing `alt` q  = q
           p       `alt` Nothing = p
           Just p  `alt` Just q  = Just (p <|>q)
       in  let nnp =  (if b then (nq `alt` np) else (np `alt` nq))
               nep =  if b then trace' "calling pe" pe else trace' "calling qe" qe 
           in  P (mkParser nnp nep) nnp rl nep
  empty  =  P  empty empty  Infinite Nothing

-- ** An alternative for the Alternative, which is greedy:  @`<<|>`@
-- | `<<|>` is the greedy version of `<|>`. If its left hand side parser can make some progress that alternative is committed. Can be used to make parsers faster, and even
--   get a complete Parsec equivalent behaviour, with all its (dis)advantages. use with are!

instance ExtAlternative (P st) where
  P ap np pl pe <<|> P aq nq ql qe 
    = let (rl, b) = nat_min pl ql 0
          bestx :: Steps a -> Steps a -> Steps a
          bestx = if b then flip best else best
          choose:: T st a -> T st a -> T st a
          choose  (T ph pf pr)  (T qh qf qr) 
             = T  (\ k st -> let left  = norm (ph k st)
                             in if has_success left then left else left `bestx` qh k st)
                  (\ k st -> let left  = norm (pf k st)
                             in if has_success left then left else left `bestx` qf k st) 
                 (\ k st -> let left  = norm (pr k st)
                            in if has_success left then left else left  `bestx` qr k st)
      in   P (choose  ap aq )
             (maybe np (\nqq -> maybe nq (\npp -> return( choose  npp nqq)) np) nq)
             rl
             (pe <|> qe) -- due to the way Maybe is instance of Alternative  the left hand operator gets priority

-- ** Parsers can recognise single tokens:  @`pSym`@ and  @`pSymExt`@
--   Many parsing libraries do not make a distinction between the terminal symbols of the language recognised 
--   and the tokens actually constructed from the  input. 
--   This happens e.g. if we want to recognise an integer or an identifier: 
--   we are also interested in which integer occurred in the input, or which identifier. 
--   The function `pSymExt` takes as argument a value of some type `symbol', and returns a value of type `token'.
--   
--   The parser will in general depend on some 
--   state which holds the input. The functional dependency fixes the `token` type, 
--   based on the `symbol` type and the type of the parser `p`.

-- | Since `pSymExt' is overloaded both the type and the value of a symbol 
--   determine how to decompose the input in a `token` and the remaining input.
--   `pSymExt` takes two extra parameters: the first describing the minimal number of tokens recognised, 
--   and the second telling whether the symbol can recognise the empty string and the value which is to be returned in that case
  
pSymExt ::   (Provides state symbol token) => Nat -> Maybe token -> symbol -> P state token
pSymExt l e a  = P t (Just t) l e
                 where t = T ( \ k inp -> splitState a k inp)
                             ( \ k inp -> splitState a (\ t inp' -> push t (k inp')) inp)
                             ( \ k inp -> splitState a (\ _ inp' -> k inp') inp)

-- | @`pSym`@ covers the most common case of recognsiing a symbol: a single token is removed form the input, 
-- and it cannot recognise the empty string
pSym    ::   (Provides state symbol token) =>                       symbol -> P state token
pSym  s   = pSymExt (Succ Zero) Nothing s 


-- ** Parsers are Monads:  @`>>=`@ and  @`return`@
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Monads      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unParser_h :: P b a -> (a -> b -> Steps r) -> b -> Steps r
unParser_h (P (T  h   _  _ ) _ _ _ )  =  h

unParser_f :: P b a -> (b -> Steps r) -> b -> Steps (a, r)
unParser_f (P (T  _   f  _ ) _ _ _ )  =  f

unParser_r :: P b a -> (b -> Steps r) -> b -> Steps r
unParser_r (P (T  _   _  r ) _ _ _ )  =  r
          
-- !! do not move the P constructor behind choices/patern matches
instance  Monad (P st) where
       p@(P  ap np lp ep) >>=  a2q = 
          (P newap newnp (nat_add lp (error "cannot compute minimal length of right hand side of monadic parser")) newep)
          where (newep, newnp, newap) = case ep of
                                 Nothing -> (Nothing, t, maybe empty id t) 
                                 Just a  -> let  P aq nq lq eq = a2q a 
                                            in  (eq, combine t nq , t `alt` aq)
                Nothing  `alt` q    = q
                Just p   `alt` q    = p <|> q
                t = case np of
                    Nothing -> Nothing
                    Just (T h _ _  ) -> Just (T  (  \k -> h (\ a -> unParser_h (a2q a) k))
                                                 (  \k -> h (\ a -> unParser_f (a2q a) k))
                                                 (  \k -> h (\ a -> unParser_r (a2q a) k)))
                combine Nothing     Nothing     = Nothing
                combine l@(Just _ ) Nothing     =  l
                combine Nothing     r@(Just _ ) =  r
                combine (Just l)    (Just r)    = Just (l <|> r)
       return  = pure 


-- * Additional useful combinators
-- | The parsers build a list of symbols which are expected at a specific point. 
--   This list is used to report errors.
--   Quite often it is more informative to get e.g. the name of the non-terminal. 
--   The @`<?>`@ combinator replaces this list of symbols by it's righ-hand side argument.

(<?>) :: P state a -> String -> P state a
P  _  np  pl pe <?> label 
  = let nnp = case np of
              Nothing -> Nothing
              Just ((T ph pf  pr)) -> Just(T ( \ k inp -> replaceExpected (norm  ( ph k inp)))
                                             ( \ k inp -> replaceExpected (norm  ( pf k inp)))
                                             ( \ k inp -> replaceExpected (norm  ( pr k inp))))
        replaceExpected :: Steps a -> Steps a
        replaceExpected (Fail _ c) = (Fail [label] c)
        replaceExpected others     = others
    in P (mkParser nnp  pe) nnp pl pe


-- | `micro` inserts a `Cost` step into the sequence representing the progress the parser is making; for its use see `Text.ParserCombinators.UU.Examples` 
micro :: P state a -> Int -> P state a
P _  np  pl pe `micro` i  
  = let nnp = case np of
              Nothing -> Nothing
              Just ((T ph pf  pr)) -> Just(T ( \ k st -> ph (\ a st -> Micro i (k a st)) st)
                                             ( \ k st -> pf (Micro i .k) st)
                                             ( \ k st -> pr (Micro i .k) st))
    in P (mkParser nnp pe) nnp pl pe

--   For the precise functioning of the combinators we refer to the technical report mentioned in the README file
--   @`amb`@ converts an ambiguous parser into a parser which returns a list of possible recognitions.
amb :: P st a -> P st [a]
amb (P _  np  pl pe) 
 = let  combinevalues  :: Steps [(a,r)] -> Steps ([a],r)
        combinevalues lar  =   Apply (\ lar -> (map fst lar, snd (head lar))) lar
        nnp = case np of
              Nothing -> Nothing
              Just ((T ph pf  pr)) -> Just(T ( \k     ->  removeEnd_h . ph (\ a st' -> End_h ([a], \ as -> k as st') noAlts))
                                             ( \k inp ->  combinevalues . removeEnd_f $ pf (\st -> End_f [k st] noAlts) inp)
                                             ( \k     ->  removeEnd_h . pr (\ st' -> End_h ([undefined], \ _ -> k  st') noAlts)))
        nep = (fmap pure pe)
    in  P (mkParser nnp nep) nnp pl nep


-- | `getErrors` retreives the correcting steps made since the last time the function was called. The result can, 
--   using a monad, be used to control how to proceed with the parsing process.

class state `Stores`  error | state -> error where
  getErrors    ::  state   -> ([error], state)

-- | The class @`Stores`@ is used by the function @`pErrors`@ which retreives the generated correction spets since the last time it was called.
--
pErrors :: Stores st error => P st [error]
pErrors = let nnp = Just (T ( \ k inp -> let (errs, inp') = getErrors inp in k    errs    inp' )
                            ( \ k inp -> let (errs, inp') = getErrors inp in push errs (k inp'))
                            ( \ k inp -> let (errs, inp') = getErrors inp in            k inp' ))
              nep =  (Just (error "pErrors cannot occur in lhs of bind"))  -- the errors consumed cannot be determined statically!
          in P (mkParser nnp  Nothing) nnp Zero Nothing


-- | @`pPos`@ retreives the correcting steps made since the last time the function was called. The result can, 
--   using a monad, be used to control how to--    proceed with the parsing process.

class state `HasPosition`  pos | state -> pos where
  getPos    ::  state   -> pos

pPos :: HasPosition st pos => P st pos
pPos =  let nnp = Just ( T ( \ k inp -> let pos = getPos inp in k    pos    inp )
                       ( \ k inp -> let pos = getPos inp in push pos (k inp))
                       ( \ k inp -> let pos = getPos inp in           k inp ))
            nep =  Just (error "pPos cannot occur in lhs of bind")  -- the errors consumed cannot be determined statically!
        in P (mkParser nnp Nothing) nnp Zero Nothing

-- | The function `pEnd` should be called at the end of the parsing process. It deletes any unconsumed input, turning them into error messages

pEnd    :: (Stores st error, Eof st) => P st [error]
pEnd    = let nnp = Just ( T ( \ k inp ->   let deleterest inp =  case deleteAtEnd inp of
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
                                            in deleterest inp))
         in P (mkParser nnp  Nothing) nnp Zero Nothing
           

-- The function @`parse`@ shows the prototypical way of running a parser on a some specific input
-- By default we use the future parser, since this gives us access to partal result; future parsers are expected to run in less space.

parse :: (Eof t) => P t a -> t -> a
parse   (P (T _  pf _) _ _ _)  = fst . eval . pf  (\ rest   -> if eof rest then         Step 0 (Step 0 (Step 0 (Step 0 (error "ambiguous parser?"))))  
                                                               else error "pEnd missing?")
parse_h (P (T ph _  _) _ _ _)  = fst . eval . ph  (\ a rest -> if eof rest then push a (Step 0 (Step 0 (Step 0 (Step 0 (error "ambiguous parser?"))))) 
                                                                           else error "pEnd missing?") 

-- | @`pSwitch`@ takes the current state and modifies it to a different type of state to which its argument parser is applied. 
--   The second component of the result is a function which  converts the remaining state of this parser back into a valuee of the original type.
--   For the second argumnet to @`pSwitch`@  (say split) we expect the following to hold:
--   
-- >  let (n,f) = split st in f n to be equal to st

pSwitch :: (st1 -> (st2, st2 -> st1)) -> P st2 a -> P st1 a -- we require let (n,f) = split st in f n to be equal to st
pSwitch split (P _ np pl pe)    
   = let nnp = fmap (\ (T ph pf pr) ->T (\ k st1 ->  let (st2, back) = split st1
                                                     in ph (\ a st2' -> k a (back st2')) st2)
                                        (\ k st1 ->  let (st2, back) = split st1
                                                     in pf (\st2' -> k (back st2')) st2)
                                        (\ k st1 ->  let (st2, back) = split st1
                                                     in pr (\st2' -> k (back st2')) st2)) np
     in P (mkParser nnp pe) nnp pl pe

-- * Maintaining Progress Information
-- | The data type @`Steps`@ is the core data type around which the parsers are constructed.
--   It is a describes a tree structure of streams containing (in an interleaved way) both the online result of the parsing process,
--   and progress information. Recognising an input token should correspond to a certain amount of @`Progress`@, 
--   which tells how much of the input state was consumed. 
--   The @`Progress`@ is used to implement the breadth-first search process, in which alternatives are
--   examined in a more-or-less synchonised way. The meaning of the various @`Step`@ constructors is as follows:
--
--   [@`Step`@] A token was succesfully recognised, and as a result the input was 'advanced' by the distance  @`Progress`@
--
--   [@`Apply`@] The type of value represented by the `Steps` changes by applying the function parameter.
--
--   [@`Fail`@] A correcting step has to made to the input; the first parameter contains information about what was expected in the input, 
--   and the second parameter describes the various corrected alternatives, each with an associated `Cost`
--
--   [@`Micro`@] A small cost is inserted in the sequence, which is used to disambiguate. Use with care!
--
--   The last two alternatives play a role in recognising ambigous non-terminals. For a full description see the technical report referred to from the README file..

type Cost = Int
type Progress = Int
type Strings = [String]

data  Steps   a  where
      Step   ::                 Progress       ->  Steps a                             -> Steps   a
      Apply  ::  forall a b.    (b -> a)       ->  Steps   b                           -> Steps   a
      Fail   ::                 Strings        ->  [Strings   ->  (Cost , Steps   a)]  -> Steps   a
      Micro   ::                 Cost           ->  Steps a                             -> Steps   a
      End_h  ::                 ([a] , [a]     ->  Steps r)    ->  Steps   (a,r)       -> Steps   (a, r)
      End_f  ::                 [Steps   a]    ->  Steps   a                           -> Steps   a

succeedAlways :: Steps a
succeedAlways = let steps = Step 0 steps in steps

failAlways :: Steps a
failAlways  =  Fail [] [const (0, failAlways)]

noAlts :: Steps a
noAlts      =  Fail [] []

has_success :: Steps t -> Bool
has_success (Step _ _) = True
has_success _        = False 

-- ! @`eval`@ removes the progress information from a sequence of steps, and constructs the value embedded in it.
--   If you are really desparate to see how your parsers are making progress (e.g. when you have written an ambiguous parser, and you cannot find the cause of
--   the exponential blow-up of your parsing process, you may switch on the trace in the function @`eval`@
-- 
eval :: Steps   a      ->  a
eval (Step  n    l)     =   {- trace ("Step " ++ show n ++ "\n")-} (eval l)
eval (Micro  _    l)    =   eval l
eval (Fail   ss  ls  )  =   trace' ("expecting: " ++ show ss) (eval (getCheapest 3 (map ($ss) ls))) 
eval (Apply  f   l   )  =   f (eval l)
eval (End_f   _  _   )  =   error "dangling End_f constructor"
eval (End_h   _  _   )  =   error "dangling End_h constructor"

push        :: v -> Steps   r -> Steps   (v, r)
push v      =  Apply (\ r -> (v, r))

apply       :: Steps (b -> a, (b, r)) -> Steps (a, r)
apply       =  Apply (\(b2a, ~(b, r)) -> (b2a b, r)) 

pushapply   :: (b -> a) -> Steps (b, r) -> Steps (a, r)
pushapply f = Apply (\ (b, r) -> (f b, r)) 

-- | @`norm`@ makes sure that the head of the seqeunce contains progress information. It does so by pushing information about the result (i.e. the @Apply@ steps) backwards.
--
norm ::  Steps a ->  Steps   a
norm     (Apply f (Step   p    l  ))   =   Step  p (Apply f l)
norm     (Apply f (Micro  c    l  ))   =   Micro c (Apply f l)
norm     (Apply f (Fail   ss   ls ))   =   Fail ss (applyFail (Apply f) ls)
norm     (Apply f (Apply  g    l  ))   =   norm (Apply (f.g) l)
norm     (Apply f (End_f  ss   l  ))   =   End_f (map (Apply f) ss) (Apply f l)
norm     (Apply f (End_h  _    _  ))   =   error "Apply before End_h"
norm     steps                         =   steps

applyFail :: (c -> d) -> [a -> (b, c)] -> [a -> (b, d)]
applyFail f  = map (\ g -> \ ex -> let (c, l) =  g ex in  (c, f l))

-- | The function @best@ compares two streams
best :: Steps a -> Steps a -> Steps a
x `best` y =   norm x `best'` norm y

best' :: Steps   b -> Steps   b -> Steps   b
Fail  sl  ll     `best'`  Fail  sr rr     =   Fail (sl ++ sr) (ll++rr)
Fail  _   _      `best'`  r               =   r
l                `best'`  Fail  _  _      =   l
Step  n   l      `best'`  Step  m  r
    | n == m                              =   Step n (l `best'` r)     
    | n < m                               =   Step n (l  `best'`  Step (m - n)  r)
    | n > m                               =   Step m (Step (n - m)  l  `best'` r)
ls@(Step _  _)    `best'`  Micro _ _        =  ls
Micro _    _      `best'`  rs@(Step  _ _)   =  rs
ls@(Micro i l)    `best'`  rs@(Micro j r)  
    | i == j                               =   Micro i (l `best'` r)
    | i < j                                =   ls
    | i > j                                =   rs
End_f  as  l            `best'`  End_f  bs r          =   End_f (as++bs)  (l `best` r)
End_f  as  l            `best'`  r                    =   End_f as        (l `best` r)
l                       `best'`  End_f  bs r          =   End_f bs        (l `best` r)
End_h  (as, k_h_st)  l  `best'`  End_h  (bs, _) r     =   End_h (as++bs, k_h_st)  (l `best` r)
End_h  as  l            `best'`  r                    =   End_h as (l `best` r)
l                       `best'`  End_h  bs r          =   End_h bs (l `best` r)
l                       `best'`  r                    =   l `best` r 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% getCheapest  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

getCheapest :: Int -> [(Int, Steps a)] -> Steps a 
getCheapest _ [] = error "no correcting alternative found"
getCheapest n l  =  snd $  foldr (\(w,ll) btf@(c, l)
                               ->    if w < c   -- c is the best cost estimate thus far, and w total costs on this path
                                     then let new = (traverse n ll w c) 
                                          in if new < c then (new, ll) else btf
                                     else btf 
                               )   (maxBound, error "getCheapest") l


traverse :: Int -> Steps a -> Int -> Int  -> Int 
traverse 0  _            v c  =  trace' ("traverse " ++ show' 0 v c ++ " choosing" ++ show v ++ "\n") v
traverse n (Step _   l)  v c  =  trace' ("traverse Step   " ++ show' n v c ++ "\n") (traverse (n -  1 ) l (v-n) c)
traverse n (Micro _  l)  v c  =  trace' ("traverse Micro  " ++ show' n v c ++ "\n") (traverse n         l v     c)
traverse n (Apply _  l)  v c  =  {- trace' ("traverse Apply  " ++ show n ++ "\n")-} (traverse n         l v     c)
traverse n (Fail m m2ls) v c  =  trace' ("traverse Fail   " ++ show m ++ show' n v c ++ "\n") 
                                 (foldr (\ (w,l) c' -> if v + w < c' then traverse (n -  1 ) l (v+w) c'
                                                       else c') c (map ($m) m2ls)
                                 )
traverse n (End_h ((a, lf))    r)  v c =  traverse n (lf a `best` removeEnd_h r) v c
traverse n (End_f (l      :_)  r)  v c =  traverse n (l `best` r) v c

show' :: (Show a, Show b, Show c) => a -> b -> c -> String
show' n v c = "n: " ++ show n ++ " v: " ++ show v ++ " c: " ++ show c


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Handling ambiguous paths             %%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

removeEnd_h     :: Steps (a, r) -> Steps r
removeEnd_h (Fail  m ls             )  =   Fail m (applyFail removeEnd_h ls)
removeEnd_h (Step  ps l             )  =   Step  ps (removeEnd_h l)
removeEnd_h (Apply f l              )  =   error "not in history parsers"
removeEnd_h (Micro c l              )  =   Micro c (removeEnd_h l)
removeEnd_h (End_h  (as, k_st  ) r  )  =   k_st as `best` removeEnd_h r 

removeEnd_f      :: Steps r -> Steps [r]
removeEnd_f (Fail m ls)        =   Fail m (applyFail removeEnd_f ls)
removeEnd_f (Step ps l)        =   Step ps (removeEnd_f l)
removeEnd_f (Apply f l)        =   Apply (map' f) (removeEnd_f l) 
                                   where map' f ~(x:xs)  =  f x : map f xs
removeEnd_f (Micro c l      )  =   Micro c (removeEnd_f l)
removeEnd_f (End_f(s:ss) r)    =   Apply  (:(map  eval ss)) s 
                                                 `best`
                                          removeEnd_f r

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Auxiliary Functions and Types        %%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- * Auxiliary functions and types
-- ** Checking for non-sensical combinations: @`must_be_non_empty`@ and @`must_be_non_empties`@
-- | The function checks wehther its second argument is a parser which can recognise the mety sequence. If so an error message is given
--   using the name of the context. If not then the third argument is returned. This is useful in testing for loogical combinations. For its use see
--   the module Text>parserCombinators.UU.Derived

must_be_non_empty :: [Char] -> P t t1 -> t2 -> t2
must_be_non_empty msg p@(P _ _ Zero _) _ 
            = error ("The combinator " ++ msg ++  " requires that it's argument cannot recognise the empty string\n")
must_be_non_empty _ _  q  = q

-- | This function is similar to the above, but can be used in situations where we recognise a sequence of elements separated by other elements. This does not 
--   make sense if both parsers can recognise the empty string. Your grammar is then highly ambiguous.

must_be_non_empties :: [Char] -> P t1 t -> P t3 t2 -> t4 -> t4
must_be_non_empties  msg (P _ _ Zero _) (P _ _ Zero _ ) _ 
            = error ("The combinator " ++ msg ++  " requires that not both arguments can recognise the empty string\n")
must_be_non_empties  msg _  _ q = q


-- ** The type @`Nat`@ for describing the minimal number of tokens consumed
-- | The data type @`Nat`@ is used to represent the minimal length of a parser.
--   Care should be taken in order to not evaluate the right hand side of the binary function @`nat-add`@ more than necesssary.

data Nat = Zero
         | Succ Nat
         | Infinite
         deriving  Show

nat_min :: Nat -> Nat -> Int -> (Nat, Bool)
nat_min _          Zero      _  = trace' "Right Zero in nat_min\n"    (Zero, False)
nat_min Zero       _         _  = trace' "Left Zero in nat_min\n"     (Zero, True)
nat_min Infinite   r         _  = trace' "Left Infinite in nat_min\n" (r,    False) 
nat_min l          Infinite  _  = trace' "Right Infinite in nat_min\n"    (l,    True) 
nat_min (Succ ll)  (Succ rr) n  = if n > 1000 then error "problem with comparing lengths" 
                                  else trace' ("Succ in nat_min " ++ show n ++ "\n")         (let (v, b) = nat_min ll  rr (n+1) in (Succ v, b))

nat_add :: Nat -> Nat -> Nat
nat_add Infinite  _ = trace' "Infinite in add\n" Infinite
nat_add Zero      r = trace' "Zero in add\n"     r
nat_add (Succ l)  r = trace' "Succ in add\n"     (Succ (nat_add l r))

get_length :: P a b -> Nat
get_length (P _ _  l _) = l

trace' :: a -> b -> b
trace' m v = {-  trace m  -} v 






