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
import Data.BreadthFirstSearch
import Char
import Debug.Trace
import Maybe

infix   2  <?>    -- should be the last element in a sequence of alternatives
infixl  3  <<|>   -- intended use p <<|> q <<|> r <|> x <|> y <?> z

-- * The triples containing a history parser, a future parser and a recogniser: @`T`@
-- The history parser part is to be used in the left hand side of a monad in order to avoid 
-- a potential comflict in case the error recovery needs access to the steps produced by the right
-- hand side. The parsers inside @`T`@ is where the actual work is done
data T st a  = T  (forall r . (a  -> st -> Steps r)  -> st -> Steps       r  ) --  history parser
                  (forall r . (      st -> Steps r)  -> st -> Steps   (a, r) ) --  future parser
                  (forall r . (      st -> Steps r)  -> st -> Steps       r  ) --  recogniser

-- ** We want to have access to the individual parsers in  a triple
class UnParser p where
  unParser_h  :: p a ->  (forall r . (a  -> st -> Steps r)  -> st -> Steps       r  )
  unParser_f  :: p a ->  (forall r . (      st -> Steps r)  -> st -> Steps   (a, r) )
  unParser_r  :: p a ->  (forall r . (      st -> Steps r)  -> st -> Steps       r  ) 

instance UnParser p where
  unParser_h (T  h  _  _ )   =  h
  unParser_f (T  _  f  _ )   =  f
  unParser_r (T  _  _  r )   =  r


-- ** @T@ is a functor
instance Functor (T st) where
  fmap f (T ph pf pr) = T  ( \  k -> ph ( k .f ))
                           ( \  k ->  pushapply f . pf k) -- pure f <*> pf
                           pr
  f <$ (T _ _ pr)     = T  ( pr . ($f)) 
                           ( \ k st -> push f ( pr k st)) 
                           pr

-- ** @T@ is Applicative:  @`<*>`@,  @`<*`@,  @`*>`@ and  @`pure`@
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


instance Monad (T state) where
  T ph _ _ >>= q = T (  \k -> h (\ a -> unParser_h (a2q a) k))
                     (  \k -> h (\ a -> unParser_f (a2q a) k))
                     (  \k -> h (\ a -> unParser_r (a2q a) k)))


instance ExtAlternative (T state) where
  p <<|> q        = error "T is not an instance of ExtAlternative since when performing erro correction we may need to flip the arguments"


instance ExtAlternative Maybe where
  Nothing <<|> r        = r
  l       <<|> Nothing  = l 
  l       <<|> r        = l -- choosing the high priority alternative ? is this the right choice?


-- * The  descriptor @`P`@ of a parser, including the tupled parser corresponding to this descriptor
--
data  P   st  a =  P  (T  st a)         --   actual parsers
                      (Maybe (T st a))  --   non-empty or dynamic parsers; Nothing if  they are absent
                      Nat               --   minimal length
                      (Maybe a)         --   possibly empty with static value 

instance Show (P st a) where
  show (P _ nt n e) = "P _ " ++ maybe "Nothing" (const "(Just _)") nt ++ " (" ++ show n ++ ") " ++ maybe "Nothing" (const "(Just _)") e

getOneP (P _ (Just _)  Zero _ )    =  error "The element is a special parser which cannot be combined"
getOneP (P _ Nothing   l    _ )    =  Nothing
getOneP (P _ onep      l    ep )   =  Just( P (mkParser onep Nothing)  onep l Nothing)
getZeroP (P _ _ l Nothing)         =  Nothing
getZeroP (P _ _ l pe)              =  Just (P (mkParser Nothing pe) Nothing l pe) -- TODO check for erroneous parsers

mkParser np@Nothing   ne@Nothing   =  empty           
mkParser np@(Just nt) ne@Nothing   =  nt              
mkParser np@Nothing   ne@(Just a)  =          (pure a)        
mkParser np@(Just nt) ne@(Just a)  =  (nt <|> pure a) 

-- combine creates the non-empty parser 
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
pSymExt l e a  = P (mkParser t e) (Just t) l e
                 where t = T ( \ k inp -> splitState a k inp)
                             ( \ k inp -> splitState a (\ t inp' -> push t (k inp')) inp)
                             ( \ k inp -> splitState a (\ _ inp' -> k inp') inp)

-- | @`pSym`@ covers the most common case of recognsiing a symbol: a single token is removed form the input, 
-- and it cannot recognise the empty string
pSym    ::   (Provides state symbol token) =>  symbol -> P state token
pSym  s   = pSymExt (Succ Zero) Nothing s 


-- ** Parsers are Monads:  @`>>=`@ and  @`return`@
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Monads      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unParser_h (P (T  h   _  _ ) _ _ _ )  =  h
unParser_f (P (T  _   f  _ ) _ _ _ )  =  f
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
              Just ((T ph pf  pr)) -> Just(T ( \ k inp -> replaceExpected  ( ph k inp))
                                             ( \ k inp -> replaceExpected  ( pf k inp))
                                             ( \ k inp -> replaceExpected  ( pr k inp)))
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


-- ** The type @`Nat`@ for describing the minimal number of tokens consumed
-- | The data type @`Nat`@ is used to represent the minimal length of a parser.
--   Care should be taken in order to not evaluate the right hand side of the binary function @`nat-add`@ more than necesssary.

data Nat = Zero
         | Succ Nat
         | Infinite
         deriving  (Show, Eq)

instance Num Nat  where
    (+)            = nat_add
                     where  nat_add Infinite  _ = trace' "Infinite in add\n" Infinite
                            nat_add Zero      r = trace' "Zero in add\n"     r
                            nat_add (Succ l)  r = trace' "Succ in add\n"     (Succ (nat_add l r))
    (-)             = error "subtraction not defined for nat"
    (*) Zero n      = n
    (*) (Succ n) m  = n + n * m
    (*) Infinite    = error "cannot multiply by Infinite Nat" 
    negate          = error "negation not defined for nat"
    abs n           = n
    signum  Zero    = Zero
    signum (Succ _) = Succ Zero
    fromInteger n   = if n>0 then Succ (fromInteger (n-1)
                      else if n==0 then Zero
                           else " cannot make a natural number from a negative number"


nat_min _          Zero      _  = trace' "Right Zero in nat_min\n"    (Zero, False)
nat_min Zero       _         _  = trace' "Left Zero in nat_min\n"     (Zero, True)
nat_min Infinite   r         _  = trace' "Left Infinite in nat_min\n" (r,    False) 
nat_min l          Infinite  _  = trace' "Right Infinite in nat_min\n"    (l,    True) 
nat_min (Succ ll)  (Succ rr) n  = if n > 1000 then error "problem with comparing lengths" 
                                  else trace' ("Succ in nat_min " ++ show n ++ "\n")         (let (v, b) = nat_min ll  rr (n+1) in (Succ v, b))



get_length  (P _ _  l _) = l
set_length ~(P a n _  e) l = P a n l e  

trace' m v = {- trace m -} v 






