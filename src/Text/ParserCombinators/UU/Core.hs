-- | The module `Core` contains the basic functionality of the parser library. 
-- It takes care of the breadth-first search, the online generation of results, the core error
-- correction administration, dealing with ambigous grammars, and the type for both kinds of parsers
-- involved and the recognisers.
 
{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction,
              TypeFamilies#-}


module Text.ParserCombinators.UU.Core ( module Text.ParserCombinators.UU.Core
                                              , module Control.Applicative) where
import Control.Applicative  hiding ((<*), (*>), (<$), many, some, optional)
import Char
import Debug.Trace
import Maybe

{-
infixl  4  <*, *>
infixl  4  <$
-}
-- * The Classes Defining the Interface
-- ** `IsParser`


-- | This class collects a number of classes which together defines what a Parser should provide. 
-- Since it is just a predicate we have prefixed the name by the phrase `Is'

class    (Applicative p, ExtApplicative p, Alternative p, Greedy p)    => IsParser p where
instance (Applicative p, ExtApplicative p, Alternative p, Greedy p)    => IsParser p where

infixl  4  <*, *>
infixl  4  <$

-- ** `ExtApplicative'
-- | The module "Control.Applicative" contains definitions for `<$`, `*>`  and `<*` which cannot be changed. Since we want to give
-- optimised implementations of these combinators, we hide those definitions, and define a class containing their signatures.

class  ExtApplicative p where
  (<*)      ::  p  a            -> p b   ->   p  a
  (*>)      ::  p  b            -> p a   ->   p  a
  (<$)      ::  a               -> p b   ->   p  a

-- ** `Greedy`
-- | In many cases there is a considerable performance gain if we can indicate which alternative should take priority 
-- in case both alternatives can make progress; if we have the rule S -> aS | epsilon, we usually want to continue recognising a's as long as possible. 
-- in such a case we use `<<|>`, to indicate that the left operand takes priority. 
class  Greedy p where 
  (<<|>) :: p a -> p a -> p a

-- ** `Symbol'
-- | Many parsing libraries do not make a distinction between the terminal symbols of the language recognised and the 
-- tokens actually constructed from the  input. This happens e.g. if we want to recognise an integer or an identifier: we are also interested in which integer occurred in the input, or which identifier.

class  Symbol p  symbol token | p symbol -> token where
  pSym  ::  symbol -> p token
-- ^ The function `pSym` takes as argument a value of some type `symbol', and returns a value of type `token'. The parser will in general depend on some 
-- state which is maintained holding the input. The functional dependency fixes the `token` type, based on the `symbol` type and the type of the parser `p`.
-- Since `pSym' is overloaded both the type and the value of symbol determine how to decompose the input in a `token` and the remaining input.

type Strings = [String]



class  Provides state symbol token | state symbol -> token  where
       splitState   ::  symbol -> (token -> state  -> Steps a) -> state -> Steps a

class Eof state where
       eof          ::  state   -> Bool
       deleteAtEnd  ::  state   -> Maybe (Cost, state)

class  Parse p  where
       parse  ::   Eof state => p state a -> state -> a

-- * Progress Information
-- | The data type `Steps` is the core data type around which the parsers are constructed. It is a stream containing both the result of the parsing process,
--   albeit often in a fragmented way, and progress information. Recognising a token should correspond to a certain amount of `Progress`, 
--   which for the time being in an `Int`.
--
--   [@`Step`@] A token was succesfully recognised, and as a result the input was 'advanced' by `Progress`
--
--   [@`Apply`@] The type of value represented by the `Steps` changes by applying the function parameter.
--
--   [@`Fail`@] A correcting step has to made to the input; the first parameter contains the error messages coresponding to the possible
--   correcting steps, and the second parameter generated the various corrected alternatives, each with an associated `Cost`
--
--   The last two alternatives play a role in recognising ambigous non-terminals. For a full description see the technical report.

type Cost = Int
type Progress = Int

data  Steps   a  where
      Step   ::              Progress       ->  Steps a                                -> Steps   a
      Apply  ::  forall b.   (b -> a)       ->  Steps   b                              -> Steps   a

      Fail   ::              Strings        ->  [Strings   ->     (Cost , Steps   a)]  -> Steps   a

      End_h  ::              ([a] , [a] -> Steps r)        ->  Steps   (a,r)           -> Steps   (a, r)
      End_f  ::              [Steps   a]   ->  Steps   a                               -> Steps   a
{-

failAlways  =  Fail [] [const ((0, failAlways))]
noAlts      =  Fail [] []

eval :: Steps   a      ->  a
eval (Step  _    l)     =   eval l
eval (Fail   ss  ls  )  =   eval (getCheapest 3 (map ($ss) ls) 
eval (Apply  f   l   )  =   f (eval l)
eval (End_f   _  _   )  =   error "dangling End_f constructor"
eval (End_h   _  _   )  =   error "dangling End_h constructor"

push    :: v -> Steps   r -> Steps   (v, r)
push v  =  Apply (\ r -> (v, r))
apply   :: Steps (b -> a, (b, r)) -> Steps (a, r)
apply   =  Apply (\(b2a, ~(b, r)) -> (b2a b, r))  

norm ::  Steps a ->  Steps   a
norm     (Apply f (Step   p    l  ))   =   Step p (Apply f l)
norm     (Apply f (Fail   ss   ls ))   =   Fail ss (applyFail (Apply f) ls)
norm     (Apply f (Apply  g    l  ))   =   norm (Apply (f.g) l)
norm     (Apply f (End_f  ss   l  ))   =   End_f (map (Apply f) ss) (Apply f l)
norm     (Apply f (End_h  _    _  ))   =   error "Apply before End_h"
norm     steps                         =   steps

applyFail f  = map (\ g -> \ ex -> let (c, l) =  g ex in  (c, f l))

best :: Steps   a -> Steps   a -> Steps   a
x `best` y =   norm x `best'` norm y

best' :: Steps   b -> Steps   b -> Steps   b
Fail  sl  ll     `best'`  Fail  sr rr     =   Fail (sl ++ sr) (ll++rr)
Fail  _   _      `best'`  r               =   r
l                `best'`  Fail  _  _      =   l
Step  n   l      `best'`  Step  m  r
    | n == m                              =   Step n (l `best'` r)     
    | n < m                               =   Step n (l  `best'`  Step (m - n)  r)
    | n > m                               =   Step m (Step (n - m)  l  `best'` r)
End_f  as  l            `best'`  End_f  bs r     =   End_f (as++bs)  (l `best` r)
End_f  as  l            `best'`  r               =   End_f as        (l `best` r)
l                       `best'`  End_f  bs r     =   End_f bs        (l `best` r)
End_h  (as, k_h_st)  l  `best'`  End_h  (bs, _) r     =   End_h (as++bs, k_h_st)  (l `best` r)
End_h  as  l            `best'`  r               =   End_h as (l `best` r)
l                       `best'`  End_h  bs r     =   End_h bs (l `best` r)
l                       `best'`  r               =   l `best` r 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% getCheapest  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- The function 
getCheapest :: Int -> [(Int, Steps a)] -> Steps a 
getCheapest _ [] = error "no correcting alternative found"
getCheapest n l  =  snd $  foldr (\(w,ll) btf@(c, l)
                               ->    if w < c 
                                     then let new = (traverse n ll w c) 
                                          in if new < c then (new, ll) else btf
                                     else btf 
                               )   (maxBound, error "getCheapest") l


traverse :: Int -> Steps a -> Int -> Int  -> Int 
traverse 0  _               =  \ v c ->  v
traverse n (Step _  l)      =  traverse (n -  1 ) l
traverse n (Apply _ l)      =  traverse n         l
traverse n (Fail m m2ls)    =  \ v c ->  foldr (\ (w,l) c' -> if v + w < c' then traverse (n -  1 ) l (v+w) c'
                                                                            else c'
                                               ) c (map ($m) m2ls)
traverse n (End_h ((a, lf))    r)  =  traverse n (lf a `best` removeEnd_h r)
traverse n (End_f (l      :_)  r)  =  traverse n (l `best` r)   


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% History     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- do not change into data, or be prepared to add ~ at subtle places !!
newtype  P_h    st  a =  P_h  (forall r . (a  -> st -> Steps r)  -> st -> Steps r)
unP_h (P_h p) = p

instance   Functor (P_h  state) where 
  fmap f      (P_h p)  =  P_h  (\  k -> p (\a -> k (f a))) 

instance   Applicative (P_h  state) where
  (P_h p) <*> (P_h q)  =  P_h  (\  k -> p (\ f -> q (\ a -> k (f a))))  
  pure a               =  P_h  (\  k -> k a)

instance   Alternative (P_h  state) where 
  (P_h p) <|> (P_h q)  =  P_h  (\  k inp  -> p k inp `best` q k inp) 
  empty                =  P_h  (\  k -> const noAlts) 

instance  ( Provides state symbol token) => Symbol (P_h  state) symbol token where
  pSym a =  P_h (splitState a)

data Id a = Id a deriving Show

instance   Parse P_h  where
  parse (P_h p)
   =  fst . eval . p  (\ a rest -> if eof rest then push a failAlways else error "pEnd missing?") 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Future      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- do not change into data !!
newtype  P_f st a  = P_f (forall r . (st -> Steps   r) -> st -> Steps   (a, r))
unP_f (P_f p) = p

instance  Functor (P_f st) where
 fmap f (P_f p)     =  P_f (\k inp ->  Apply (\(a,r) -> (f a, r)) (p k inp)) -- \pure f <*> p

instance Applicative (P_f st) where
 P_f p  <*>  P_f q  =   P_f ( (apply .) . (p .q)) 
 pure a             =   P_f ((push a).)

instance Alternative (P_f st) where
 P_f p  <|>  P_f q  =   P_f (\ k inp  -> p k inp `best` q k inp)  
 empty              =   P_f (\ k inp  -> noAlts)


instance  (Provides state symbol token) =>  Symbol (P_f  state) symbol token where
  pSym a =  P_f (\ k inp-> splitState a (\ t inp' -> push t (k inp')) inp)

instance  Parse P_f  where
  parse (P_f p) =  fst . eval . p (\ rest -> if eof rest then failAlways else error "pEnd missing")

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Monads      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

infixr 1 >>>=
class GenMonad  m_1 m_2 where
   (>>>=) :: m_1 b -> ( b -> m_2  a) -> m_2 a

instance     Monad (P_h  state) 
         =>  GenMonad (P_h  state) (P_h state) where
  (>>>=)  = (>>=) --  the monadic bind defined before

instance GenMonad (P_h  state) (P_f  state) where
  (P_h p)  >>>= pv2q 
           = P_f (\ k st -> p (\ pv st -> unP_f (pv2q pv) k st) st)

newtype Parser state a = Parser (P_h  state a, P_f state a, R state a) 
unParser_h (Parser  (P_h h,  _    , _  ))  =  h
unParser_f (Parser  (_    ,  P_f f, _  ))  =  f
unParser_r (Parser  (_    ,  _    , R r))  =  r

instance  (   Functor (P_h  st), Functor (P_f  st), Functor (R st)) 
          =>  Functor (Parser  st) where
 fmap f  (Parser (hp, fp, fr))  = Parser  (fmap f hp, fmap f fp, fmap f fr)      

instance  (   Applicative (P_h  st), Applicative (P_f  st), Applicative (R st)) 
          =>  Applicative (Parser  st) where
 Parser (hp, fp, rp)  <*> ~(Parser (hq, fq, rq))    = Parser  (hp <*> hq, fp <*> fq, rp <*> rq )
 pure a                                        = Parser  (pure a, pure a, pure a)       

instance  (   Alternative (P_h  st), Alternative (P_f  st), Alternative (R st)) 
          =>  Alternative (Parser  st) where 
 Parser (hp, fp, rp)  <|> Parser (hq, fq, rq)    = Parser  (hp <|> hq, fp <|> fq, rp <|> rq)
 empty                                     = Parser  (empty    , empty    , empty)       

instance  (Provides state symbol token)  => Symbol (Parser state) symbol token where
  pSym a =  Parser (pSym a, pSym a, pSym a)

instance   Parse Parser  where
  parse (Parser (_, (P_f fp), _))  
      =  fst . eval. fp (\ rest -> if eof rest  then failAlways else error "End_fmissing?") 

instance Applicative (P_h state) => Monad (P_h state) where
  P_h p >>= a2q  = P_h ( \ k -> p (\ a -> unP_h (a2q a) k))
  return     = pure

instance Applicative (Parser st) => Monad (Parser st) where
     Parser  (P_h p, _, _)  >>=  a2q = 
           Parser  (  P_h   (\k -> p (\ a -> unParser_h (a2q a) k))
                ,  P_f   (\k -> p (\ a -> unParser_f (a2q a) k))
                ,  R     (\k -> p (\ a -> unParser_r (a2q a) k))
                )
     return  = pure 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Recognisers           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
type family State p :: *

newtype  R st a  = R (forall r . (st -> Steps   r) -> st -> Steps r)
unR (R p) = p

instance Functor (R st) where
 fmap f  (R r)       =  R r

instance Applicative (R st) where
 R p  <*>  R q   =   R (p.q)  
 pure    a       =   R (id)

instance Alternative (R st) where
 R p  <|>  R q   =   R (\ k inp  -> p k inp `best` q k inp)  
 empty           =   R (\ k inp  -> noAlts)

instance  (Provides state symbol token) =>  Symbol (R  state) symbol token where
  pSym a =  R (\k inp ->  splitState a (\ v inp' -> k inp') inp) 



type instance State (P_f st) = st
type instance State (P_h st) = st
type instance State (Parser st) = st

{-

class StateOf p st | p -> st

instance StateOf (P_h st) st
instance StateOf (P_h st) st
instance StateOf (P_h st) st
-}

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Greedy      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_gr :: Steps a -> Steps a -> Steps a

l@  (Step _ _)   `best_gr` _  = l
l                `best_gr` r  = l `best` r


instance Greedy (P_h state)  where
  P_h p <<|> P_h q = P_h (\ k st  -> norm (p k st) `best_gr` norm (q k st))

instance Greedy (P_f state)  where
  P_f p <<|> P_f q = P_f (\ k st  -> norm (p k st) `best_gr` norm (q k st))

instance Greedy (Parser state) where
    Parser (hp, fp)  <<|> Parser (hq, fq) = Parser  (hp <<|> hq, fp <<|> fq) 


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Ambiguous   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class Ambiguous p where
 amb :: p a -> p [a]

instance Ambiguous (P_h state) where
  amb (P_h p) = P_h ( \k ->  removeEnd_h . p (\ a st' -> End_h ([a], \ as -> k as st') noAlts))
removeEnd_h     :: Steps (a, r) -> Steps r
removeEnd_h (Fail  m ls             )  =   Fail m (applyFail removeEnd_h ls)
removeEnd_h (Step  ps l             )  =   Step  ps (removeEnd_h l)
removeEnd_h (Apply f l              )  =   error "not in history parsers"
removeEnd_h (End_h  (as, k_st  ) r  )  =   k_st as `best` removeEnd_h r 


instance Ambiguous (P_f state) where
  amb (P_f p) = P_f (\k inp -> combinevalues . removeEnd_f $ p (\st -> End_f [k st] noAlts) inp)
removeEnd_f      :: Steps r -> Steps [r]
removeEnd_f (Fail m ls)        =   Fail m (applyFail removeEnd_f ls)
removeEnd_f (Step ps l)        =   Step ps (removeEnd_f l)
removeEnd_f (Apply f l)        =   Apply (map' f) (removeEnd_f l)
removeEnd_f (End_f(s:ss) r)    =   Apply  (:(map  eval ss)) s 
                                                 `best`
                                          removeEnd_f r

combinevalues  :: Steps [(a,r)] -> Steps ([a],r)
combinevalues lar           =   Apply (\ lar -> (map fst lar, snd (head lar))) lar
map' f ~(x:xs)              =   f x : map f xs

instance (Ambiguous (P_h state), Ambiguous (P_f state), Ambiguous (R state)) => Ambiguous (Parser state) where
  amb  (Parser (hp, fp))  = Parser (amb hp, amb fp, error "Ambiguous for recognisers not defined yet")
       

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% pErrors     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class state `Stores`  errors where
  getErrors    ::  state   -> (errors, state)

class  p `AsksFor` errors where
  pErrors :: p errors
  pEnd    :: p errors

instance (Eof state, Stores state errors) =>  AsksFor (P_h state) errors where
  pErrors = P_h (\ k inp -> let (errs, inp') = getErrors inp
                            in k errs inp')
  pEnd    = P_h (\ k inp -> let deleterest inp =  case deleteAtEnd inp of
                                                  Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                             in k  finalerrors finalstate
                                                  Just (i, inp') -> Fail []  [const ((i,  deleterest inp'))]
                             in deleterest inp
                )

instance (Eof state, Stores state errors) => AsksFor (P_f state) errors where
  pErrors = P_f (\ k   inp -> let (errs, inp') = getErrors inp
                              in push errs (k inp'))
  pEnd    = P_f (\ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in push finalerrors (k finalstate)
                                                    Just (i, inp') -> Fail [] [const ((i, deleterest inp'))]
                              in deleterest inp
                )

instance (Eof state, Stores state errors) => AsksFor (R state) errors where
  pErrors = P_f (\ k   inp -> let (errs, inp') = getErrors inp
                              in  (k inp'))
  pEnd    = P_f (\ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in  (k finalstate)
                                                    Just (i, inp') -> Fail [] [const ((i, deleterest inp'))]
                              in deleterest inp
                )

instance  (state `Stores` errors, Eof state) => AsksFor (Parser state)  errors where
  pErrors   = Parser  (pErrors,  pErrors, pErrors)
  pEnd      = Parser  (pEnd,     pEnd,    pEnd)

{-
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Microsteps  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


class MicroStep result where
  microstep :: result a -> result a

instance MicroStep Steps where
   microstep steps = Micro steps

class Micro p where
  micro :: p a -> p a

instance  Micro (P_f  st) where
  micro (P_f p) = P_f (\k st -> microstep ( p k st ) )
-}

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% State Change          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class Switch p where
  pSwitch :: (st1 -> (st2, st2 -> st1)) -> p st2 a -> p st1 a

instance Switch P_h where
  pSwitch split (P_h p) = P_h  (\ k st1 ->  let (st2, back) = split st1
                                            in p (\ a st2' -> k a (back st2')) st2)

instance Switch P_f where
  pSwitch split (P_f p) = P_f  (\k st1 ->  let (st2, back) = split st1
                                           in p (\st2' -> k (back st2')) st2)

instance Switch Parser where
  pSwitch split (Parser (p, q, r)) = Parser (pSwitch split p, pSwitch split q, pSwitch split r)




instance ExtApplicative (P_h st)  where
  P_h p <* R r     = P_h ( p. (r.)) 
  R   r *> P_h p   = P_h ( r .p   )
  f     <$  R r    = P_h ( r . ($f))

instance ExtApplicative (P_f st) where
  P_f p <* R r     = P_f (\ k st -> p (r k) st)
  R   r *> P_f p   = P_f (\ k st -> r (p k) st)
  f     <$  R r    = P_f (\ k st -> push f (r k st))

instance  (ExtApplicative (P_h  st), ExtApplicative (P_f  st))
          =>  ExtApplicative (Parser  st)  where
  Parser (P_h hp, P_f fp, R rp)  <*  Parser (P_h hq, P_f fq, R rq)  = Parser  ( P_h ( ph . (rq.))
                                                                              , P_f ( fp .rq    )
                                                                              , R   ( rp.rq     ) 
                                                                              )

  r                    *>  Parser (hq, fq, rq)  = Parser  (r  *> hq , r *> fq)
  f                    <$  r               = Parser  (f  <$ r, f <$ r)       
 

-}