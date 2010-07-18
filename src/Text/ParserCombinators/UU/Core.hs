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
              NoMonomorphismRestriction #-}


module Text.ParserCombinators.UU.Core ( module Text.ParserCombinators.UU.Core
                                              , module Control.Applicative) where
import Control.Applicative  hiding ((<*), (*>), (<$), many, some, optional)
import Char
import Debug.Trace
import Maybe

-- * The Classes Defining the Interface
-- ** `IsParser`

trace' v m = m

-- | This class collects a number of classes which together defines what a `Parser` should provide. 
-- Since it is just a predicate we have prefixed the name by the phrase `Is'

class    (Applicative p, ExtApplicative p, Alternative p)    => IsParser p where
instance (Applicative p, ExtApplicative p, Alternative p)    => IsParser p where

infixl  4  <*, *>
infixl  4  <$
infix   2  <?>

-- ** `ExtApplicative'
-- | The module "Control.Applicative" contains definitions for `<$`, `*>`  and `<*` which cannot be changed. Since we want to give
-- optimised implementations of these combinators, we hide those definitions, and define a class containing their signatures.

class  ExtApplicative p where
  (<*)      ::  p  a            -> p b   ->   p  a
  (*>)      ::  p  b            -> p a   ->   p  a
  (<$)      ::  a               -> p b   ->   p  a

-- ** `Symbol'
-- | Many parsing libraries do not make a distinction between the terminal symbols of the language recognised and the 
-- tokens actually constructed from the  input. This happens e.g. if we want to recognise an integer or an identifier: we are also interested in which integer occurred in the input, or which identifier. Note that if the alternative later fails repair will take place, instead of trying the other altrenatives at the greedy choice point.

class  Symbol p  symbol token | p symbol -> token where
  pSym  ::  symbol -> p token
-- ^ The function `pSym` takes as argument a value of some type `symbol', and returns a value of type `token'. The parser will in general depend on some 
-- state which is maintained holding the input. The functional dependency fixes the `token` type, based on the `symbol` type and the type of the parser `p`.
-- Since `pSym' is overloaded both the type and the value of symbol determine how to decompose the input in a `token` and the remaining input.

-- ** `Provides'

class  Provides state symbol token | state symbol -> token  where
       splitState   ::  symbol -> (token -> state  -> Steps a) -> state -> Steps a

-- ** `Eof'

class Eof state where
       eof          ::  state   -> Bool
       deleteAtEnd  ::  state   -> Maybe (Cost, state)

-- * Progress Information
-- | The data type `Steps` is the core data type around which the parsers are constructed. It is a stream containing both the result of the parsing process,
--   albeit often in a fragmented way, and progress information. Recognising a token should correspond to a certain amount of `Progress`, 
--   which for the time being in an `Int`.
--
--   [@`Step`@] A token was succesfully recognised, and as a result the input was 'advanced' by the distance  `Progress`
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
      Step   ::                 Progress       ->  Steps a                             -> Steps   a
      Cost   ::                 Cost           ->  Steps a                             -> Steps   a
      Apply  ::  forall a b.    (b -> a)       ->  Steps   b                           -> Steps   a
      Fail   ::                 Strings        ->  [Strings   ->  (Cost , Steps   a)]  -> Steps   a
      End_h  ::                 ([a] , [a]     ->  Steps r)    ->  Steps   (a,r)       -> Steps   (a, r)
      End_f  ::                 [Steps   a]    ->  Steps   a                           -> Steps   a

succeedAlways = let steps = Step 0 steps in steps
failAlways  =  Fail [] [const (0, failAlways)]
noAlts      =  Fail [] []

eval :: Steps   a      ->  a
eval (Step  _    l)     =   eval l
eval (Cost  _    l)     =   eval l
eval (Fail   ss  ls  )  =   trace' ("expecting: " ++ show ss) (eval (getCheapest 3 (map ($ss) ls))) 
eval (Apply  f   l   )  =   f (eval l)
eval (End_f   _  _   )  =   error "dangling End_f constructor"
eval (End_h   _  _   )  =   error "dangling End_h constructor"

push    :: v -> Steps   r -> Steps   (v, r)
push v  =  Apply (\ r -> (v, r))
apply   :: Steps (b -> a, (b, r)) -> Steps (a, r)
apply   =  Apply (\(b2a, ~(b, r)) -> (b2a b, r))  

norm ::  Steps a ->  Steps   a
norm     (Apply f (Step   p    l  ))   =   Step p (Apply f l)
norm     (Apply f (Cost   c    l  ))   =   Cost c (Apply f l)
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
ls@(Step _  _)   `best'`  Cost _ _        =  ls
Cost _    _      `best'`  rs@(Step  _ _)  =  rs
ls@(Cost i l)    `best'`  rs@(Cost  j r)  
    | i == j                              =   Cost i (l `best'` r)
    | i < j                               =   ls
    | i > j                               =   rs
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

-- The function 
getCheapest :: Int -> [(Int, Steps a)] -> Steps a 
getCheapest _ [] = error "no correcting alternative found"
getCheapest n l  =  snd $  foldr (\(w,ll) btf@(c, l)
                               ->    if w < c   -- c is the best cost estimate thus far, and w total costs on this path
                                     then let new = (traverse n ll w c) 
                                          in if new < c then (new, ll) else btf
                                     else btf 
                               )   (maxBound, error "getCheapest") l


traverse :: Int -> Steps a -> Int -> Int  -> Int 
traverse 0  _               =  trace' ("traverse " ++ show 0 ++ "\n") (\ v c ->  v)
traverse n (Step _  l)      =  trace' ("traverse Step  " ++ show n ++ "\n") (traverse (n -  1 ) l)
traverse n (Cost _  l)      =  trace' ("traverse Cost  " ++ show n ++ "\n") (traverse n         l)
traverse n (Apply _ l)      =  trace' ("traverse Apply " ++ show n ++ "\n") (traverse n         l)
traverse n (Fail m m2ls)    =  trace' ("traverse Fail  " ++ show n ++ "\n") (\ v c ->  foldr (\ (w,l) c' -> if v + w < c' then traverse (n -  1 ) l (v+w) c'
                                                                                                           else c'
                                                                                            ) c (map ($m) m2ls)
                                                                    )
traverse n (End_h ((a, lf))    r)  =  traverse n (lf a `best` removeEnd_h r)
traverse n (End_f (l      :_)  r)  =  traverse n (l `best` r)   


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Computing minimal length     %%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

get_length (P _ _ _ l ) = l

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Parsers     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- do not change into data, or be prepared to add ~ at subtle places !!
data  P   st  a =  P  (forall r . (a  -> st -> Steps r)  -> st -> Steps       r  )   -- history parser
                      (forall r . (      st -> Steps r)  -> st -> Steps   (a, r) )   -- future parser
                      (forall r . (      st -> Steps r)  -> st -> Steps       r  )   -- recogniser
                      Nat                                                            -- minimal length 

instance   Functor (P  state) where 
  fmap f   (P   ph pf pr l)   =  P  ( \  k -> ph ( k .f ))
                                    ( \  k inp ->  Apply (\(a,r) -> (f a, r)) (pf k inp)) -- pure f <*> pf
                                    (pr) 
                                    l

instance   Applicative (P  state) where
  P ph pf pr pl <*> ~(P qh qf qr ql)  =  P  ( \  k -> ph (\ pr -> qh (\ qr -> k (pr qr))))
                                            ((apply .) . (pf .qf))
                                            ( pr . qr)
                                            (nat_add pl ql) 
  pure a                              =  P  ($a) ((push a).) id Zero


instance   Alternative (P   state) where 
  P ph pf pr pl <|> P qh qf qr ql =  let (rl, b) = nat_min pl ql
                                         bestx :: Steps a -> Steps a -> Steps a
                                         bestx = if b then flip best else best 
                                     in    P (\  k inp  -> ph k inp `bestx` qh k inp)
                                             (\  k inp  -> pf k inp `bestx` qf k inp)
                                             (\  k inp  -> pr k inp `bestx` qr k inp)
                                             rl
                                            
  empty                =  P  ( \  k inp  ->  noAlts)
                             ( \  k inp  ->  noAlts)
                             ( \  k inp  ->  noAlts)
                             Infinite

instance  ( Provides state symbol token) => Symbol (P  state) symbol token where
  pSym a =  P ( \ k inp -> splitState a k inp)
              ( \ k inp -> splitState a (\ t inp' -> push t (k inp')) inp)
              ( \ k inp -> splitState a (\ _ inp' -> k inp') inp)
              (Succ Zero)

(<?>) :: P state a -> String -> P state a
P  ph  pf  pr  pl <?> label = P ( \ k inp -> replaceExpected  ( ph k inp))
                                ( \ k inp -> replaceExpected  ( pf k inp))
                                ( \ k inp -> replaceExpected  ( pr k inp))
                                pl
                           where replaceExpected (Fail _ c) = (Fail [label] c)
                                 replaceExpected others     = others
      
data Id a = Id a deriving Show

-- parse_h (P (ph, pf, pr)) = fst . eval . ph  (\ a rest -> if eof rest then push a failAlways else error "pEnd missing?") 
parse (P ph pf pr pl) = fst . eval . pf  (\ rest   -> if eof rest then succeedAlways        else error "pEnd missing?")

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Monads      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unParser_h (P  h   _  _  _)  =  h
unParser_f (P  _   f  _  _)  =  f
unParser_r (P  _   _  r  _)  =  r
          

instance  Monad (P st) where
       P  ph pf pr pl  >>=  a2q = 
                P  (  \k -> ph (\ a -> unParser_h (a2q a) k))
                   (  \k -> ph (\ a -> unParser_f (a2q a) k))
                   (  \k -> ph (\ a -> unParser_r (a2q a) k))
                   (nat_add pl (error "cannot compute minimal length of right hand side of monadic parser"))
       return  = pure 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Greedy      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_gr mbf l@(Step _ _)  _  = l
best_gr mbf l             r  = mbf best l r 

P ph pf pr pl <<|> P qh qf qr ql  = let (rl, b) = nat_min pl ql
                                        bestx = if b then flip best else best
                                    in   P ( \ k st  -> norm (ph k st) `bestx` norm (qh k st))
                                           ( \ k st  -> norm (pf k st) `bestx` norm (qf k st))
                                           ( \ k st  -> norm (pr k st) `bestx` norm (qr k st))
                                           rl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Microsteps  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


P ph pf pr pl `micro` i = P ( \ k st -> ph (\ a st -> Cost i (k a st)) st)
                            ( \ k st -> pf (Cost i .k) st)
                            ( \ k st -> pr (Cost i .k) st)
                            pl 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Ambiguous   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
amb :: P st a -> P st [a]

amb (P ph pf pr pl) = P ( \k     ->  removeEnd_h . ph (\ a st' -> End_h ([a], \ as -> k as st') noAlts))
                        ( \k inp ->  combinevalues . removeEnd_f $ pf (\st -> End_f [k st] noAlts) inp)
                        ( \k     ->  removeEnd_h . pr (\ st' -> End_h ([undefined], \ _ -> k  st') noAlts))
                        pl

removeEnd_h     :: Steps (a, r) -> Steps r
removeEnd_h (Fail  m ls             )  =   Fail m (applyFail removeEnd_h ls)
removeEnd_h (Step  ps l             )  =   Step  ps (removeEnd_h l)
removeEnd_h (Apply f l              )  =   error "not in history parsers"
removeEnd_h (End_h  (as, k_st  ) r  )  =   k_st as `best` removeEnd_h r 

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
       
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% pErrors     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class state `Stores`  errors | state -> errors where
  getErrors    ::  state   -> (errors, state)

pErrors :: Stores st errors => P st errors
pEnd    :: (Stores st errors, Eof st) => P st errors

pErrors = P ( \ k inp -> let (errs, inp') = getErrors inp in k    errs    inp' )
            ( \ k inp -> let (errs, inp') = getErrors inp in push errs (k inp'))
            ( \ k inp -> let (errs, inp') = getErrors inp in            k inp' )
            Zero

pEnd    = P ( \ k inp -> let deleterest inp =  case deleteAtEnd inp of
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


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% State Change          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pSwitch :: (st1 -> (st2, st2 -> st1)) -> P st2 a -> P st1 a


pSwitch split (P ph pf pr pl)    = P (\ k st1 ->  let (st2, back) = split st1
                                                  in ph (\ a st2' -> k a (back st2')) st2)
                                     (\ k st1 ->  let (st2, back) = split st1
                                                  in pf (\st2' -> k (back st2')) st2)
                                     (\ k st1 ->  let (st2, back) = split st1
                                                  in pr (\st2' -> k (back st2')) st2)
                                     pl 

instance ExtApplicative (P st)  where
  P ph pf pr pl <*  ~(P _  _  qr ql)   = P ( ph. (qr.)) (pf. qr)    (pr . qr)            (nat_add pl ql)
  P _  _  pr pl *>  ~(P qh qf qr ql)   = P ( pr . qh  ) (pr. qf)    (pr . qr)            (nat_add pl ql)
  f             <$   (P _  _  qr ql)   = P ( qr . ($f)) (\ k st -> push f (qr k st)) qr              ql

type Strings = [String]
