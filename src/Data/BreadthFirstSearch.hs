{-# LANGUAGE  RankNTypes, 
              GADTs,
              CPP #-}

 -- | This module contains the necessary data and functions for a breadth-first search stratey with error-correcting steps.
--   Its main use is in the new uu-parsinglib package, but since it is more generally appliccable we have gathered the code in into a separate module.

module Data.BreadthFirstSearch where
import Debug.Trace

-- | The data type @`Steps`@ is the core data type on which we can base our search.a breadth-first search stratey with error-corrceting steps.
--   @Steps@  describes a tree  of streams (with common prefiexes) containing (in an interleaved way) both the online result of the searching process,
--   and progress information. Recognising an input token (parser speak) should correspond to a certain amount of @`Progress`@, 
--   which tells how much of the input state was consumed. 
--   The @`Progress`@ is used to implement the breadth-first searching process, in which alternatives are
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
--   The last two alternatives play a role in recognising ambigous non-terminals.
--   For a full description see the technical report referred to from the "Text.ParserCombinators.UU.README"  file.


data  Steps   a  where
      Step   ::                 Progress       ->  Steps a                             -> Steps   a
      Apply  ::  forall a b.    (b -> a)       ->  Steps   b                           -> Steps   a
      Fail   ::                 Strings        ->  [Strings   ->  (Cost , Steps   a)]  -> Steps   a
      Micro   ::                 Cost           ->  Steps a                             -> Steps   a
      End_h  ::                 ([a] , [a]     ->  Steps r)    ->  Steps   (a,r)       -> Steps   (a, r)
      End_f  ::                 [Steps   a]    ->  Steps   a                           -> Steps   a

type Cost = Int
type Progress = Int
type Strings = [String]

succeedAlways :: Steps a
succeedAlways = let steps = Step 0 steps in steps

failAlways    :: Steps a
failAlways  =  Fail [] [const (0, failAlways)]

noAlts         :: Steps a
noAlts      =  Fail [] []

has_success :: Steps a -> Bool
has_success (Step _ _) = True
has_success _        = False 

-- ! the functiona @`eval`@ removes the progress information from a sequence of steps, and constructs the value embedded in it by the @Apply@ steps.
--   If you are really desparate to see how your parsers are making progress (e.g. when you have written an ambiguous parser, and you cannot find the cause of
--   the exponential blow-up of your parsing process, you may switch on the trace in the function @`eval`@
-- 
#if TRACEEVAL
#define trace(msg,v)  trace (msg) (v)
#else
#define trace(msg,v)  v
#endif

eval :: Steps   a      ->  a
eval (Step  n    l)     =   trace("Step " ++ show n ++ "\n", eval l)
eval (Micro  _    l)    =   eval l
eval (Fail   ss  ls  )  =   trace("expecting: " ++ show ss, eval (getCheapest 3 (map ($ss) ls))) 
eval (Apply  f   l   )  =   f (eval l)
eval (End_f   _  _   )  =   error "dangling End_f constructor"
eval (End_h   _  _   )  =   error "dangling End_h constructor"

push        :: v -> Steps   r -> Steps   (v, r)
push v      =  Apply (\ r -> (v, r))
apply       :: Steps (b -> a, (b, r)) -> Steps (a, r)
apply       =  Apply (\(b2a, ~(b, r)) -> (b2a b, r)) 
pushapply   :: (b -> a) -> Steps (b, r) -> Steps (a, r)
pushapply f =  Apply (\ (b, r) -> (f b, r)) 

-- | @`norm`@ makes sure that the head of the sequence contains progress information.
-- It does so by pushing information about the result (i.e. the @Apply@ steps) backwards.
--
norm ::  Steps a ->  Steps   a
norm     (Apply f (Step   p    l  ))   =   Step  p (Apply f l)
norm     (Apply f (Micro  c    l  ))   =   Micro c (Apply f l)
norm     (Apply f (Fail   ss   ls ))   =   Fail ss (applyFail (Apply f) ls)
norm     (Apply f (Apply  g    l  ))   =   norm (Apply (f.g) l)
norm     (Apply f (End_f  ss   l  ))   =   End_f (map (Apply f) ss) (Apply f l)
norm     (Apply f (End_h  _    _  ))   =   error "Apply before End_h"
norm     steps                         =   steps

applyFail f  = map (\ g -> \ ex -> let (c, l) =  g ex in  (c, f l))

-- | The function @best@ compares two streams and best :: Steps   a -> Steps   a -> Steps   a
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

#if TRACETRAVERSE
#define trace(msg,v)  trace (msg) (v)
#else
#define trace(msg,v)  v
#endif

traverse :: Int -> Steps a -> Int -> Int  -> Int 
traverse 0  _                =  trace("traverse " ++ show 0 ++ "\n", \ v c ->  v)
traverse n (Step _   l)      =  trace("traverse Step   " ++ show n ++ "\n",traverse (n -  1 ) l)
traverse n (Micro _  l)      =  trace("traverse Micro  " ++ show n ++ "\n",traverse n         l)
traverse n (Apply _  l)      =  trace("traverse Apply  " ++ show n ++ "\n",traverse n         l)
traverse n (Fail m m2ls)     =  trace("traverse Fail   " ++ show n ++ "\n",\ v c ->  foldr (\ (w,l) c' -> if v + w < c' then traverse (n -  1 ) l (v+w) c'
                                                                                                           else c'
                                                                                            ) c (map ($m) m2ls)
                                     )
traverse n (End_h ((a, lf))    r)  =  traverse n (lf a `best` removeEnd_h r)
traverse n (End_f (l      :_)  r)  =  traverse n (l `best` r) 

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

