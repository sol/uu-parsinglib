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
              ImpredicativeTypes, 
              TypeSynonymInstances,
              LiberalTypeSynonyms,
              ScopedTypeVariables #-}


module Text.ParserCombinators.UU.Core ( module Text.ParserCombinators.UU.Core
                                              , module Control.Applicative) where
import Control.Applicative  hiding ((<*), (*>), (<$), (<$>), many, some, optional)
-- import Char
-- import Debug.Trace
-- import Maybe

{-
class Applicative p where
 (<*>) :: p (b -> a) -> p b -> pa
 pure  :: a -> p a
-}

-- * The Classes Defining the Interface
-- ** `IsParser`

-- | This class collects a number of classes which together defines what a `Parser` should provide. 
-- Since it is just a predicate we have prefixed the name by the phrase `Is'

class    (Applicative p, ExtApplicative p, Alternative p)    => IsParser p where
instance (Applicative p, ExtApplicative p, Alternative p)    => IsParser p where

infixl  4  <*, *>
infixl  4  <$, <$>

-- ** `ExtApplicative'
-- | The module "Control.Applicative" contains definitions for `<$`, `*>`  and `<*` which cannot be changed. Since we want to give
-- optimised implementations of these combinators, we are not importing those definitions, and define a class containing their signatures instead. Hopefully this change will make it into the module @Control.Application@ in the future.

class  Applicative p => ExtApplicative p where
  (<$>)     ::  (b -> a)        -> p b   ->   p  a
  (<*)      ::  p  a            -> p b   ->   p  a
  (*>)      ::  p  b            -> p a   ->   p  a
  (<$)      ::  a               -> p b   ->   p  a
  f <$> p   = pure f <*> p
  p <* q    = pure const <*> p <*> q
  p *> q    = (\ _ qr -> qr) <$> p <*> q
  f <$ p    = pure (const f) <*> p

-- ** `Eof'

class Eof state where
       eof          ::  state   -> Bool
       deleteAtEnd  ::  state   -> Maybe (Cost, state)

---------------------------------------------------------------------------------
-- Ph Pf Pr ---------------------------------------------------------------------
---------------------------------------------------------------------------------

newtype Ph st a =  Ph (forall r . (a  -> st -> Steps r)  -> st -> Steps       r )   -- history parser
newtype Pf st a =  Pf (forall r . (      st -> Steps r)  -> st -> Steps   (a, r))   -- future parser
newtype Pr st a =  Pr (forall r . (      st -> Steps r)  -> st -> Steps       r )   -- recogniser

instance Functor (Ph st) where
  fmap f (Ph ph) = Ph (\k -> ph (k.f))

instance Functor (Pf st) where
  fmap f (Pf pf) = Pf (\k st ->  apply (push f (pf k st))) -- pure f <*> pf

instance Functor (Pr p) where
  fmap f (Pr pr)   = Pr pr
 
instance Applicative (Ph st) where
  Ph ph <*> Ph qh = Ph (\ k -> ph (\f -> qh (\ a -> k (f a))))
  pure a          = Ph (\ k -> k a)

instance Applicative (Pf st) where
  Pf pf <*> Pf qf = Pf (\k -> apply .  (pf (qf k)))
  pure a          = Pf (\k -> push a . k)

instance Applicative (Pr st) where
  Pr pr <*> Pr qr = Pr (\ k -> pr (qr k))
  pure a          = Pr id

---------------------------------------------------------------------------------
-- Triples ----------------------------------------------------------------------
---------------------------------------------------------------------------------
data Triple st a  = Triple   (Ph st a)  (Pf st a)  (Pr st a )
                  | None

instance Functor (Triple st) where
  fmap f   (Triple ph pf pr)   = Triple  (fmap f ph) (fmap f pf) (fmap f pr) 
  fmap f   None                = None 

map3L (f, g, h) NoneL              = None
map3L (f, g, h) (TripleL ph pf pr) = Triple (f ph) (g pf) (h pr)

instance Applicative (Triple st) where
  Triple ph pf pr <*> ~(Triple qh qf qr) =  Triple (ph <*> qh) (pf <*> qf) (pr <*> qr)
  _               <*> _                  =  error " <*>  with at least one side without alternatives"
  pure a                                 =  Triple (pure a) (pure a) (pure a)
  
instance ExtApplicative (Triple st) where
   f <$>  ~(Triple (Ph qh) (Pf qf) (Pr qr))   
     = Triple (Ph (\ k -> qh (k.f)))
              (Pf (\ k st -> Apply (mapFst f) (qf k st)))
              (Pr qr) 
   Triple (Ph ph) (Pf pf) (Pr pr) <*   ~(Triple (Ph qh) (Pf qf) (Pr qr))
     = Triple (Ph (\ k st -> ph (\a st -> qr (\st -> k a st) st) st))
              (Pf (\ k st -> pf (qr k) st))
              (Pr (\ k st -> pr (qr k) st))     
   Triple (Ph ph) (Pf pf) (Pr pr) *>   ~(Triple (Ph qh) (Pf qf) (Pr qr))
     = Triple (Ph (\ k st -> pr (\ st -> qh (\a st -> k a st) st) st))
              (Pf (\ k st -> pr (qf k) st))
              (Pr (\ k st -> pr (qr k) st))
   a <$   ~(Triple (Ph qh) (Pf qf) (Pr qr))  
     = Triple (Ph (\ k st -> qr (\ st -> k a st) st ))
              (Pf (\ k st -> push a ( qr k st)))
              (Pr qr)


data TripleL st a = TripleL [Ph st a] [Pf st a] [Pr st a]
                  | NoneL

transposeTL NoneL = []
transposeTL (TripleL [ph] [pf] [pr]) = [Triple ph pf pr]
transposeTL (TripleL (ph:phs) (pf:pfs) (pr:prs)) = Triple ph pf pr : transposeTL (TripleL phs pfs prs)

transposeLT [] = NoneL
transposeLT [Triple ph pf pr] =  TripleL [ph] [pf] [pr]
transposeLT (Triple ph pf pr:lt) = let TripleL phs pfs prs = transposeLT lt
                                   in  TripleL (ph:phs)  (pf:pfs) (pr:prs)

instance Functor (TripleL st) where
  fmap f   (TripleL phs pfs prs)   = TripleL (map (fmap f) phs) 
                                             (map (fmap f) pfs) 
                                             (map (fmap f) prs)
  fmap f  NoneL                    = NoneL
---------------------------------------------------------------------------------
-- Descriptors ------------------------------------------------------------------
---------------------------------------------------------------------------------
newtype Descr st  a =  Descr ( [Triple st a]     -- non-empty parsers
                             , [String]          -- expected symbols
                             , Maybe (Bool, a)   -- empty parser
                             , Triple st a       -- dynamic low    priority parser
                             , Triple st a       -- dynamic normal priority parser    
                             ) 

instance Functor (Descr  state) where 
  fmap f  (Descr (             triplel, exp,                 emp,        dynl,        dynh)) 
        =  Descr (map (fmap f) triplel, exp, fmap (mapSnd f) emp, fmap f dynl, fmap f dynh)

-- it does not make much sense to make Descriptors an instance of Applicative
-- since we need the parser tupled with the right-hand side operand


-- Parsers consist of a descriptor and the parser constructed from this descriptor

newtype P st a = P ( Triple st a, Descr st a)

instance Functor (P st) where
  fmap f (P (_, descr)) = mkParser (fmap f descr)

-- the function mkParser mainatins the invarinat that the first component of a P is described by its second component
mkParser :: Descr st a -> P st a
mkParser d@(Descr (triple, exp, emp, dynl, dynh))       
    = let non_empty = map3L (bestLh exp, bestLf exp, bestLr exp) (transposeLT triple)
          empTriple Nothing  _     = None
          empTriple (Just (low ,a))  low' 
                    | low == low'  = pure a
                    | True         = None
      in P ( (non_empty `tripleChoiceBest` dynh `tripleChoiceBest` empTriple emp False)  -- the empty parser with normal priority
              `tripleChoiceGreedy`
             (dynl `tripleChoiceBest` empTriple emp True)
           , d)

tripleChoiceBest   ::  Triple st a -> Triple st a  -> Triple st a
tripleChoiceGreedy ::  Triple st a -> Triple st a  -> Triple st a
tripleChoiceBest   = tripleChoice best
tripleChoiceGreedy = tripleChoice best_gr
tripleChoice :: (forall r. Steps r -> Steps r -> Steps r) -> Triple st a -> Triple st a  -> Triple st a
tripleChoice _ None  r    = r
tripleChoice _ l     None = l
tripleChoice best (Triple (Ph ph) (Pf pf) (Pr pr))  (Triple (Ph qh) (Pf qf) (Pr qr))
  = Triple  (Ph  (\ k st -> ph k st `best` qh k st))
            (Pf  (\ k st -> pf k st `best` qf k st))
            (Pr  (\ k st -> pr k st `best` qr k st))

bestLh :: Strings -> [Ph st a] ->  Ph st a
bestLf :: Strings -> [Pf st a] ->  Pf st a
bestLr :: Strings -> [Pr st a] ->  Pr st a

bestLh  exp ps = Ph ( \k st -> addExp exp . foldr1 best $ [p k st | Ph p <- ps])
bestLf  exp ps = Pf (\ k st -> addExp exp . foldr1 best $ [p k st | Pf p <- ps])
bestLr  exp ps = Pr (\ k st -> addExp exp . foldr1 best $ [p k st | Pr p <- ps])

addExp exp steps = Expect exp steps

instance Applicative (P st) where
  P (_, Descr (ps, expp, mp, dynl, dynh)         ) <*> P (q, Descr ~(tripleql, expq, mq, _, _)) 
   = mkParser (Descr ( map (<*> q) ps  ++ case mp  of
                                          Just (False, a) -> map (a <$>) tripleql
                                          _               -> []                            
                     , case mp of {Nothing -> expp; Just _ -> expp++expq}
                     , do (pbest, f) <- mp
                          (_,     a) <- mq
                          return (pbest, f a)
                     , (dynl <*> q)  `tripleChoiceBest` emptyWithRhs
                     ,  dynh <*> q 
             )       ) 
     where emptyWithRhs =  case mp of {Just (True, f)  -> f <$> q; _ -> None} 
  pure a    = mkParser (Descr ( [], [], Just(True, a), None, None))




instance ExtApplicative (P st)  where
  P (_, Descr (ps, expp, mp, dynl, dynh)         ) <* P (q, Descr ~(tripleql, expq, mq, _, _)) 
   = mkParser (Descr ( map (<* q) ps  ++  case mp  of
                                          Just (False, a) -> map (a <$) tripleql
                                          _               -> []                            
                     , case mp of {Nothing -> expp; Just _ -> expp++expq}
                     , do (pbest, f) <- mp
                          (_,     a) <- mq
                          return (pbest, f)
                     , (dynl <* q)  `tripleChoiceBest` emptyWithRhs
                     ,  dynh <* q 
             )       ) 
     where emptyWithRhs =  case mp of {Just (True, f)  -> f <$ q; _ -> None} 
  P (_, Descr (ps, expp, mp, dynl, dynh)         ) *> P (q, Descr ~(tripleql, expq, mq, _, _)) 
   = mkParser (Descr ( map (*> q) ps  ++  case mp  of
                                          Just (False, a) -> tripleql
                                          _               -> []                            
                     , case mp of {Nothing -> expp; Just _ -> expp++expq}
                     , do (pbest, f) <- mp
                          (_,     a) <- mq
                          return (pbest, a)
                     , (dynl *> q)  `tripleChoiceBest` emptyWithRhs
                     ,  dynh *> q 
             )       ) 
     where emptyWithRhs =  case mp of {Just (True, f)  ->  q; _ -> None} 
  f <$> P (q, Descr ~(tripleql, expq, mq, dynl, dynr)) 
   = mkParser (Descr ( map (f<$>) tripleql                           
                     , expq
                     , fmap (mapSnd f) mq
                     , f <$> dynl
                     , f <$> dynr 
              )      ) 
  f <$ P (q, Descr ~(tripleql, expq, mq, dynl, dynr)) 
   = mkParser (Descr ( map (f<$) tripleql                           
                     , expq
                     , case mq of {Just (b, _) -> Just (b, f); _ -> Nothing}
                     , f <$ dynl
                     , f <$ dynr 
              )      ) 



instance   Alternative (P st) where 
  P (_, Descr (ps, expp, mp, dynlp, dynhp)) <|> P (_, Descr (qs, expq, mq, dynlq, dynhq))
   = mkParser (Descr ( ps ++ qs
                     , expp++expq
                     , case (mp, mq) of
                            (Nothing, _)        -> mq
                            (_      , Nothing ) -> mp
                            _                   -> error ("choice between two possibly empty alteratives,\none expecting: " ++ show expp 
                                                                ++ "\nand the other expecting: " ++ show expq)
                     , dynlp `tripleChoiceBest` dynlq
                     , dynhp `tripleChoiceBest` dynhq
              )      )
  empty = mkParser (Descr ([], [], Nothing, None, None))



-- parse_h (P (ph, pf, pr)) = fst . eval . ph  (\ a rest -> if eof rest then push a failAlways else error "pEnd missing?") 
parse (P (Triple _ (Pf pf) _, _)) = fst . eval [] .  pf  (\ rest   -> if eof rest then failAlways  else error "pEnd missing?")


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Monads      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unParser_h (P (Triple (Ph ph) pf pr, _))  =  ph
unParser_f (P (Triple ph (Pf pf) pr, _))  =  pf
unParser_r (P (Triple ph pf (Pr pr), _))  =  pr
          

None `bind` _ = error "no alternative found in left hand side of monadic bind"
Triple (Ph ph) (Pf pf) (Pr pr) `bind` a2q
  = Triple (Ph  ( \k -> ph (\ a -> unParser_h (a2q a) k)))
           (Pf  ( \k -> ph (\ a -> unParser_f (a2q a) k)))
           (Pr  ( \k -> ph (\ a -> unParser_r (a2q a) k))) 

instance  Monad (P st) where
       P ( _, Descr (ps, expp, mp, dynl, dynh))  >>=  a2q 
         = let non_empty_result 
                = mkParser. Descr $
                           (  map (`bind` a2q) ps
                           ,  expp
                           ,  Nothing
                           ,  dynl `bind` a2q , dynh `bind` a2q
                           )
           in case mp of
              Nothing -> non_empty_result
              Just (greedy, a)  -> if greedy then non_empty_result  <<|> a2q a -- to be replaced by <<|>
                                             else non_empty_result  <|> a2q a                    
       return  = pure 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Greedy      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_gr :: Steps a -> Steps a -> Steps a

l@  (Step _ _)   `best_gr` _  = l
l                `best_gr` r  = l `best` r

p <<|> q  = p <|> q  -- not intended behaviour, but working for the time being, has to be replaced


{-
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Ambiguous   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
amb :: P st a -> P st [a]

amb (P (ph, pf, pr, pexp, mp)) 
  = P ( \k     ->  removeEnd_h . ph (\ a st' -> End_h ([a], \ as -> k as st') noAlts)
      , \k inp ->  combinevalues . removeEnd_f $ pf (\st -> End_f [k st] noAlts) inp
      , \k     ->  removeEnd_h . pr (\ st' -> End_h ([undefined], \ _ -> k  st') noAlts)
      , pexp
      , fmap (:[]) mp
      )

-}
{-
removeEnd_h     :: Steps (a, r) -> Steps r
removeEnd_h (Fail     ls            ) =    Fail  (applyFail removeEnd_h ls)
removeEnd_h (Step  ps l             )  =   Step  ps (removeEnd_h l)
removeEnd_h (Apply f l              )  =   error "not in history parsers"
removeEnd_h (End_h  (as, k_st  ) r  )  =   k_st as `best` removeEnd_h r 

removeEnd_f      :: Steps r -> Steps [r]
removeEnd_f (Fail   ls)        =   Fail   (applyFail removeEnd_f ls)
removeEnd_f (Step ps l)        =   Step ps (removeEnd_f l)
removeEnd_f (Apply f l)        =   Apply (map' f) (removeEnd_f l)
removeEnd_f (End_f(s:ss) r)    =   Apply  (:(map  eval ss)) s 
                                                 `best`
                                          removeEnd_f r

combinevalues  :: Steps [(a,r)] -> Steps ([a],r)
combinevalues lar           =   Apply (\ lar -> (map fst lar, snd (head lar))) lar

map' f ~(x:xs)              =   f x : map f xs
-} 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% pErrors     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class state `Stores`  errors | state -> errors where
  getErrors    ::  state   -> (errors, state)

pErrors :: Stores st errors => P st errors
pEnd    :: (Stores st errors, Eof st) => P st errors

pErrors = mkParser. Descr $
            ( []
            , ["pErrors"]
            , Nothing
            , None
            , Triple (Ph (\ k inp -> let (errs, inp') = getErrors inp in k    errs    inp' ))
                     (Pf (\ k inp -> let (errs, inp') = getErrors inp in push errs (k inp')))
                     (Pr (\ k inp -> let (errs, inp') = getErrors inp in            k inp' ))
            )

pEnd    = mkParser .Descr $
            ( []
            , ["pEnd"]
            , Nothing
            , None
            , Triple ( Ph (\ k inp -> let deleterest inp =  case deleteAtEnd inp of
                                                  Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                             in k  finalerrors finalstate
                                                  Just (i, inp') -> Fail   [const (i,  deleterest inp')]
                                     in deleterest inp))
                     (Pf(\ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in push finalerrors (k finalstate)
                                                    Just (i, inp') -> Fail  [const ((i, deleterest inp'))]
                                       in deleterest inp))
                     (Pr (\ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in  (k finalstate)
                                                    Just (i, inp') -> Fail  [const (i, deleterest inp')]
                                       in deleterest inp))
            )        
{-

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% State Change          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pSwitch :: (st1 -> (st2, st2 -> st1)) -> P st2 a -> P st1 a


pSwitch split (P (_, Descr (TripleL (phs, pfs, prs), expp, pm)))  
      = mkParser (Descr (TripleL  ( [Ph (\ k st1 ->  let (st2, back) = split st1  in ph (\ a st2' -> k a (back st2')) st2) | Ph ph <- phs]
                                  , [Pf (\ k st1 ->  let (st2, back) = split st1  in pf (\   st2' -> k   (back st2')) st2) | Pf pf <- pfs]
                                  , [Pr (\ k st1 ->  let (st2, back) = split st1  in pr (\   st2' -> k   (back st2')) st2) | Pr pr <- prs]
                                  )
                        , expp
                        , pm
                 )      )


type Strings = [String]

removeEnd_h = error "removeEnd_h"
-}
mapFst f (a, b) = (f a, b)
mapSnd f (a, b) = (a, f b)

type Strings = [String]


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
      Step   ::              Progress       ->  Steps a                                -> Steps   a
      Apply  ::  forall b.   (b -> a)       ->  Steps b                                -> Steps   a
      Expect ::              Strings        ->  Steps a                                -> Steps   a
      Fail   ::                                 [Strings   ->     (Cost , Steps   a)]  -> Steps   a
      End_h  ::              ([a] , [a] -> Steps r)        ->  Steps   (a,r)           -> Steps   (a, r)
      End_f  ::              [Steps   a]   ->  Steps   a                               -> Steps   a

push    :: v -> Steps   r -> Steps   (v, r)
push v  =  Apply (\ r -> (v, r))
apply   :: Steps (b -> a, (b, r)) -> Steps (a, r)
apply   =  Apply (\(b2a, ~(b, r)) -> (b2a b, r))  

failAlways  =  Fail  [const (0, failAlways)]
noAlts      =  Fail  []

eval :: Strings -> Steps   a      ->  a
eval e (Step  _    l       )  =   eval e l
eval e (Expect e'  l       )  =   eval (e++e') l
eval e (Fail       ls      )    =   eval [] (getCheapest 3 (map ($e) ls)) 
eval e (Apply  f   l       )  =   f (eval e l)
eval e (End_f   _  _       )  =   error "dangling End_f constructor in eval"
eval e (End_h   _  _       )  =   error "dangling End_h constructor in eval"


norm ::  Steps a ->  Steps   a
norm     (Apply f (Step   p    l  ))   =   Step p (Apply f l)
norm     (Apply f (Fail        ls ))   =   Fail (applyFail (Apply f) ls)
norm     (Apply f (Apply  g    l  ))   =   norm (Apply (f.g) l)
norm     (Apply f (End_f  ss   l  ))   =   End_f (map (Apply f) ss) (Apply f l)
norm     (Apply f (End_h  _    _  ))   =   error "Apply before End_h"
norm     (Expect e r               )   =   Expect e (norm r)


applyFail f  = map (\ g -> \ ex -> let (c, l) =  g ex in  (c, f l))

-- moet nog aangepast worden aan SFail

best :: Steps   a -> Steps   a -> Steps   a
x `best` y =   best' (norm x) (norm y)

best' ::  Steps   b -> Steps   b -> Steps   b
Expect ep  l     `best'`   r              =   Expect ep (l `best'` r)
l                `best'`  Expect eq r     =   Expect eq (l `best'` r)
Fail   ll        `best'`  Fail    rr      =   Fail (ll++rr)
Fail  _          `best'`  r               =   r
l                `best'`  Fail     _      =   l
Step  n   l      `best'`  Step  m  r
    | n == m                              =   Step n (l `best'` r)     
    | n < m                               =   Step n (l `best'`  Step (m - n)  r)
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
                                     then let new = (traverse n [] ll w c) 
                                          in if new < c then (new, ll) else btf
                                     else btf 
                               )   (maxBound, error "getCheapest") l


traverse :: Int -> Strings -> Steps a -> Int -> Int  -> Int 
traverse 0  _ _               =  \ v c ->  v
traverse n  e (Step _  l)     =  traverse (n -  1 ) e      l
traverse n  e (Expect e' l)   =  traverse n        (e++e') l
traverse n  e (Apply _ l)     =  traverse n        e       l
traverse n  e (Fail  m2ls)    =  \ v c ->  foldr (\ (w,l) c' -> if v + w < c' then traverse (n -  1 ) [] l (v+w) c'
                                                                              else c'
                                                 ) c (map ($e) m2ls)
traverse n  e (End_h ((a, lf))    r)  =  traverse n e (lf a `best` removeEnd_h r)
traverse n  e (End_f (l      :_)  r)  =  traverse n e (l `best` r)   

removeEnd_h = undefined
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

-- ** `Symbol'
-- | Many parsing libraries do not make a distinction between the terminal symbols of the language recognised and the 
-- tokens actually constructed from the  input. This happens e.g. if we want to recognise an integer or an identifier: we are also interested in which integer occurred in the input, or which identifier. Note that if the alternative later fails repair will take place, instead of trying the other altrenatives at the greedy choice point.

class  Show symbol => Symbol p  symbol token | p symbol -> token where

  pSymExp ::  symbol -> String   -> p token

pSym  a = pSymExp a (show a) 

-- ^ The function `pSym` takes as argument a value of some type `symbol', and returns a value of type `token'. The parser will in general depend on some 
-- state which is maintained holding the input. The functional dependency fixes the `token` type, based on the `symbol` type and the type of the parser `p`.
-- Since `pSym' is overloaded both the type and the value of symbol determine how to decompose the input in a `token` and the remaining input.

-- ** `Provides'

class  Provides state symbol token | state symbol -> token  where
       splitState   ::  symbol ->  (token -> state  -> Steps a) -> state -> Steps a


pSplit :: (Provides state symbol token) => (symbol, String) -> P state token 
pSplit (a, exp)
   = let splitState_a = splitState a
     in     mkParser (Descr ( [Triple ( Ph (\ k inp -> splitState_a  k inp))
                                      ( Pf (\ k inp -> splitState_a  (\ t inp' -> push t (k inp')) inp))
                                      ( Pr (\ k inp -> splitState_a  (\ _ inp' -> k inp') inp))
                       ]
                     , [exp]
                     , Nothing
                     , None
                     , None
             )       )





