{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction,
              TypeSynonymInstances,
              ScopedTypeVariables #-}

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Some Instances        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

module Text.ParserCombinators.UU.BasicInstances where
import Text.ParserCombinators.UU.Core
import qualified Data.List  as DL
import Debug.Trace

-- | The class @StringLike@ captures what we need to know from and about our input data structure. 
--   It virtually contains symbols of type @a@
--
class  StringLike str a | str -> a where
   _uncons     ::                   str -> Maybe (a, str)
   _span       ::  (a -> Bool)   -> str -> (str, str)
   _unpack     :: str                   -> [a]
   _pack       :: [a]                   -> str
   _head       :: str                   -> a

class SeqLike str where
   _null       ::          str -> Bool 
   _length     ::          str -> Int   
   _tail       ::          str -> str
   _isPrefixOf :: str   -> str -> Bool
   _drop       :: Int   -> str -> str


data Error  pos =    Inserted String pos Strings
                   | Deleted  String pos Strings
                   | DeletedAtEnd String

instance (Show pos) => Show (Error  pos) where 
 show (Inserted s pos expecting) = "-- >    Inserted " ++  s ++ " at position " ++ show pos ++  show_expecting  expecting 
 show (Deleted  t pos expecting) = "-- >    Deleted  " ++  t ++ " at position " ++ show pos ++  show_expecting  expecting 
 show (DeletedAtEnd t)           = "-- >    The token " ++ t ++ " was not consumed by the parsing process."

show_errors = sequence_ . (map (putStrLn . show))


show_expecting [a]    = " expecting " ++ a
show_expecting (a:as) = " expecting one of [" ++ a ++ concat (map (", " ++) as) ++ "]"
show_expecting []     = " expecting nothing"

data Str str a  loc  = Str   {  input    :: str
                             ,  msgs     :: [Error loc ]
                             ,  pos      :: loc
                             ,  deleteOk :: !Bool}

listToStr ls initloc = Str   ls  []  initloc  True

type Parser a = P (Str String Char (Int,Int)) a 

instance IsLocationUpdatedBy (Int,Int) Char where
   advance (line,pos) c = case c of
                          '\n' ->  (line+1, 0) 
                          '\t' ->  (line  , pos + 8 - (pos-1) `mod` 8)
                          _    ->  (line  , pos + 1)

instance IsLocationUpdatedBy (Int,Int) String where
   advance  = foldl advance 

instance (Show a,  loc `IsLocationUpdatedBy` str, StringLike str a) => Provides  (Str str a loc)  (a -> Bool, String, a)  a where
       splitState (p, msg, a) k (Str  tts   msgs pos  del_ok) 
          = let ins exp =       (5, k a (Str tts (msgs ++ [Inserted (show a)  pos  exp]) pos  False))
                del exp =       (5, splitState (p,msg, a) 
                                    k
                                    (Str (_tail tts) 
                                         (msgs ++ [Deleted  (show(_head tts))  pos  exp]) 
                                         (advance pos (_pack([_head tts])::str))
                                         True ))
            in case _uncons tts of
               Just (t,ts)  ->  if p t 
                                then  Step 1 (k t (Str ts msgs (advance pos ((_pack [t])::str)) True))
                                else  Fail [msg] (ins: if del_ok then [del] else [])
               Nothing ->  Fail [msg] [ins]

instance (Ord a, Show a, loc `IsLocationUpdatedBy` str, StringLike str a) => Provides  (Str str a loc)  (a,a)  a where
       splitState a@(low, high) = splitState (\ t -> low <= t && t <= high, show low ++ ".." ++ show high, low)

data Single a = Single a
instance (Eq a, Show a, loc `IsLocationUpdatedBy`  str , StringLike str a) => Provides  (Str str a  loc)  (Single a)  a where
       splitState (Single a)  = splitState ((==a), show a, a) 

instance (Show a, StringLike str a, SeqLike str) => Eof (Str str a loc) where
       eof (Str  i        _    _    _    )           = _null i
       deleteAtEnd (Str  str   msgs pos ok    )   
        = fmap (\ (i,ii) -> (5, Str ii (msgs ++ [DeletedAtEnd (show i)]) pos ok)) (_uncons str)

instance  Stores (Str str a loc) (Error loc) where
       getErrors (Str inp  msgs pos ok) = (msgs, Str inp [] pos ok)

instance  HasPosition (Str str a loc) loc where
       getPos    (Str inp  msgs pos ok) = pos

-- pMunch

data Munch a = Munch (a -> Bool) String

instance (Show a, loc `IsLocationUpdatedBy` str, StringLike str a, SeqLike str) => Provides (Str str a loc) (Munch a) [a] where 
       splitState (Munch p x) k inp@(Str tts msgs pos del_ok)
          =    let (munched, rest) = _span p tts
                   l               = _length munched
               in if l > 0 then Step l (k (_unpack munched) (Str rest msgs (advance pos munched)  (l>0 || del_ok)))
                           else k [] inp

pMunch :: (Provides st (Munch a) [a]) => (a -> Bool) -> P st [a]
pMunch  p   = pSymExt Zero Nothing  (Munch p "") -- the empty case is handled above
pMunchL p l = pSymExt Zero Nothing  (Munch p l) -- the empty case is handled above
data Token a = Token [a] Int -- the Int value represents the cost for inserting such a token

instance (Show a, Eq a, loc `IsLocationUpdatedBy` str, StringLike str a, SeqLike str)
         => Provides (Str str a loc) (Token a) [a] where 
  splitState tok@(Token  as cost) k (Str tts msgs pos del_ok)
   =  let pas:: str = _pack as
          l   = _length pas           
      in  if _isPrefixOf pas tts 
          then Step l (k as (Str (_drop l tts)  msgs (undefined) True))
          else let msg = show as
                   ins exp =  (cost, k as  ((Str tts (msgs ++ [Inserted msg   pos  exp])  pos  False)::(Str str a loc)))
                   del exp =  (5,     splitState tok k ((Str (_tail tts)  (msgs ++ [Deleted  (show(_head tts))  pos  exp])  (undefined) True )::(Str str a loc)))
               in if _null tts then  Fail [msg] [ins]
                              else  Fail [msg] (ins: if del_ok then [del] else [])



pToken     as   =   pTokenCost as 5
pTokenCost as c =   case as of
                    [] -> error "call to pToken with empty token"
                    _  ->  pSymExt (length as) Nothing (Token as c)
                           where length [] = Zero
                                 length (_:as) = Succ (length as)

