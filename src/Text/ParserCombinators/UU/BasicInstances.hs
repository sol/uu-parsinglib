{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction,
              TypeSynonymInstances #-}

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Some Instances        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

module Text.ParserCombinators.UU.BasicInstances where
import Text.ParserCombinators.UU.Core
import Data.List
import Debug.Trace

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

data Str     t  loc  = Str   {  input    :: [t]
                             ,  msgs     :: [Error loc ]
                             ,  pos      :: loc
                             ,  deleteOk :: !Bool}

listToStr ls initloc = Str   ls  []  initloc  True

type Parser a = P (Str Char (Int,Int)) a 
instance IsLocationUpdatedBy (Int,Int) Char where
   advance (line,pos) c = case c of
                          '\n' ->  (line+1, 0) 
                          '\t' ->  (line  , pos + 8 - (pos-1) `mod` 8)
                          _    ->  (line  , pos + 1)

instance IsLocationUpdatedBy (Int,Int) String where
   advance  = foldl advance 

instance (Show a,  loc `IsLocationUpdatedBy` a) => Provides  (Str  a loc)  (a -> Bool, String, a)  a where
       splitState (p, msg, a) k (Str  tts   msgs pos  del_ok) 
          = let ins exp =       (5, k a (Str tts (msgs ++ [Inserted (show a)  pos  exp]) pos  False))
                del exp =       (5, splitState (p,msg, a) 
                                    k
                                    (Str (tail tts) 
                                         (msgs ++ [Deleted  (show(head tts))  pos  exp]) 
                                         (advance pos (head tts))
                                         True ))
            in case tts of
               (t:ts)  ->  if p t 
                           then  show_symbol ("Accepting symbol: " ++ show t ++ " at position: " ++ show pos ++"\n") 
                                 (Step 1 (k t (Str ts msgs (advance pos t) True)))
                           else  Fail [msg] (ins: if del_ok then [del] else [])
               []      ->  Fail [msg] [ins]

instance (Ord a, Show a, loc `IsLocationUpdatedBy`  a) => Provides  (Str  a loc)  (a,a)  a where
       splitState a@(low, high) = splitState (\ t -> low <= t && t <= high, show low ++ ".." ++ show high, low)

instance (Eq a, Show a, loc `IsLocationUpdatedBy`  a) => Provides  (Str  a loc)  a  a where
       splitState a  = splitState ((==a), show a, a) 

instance Show a => Eof (Str a loc) where
       eof (Str  i        _    _    _    )                = null i
       deleteAtEnd (Str  (i:ii)   msgs pos ok    )        = Just (5, Str ii (msgs ++ [DeletedAtEnd (show i)]) pos ok)
       deleteAtEnd _                                      = Nothing


instance  Stores (Str a loc) (Error loc) where
       getErrors   (Str  inp      msgs pos ok    )     = (msgs, Str inp [] pos ok)

instance  HasPosition (Str a loc) loc where
       getPos   (Str  inp      msgs pos ok    )        = pos

-- pMunch

data Munch a = Munch (a -> Bool) String

instance (Show a, loc `IsLocationUpdatedBy` [a]) => Provides (Str a loc) (Munch a) [a] where 
       splitState (Munch p x) k inp@(Str tts msgs pos del_ok)
          =    let (munched, rest) = span p tts
                   l               = length munched
               in if l > 0 then show_munch ("Accepting munch: " ++ x ++ " " ++ show munched ++  show pos ++ "\n") 
                                (Step l (k munched (Str rest msgs (advance pos munched)  (l>0 || del_ok))))
                           else show_munch ("Accepting munch: " ++ x ++ " " ++ show munched ++ show pos ++ "\n") (k [] inp)

pMunch :: (Provides st (Munch a) [a]) => (a -> Bool) -> P st [a]
pMunch  p   = pSymExt Zero Nothing  (Munch p "") -- the empty case is handled above
pMunchL p l = pSymExt Zero Nothing  (Munch p l) -- the empty case is handled above


data Token a = Token [a] Int -- the Int value represents the cost for inserting such a token

instance (Show a, Eq a, loc `IsLocationUpdatedBy` [a]) => Provides (Str a loc) (Token a) [a] where 
  splitState tok@(Token  as cost) k (Str tts msgs pos del_ok)
   =  let l = length as
          msg = show as 
      in  case stripPrefix as tts of
          Nothing  ->  let ins exp =  (cost, k as             (Str tts         (msgs ++ [Inserted msg               pos  exp])   pos    False))
                           del exp =  (5,    splitState tok k (Str (tail tts)  (msgs ++ [Deleted  (show(head tts))  pos  exp])  (advance pos [(head tts)]) True ))
                       in if null tts then  Fail [msg] [ins]
                                      else  Fail [msg] (ins: if del_ok then [del] else [])
          Just rest -> show_tokens ("Accepting token: " ++ show as ++"\n") 
                       (Step l (k as (Str rest msgs (advance pos as) True)))

pToken     as   =   pTokenCost as 5
pTokenCost as c =   if null as then error "call to pToken with empty token"
                    else pSymExt (length as) Nothing (Token as c)
                    where length [] = Zero
                          length (_:as) = Succ (length as)

show_tokens m v = {-  trace m  -} v
show_munch  m v = {-  trace m  -} v
show_symbol m v = {-  trace m  -} v
