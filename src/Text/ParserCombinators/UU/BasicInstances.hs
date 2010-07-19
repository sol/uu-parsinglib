{-# LANGUAGE  RankNTypes, 
              GADTs,
              MultiParamTypeClasses,
              FunctionalDependencies, 
              FlexibleInstances, 
              FlexibleContexts, 
              UndecidableInstances,
              NoMonomorphismRestriction#-}

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Some Instances        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

module Text.ParserCombinators.UU.BasicInstances where
import Text.ParserCombinators.UU.Core
import Data.List

data Error  pos =    Inserted String pos Strings
                   | Deleted  String pos Strings
                   | DeletedAtEnd String

instance (Show pos) => Show (Error  pos) where 
 show (Inserted s pos expecting) = "\nInserted " ++  s ++ " at position " ++ show pos ++  show_expecting  expecting 
 show (Deleted  t pos expecting) = "\nDeleted  " ++  t ++ " at position " ++ show pos ++  show_expecting  expecting 
 show (DeletedAtEnd t)           = "\nThe token " ++ t ++ " was not consumed by the parsing process."


show_expecting [a]    = " expecting " ++ a
show_expecting (a:as) = " expecting one of [" ++ a ++ concat (map (", " ++) as) ++ "]"
show_expecting []     = " expecting nothing"

data Str     t    = Str   {  input    :: [t]
                          ,  msgs     :: [Error Int ]
                          ,  pos      :: !Int
                          ,  deleteOk :: !Bool}

listToStr ls = Str   ls  []  0  True

instance (Show a) => Provides  (Str  a)  (a -> Bool, String, a)  a where
       splitState (p, msg, a) k (Str  tts   msgs pos  del_ok) 
          = let ins exp =       (5, k a (Str tts (msgs ++ [Inserted (show a)  pos  exp]) pos  False))
                del exp =       (5, splitState (p,msg, a) 
                                    k
                                    (Str (tail tts)  (msgs ++ [Deleted  (show(head tts))  pos  exp]) (pos+1) True ))
            in case tts of
               (t:ts)  ->  if p t 
                           then  Step 1 (k t (Str ts msgs (pos + 1) True))
                           else  Fail [msg] (ins: if del_ok then [del] else [])
               []      ->  Fail [msg] [ins]

instance (Ord a, Show a) => Provides  (Str  a)  (a,a)  a where
       splitState a@(low, high) = splitState (\ t -> low <= t && t <= high, show low ++ ".." ++ show high, low)

instance (Eq a, Show a) => Provides  (Str  a)  a  a where
       splitState a  = splitState ((==a), show a, a) 

instance Show a => Eof (Str a) where
       eof (Str  i        _    _    _    )                = null i
       deleteAtEnd (Str  (i:ii)   msgs pos ok    )        = Just (5, Str ii (msgs ++ [DeletedAtEnd (show i)]) pos ok)
       deleteAtEnd _                                      = Nothing


instance  Stores (Str a) [Error Int] where
       getErrors   (Str  inp      msgs pos ok    )        = (msgs, Str inp [] pos ok)

-- pMunch

data Munch a = Munch (a -> Bool)

instance (Show a) => Provides (Str a) (Munch a) [a] where 
       splitState (Munch p) k (Str tts msgs pos del_ok)
          =    let (munched, rest) = span p tts
                   l               = length munched
               in Step l (k munched (Str rest msgs (pos+l)  (l>0 || del_ok)))

pMunch :: (Text.ParserCombinators.UU.Core.Symbol p (Munch a) [a]) => (a -> Bool) -> p [a]
pMunch p = pSym (Munch p) 

data Token a = Token [a] Int -- the Int value represents the cost for inserting such a token

instance (Show a, Eq a) => Provides (Str a) (Token a) [a] where 
  splitState tok@(Token  as cost) k (Str tts msgs pos del_ok)
   =  let l = length as
          msg = show as 
      in  case stripPrefix as tts of
          Nothing  ->  let ins exp =  (cost, k as             (Str tts         (msgs ++ [Inserted msg               pos  exp])   pos     False))
                           del exp =  (5,    splitState tok k (Str (tail tts)  (msgs ++ [Deleted  (show(head tts))  pos  exp])  (pos+1) True ))
                       in if null tts then  Fail [msg] [ins]
                                      else  Fail [msg] (ins: if del_ok then [del] else [])
          Just rest -> Step l (k as (Str rest msgs (pos+l) True))

pToken as = pSym (Token as 5)
pTokenCost as c = pSym (Token as c)



