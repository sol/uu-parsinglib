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
import Data.Maybe
import qualified Data.List as L
import Debug.Trace
import Prelude hiding (null, head, tail, span)

data Error  pos =    Inserted String pos Strings
                   | Deleted  String pos Strings
                   | DeletedAtEnd String

instance (Show pos) => Show (Error  pos) where 
 show (Inserted s pos expecting) = "-- >    Inserted " ++  s ++ " at position " ++ show pos ++  show_expecting  expecting 
 show (Deleted  t pos expecting) = "-- >    Deleted  " ++  t ++ " at position " ++ show pos ++  show_expecting  expecting 
 show (DeletedAtEnd t)           = "-- >    The token " ++ t ++ " was not consumed by the parsing process."

show_errors :: (Show a) => [a] -> IO ()
show_errors = sequence_ . (map (putStrLn . show))

show_expecting :: [String] -> String
show_expecting [a]    = " expecting " ++ a
show_expecting (a:as) = " expecting one of [" ++ a ++ concat (map (", " ++) as) ++ "]"
show_expecting []     = " expecting nothing"

data Str a s loc = Str { input    :: s
                       , msgs     :: [Error loc]
                       , pos      :: loc
                       , deleteOk :: !Bool}

class Stream s t | s -> t where
   uncons :: s -> Maybe (t, s)
   null :: s -> Bool
   null = isNothing . uncons
   head :: s -> t
   head = fst . fromMaybe (error "Cannot get head at end of stream.") . uncons
   tail :: s -> s
   tail = snd . fromMaybe (error "Cannot get tail at end of stream.") . uncons
   span :: (t -> Bool) -> s -> ([t], s)
   span p s = case uncons s of
                 Nothing    -> ([], s)
                 Just (h,t) -> if   p h
                               then let (a,b) = span p t
                                    in  (h:a,b)
                               else ([], s)
   stripPrefix :: Eq t => [t] -> s -> Maybe s
   stripPrefix []     s = Just s
   stripPrefix (x:xs) s = do (h,t) <- uncons s
                             if h == x
                              then stripPrefix xs t
                              else Nothing

instance IsLocationUpdatedBy (Int,Int) Char where
   advance (line,pos) c = case c of
                          '\n' ->  (line+1, 0) 
                          '\t' ->  (line  , pos + 8 - (pos-1) `mod` 8)
                          _    ->  (line  , pos + 1)

instance IsLocationUpdatedBy loc a => IsLocationUpdatedBy loc [a] where
   advance  = foldl advance 

instance (Show a,  loc `IsLocationUpdatedBy` a, Stream s a) => Provides  (Str a s loc)  (a -> Bool, String, a)  a where
       splitState (p, msg, a) k (Str  tts   msgs pos  del_ok) 
          = show_attempt ("Try Predicate: " ++ msg ++ "\n") (
            let ins exp =       (5, k a (Str tts (msgs ++ [Inserted (show a)  pos  exp]) pos  False))
                del exp =       (5, splitState (p,msg, a) 
                                    k
                                    (Str (tail tts) 
                                         (msgs ++ [Deleted  (show(head tts))  pos  exp]) 
                                         (advance pos (head tts))
                                         True ))
            in case uncons tts of
               Just (t,ts) ->  if p t 
                               then  show_symbol ("Accepting symbol: " ++ show t ++ " at position: " ++ show pos ++"\n") 
                                     (Step 1 (k t (Str ts msgs (advance pos t) True)))
                               else  Fail [msg] (ins: if del_ok then [del] else [])
               _           ->  Fail [msg] [ins]
            )

instance (Ord a, Show a, loc `IsLocationUpdatedBy`  a, Stream s a) => Provides  (Str  a s loc)  (a,a)  a where
       splitState a@(low, high) = splitState (\ t -> low <= t && t <= high, show low ++ ".." ++ show high, low)

instance (Eq a, Show a, loc `IsLocationUpdatedBy`  a, Stream s a) => Provides  (Str  a s loc)  a  a where
       splitState a  = splitState ((==a), show a, a) 

instance (Show a, Stream s a) => Eof (Str a s loc) where
       eof (Str  i        _    _    _    )                = null i
       deleteAtEnd (Str s msgs pos ok )                   = do (i,ii) <- uncons s
                                                               return (5, Str ii (msgs ++ [DeletedAtEnd (show i)]) pos ok)


instance  Stores (Str a s loc) (Error loc) where
       getErrors   (Str  inp      msgs pos ok    )     = (msgs, Str inp [] pos ok)

instance  HasPosition (Str a s loc) loc where
       getPos   (Str  inp      msgs pos ok    )        = pos

-- pMunch

data Munch a = Munch (a -> Bool) String

instance (Show a, loc `IsLocationUpdatedBy` [a], Stream s a) => Provides (Str a s loc) (Munch a) [a] where 
       splitState (Munch p x) k inp@(Str tts msgs pos del_ok)
          =    show_attempt ("Try Munch: " ++ x ++ "\n") (
               let (munched, rest) = span p tts
                   l               = length munched
               in if l > 0 then show_munch ("Accepting munch: " ++ x ++ " " ++ show munched ++  show pos ++ "\n") 
                                (Step l (k munched (Str rest msgs (advance pos munched)  (l>0 || del_ok))))
                           else show_munch ("Accepting munch: " ++ x ++ " as emtty munch " ++ show pos ++ "\n") (k [] inp)
               )

-- | Parse the longest prefix of tokens obeying the predicate.
pMunch :: (Provides st (Munch a) [a]) => (a -> Bool) -> P st [a]
pMunch  p   = pSymExt Zero Nothing  (Munch p "") -- the empty case is handled above
pMunchL p l = pSymExt Zero Nothing  (Munch p l) -- the empty case is handled above


data Token a = Token [a] Int -- the Int value represents the cost for inserting such a token

instance (Show a, Eq a, loc `IsLocationUpdatedBy` [a], Stream s a) => Provides (Str a s loc) (Token a) [a] where 
  splitState tok@(Token  as cost) k (Str tts msgs pos del_ok)
   =  let l = length as
          msg = show as 
      in  show_attempt ("Try Token: " ++ show as ++ "\n") (
          case stripPrefix as tts of
          Nothing  ->  let ins exp =  (cost, k as             (Str tts         (msgs ++ [Inserted msg               pos  exp])   pos    False))
                           del exp =  (5,    splitState tok k (Str (tail tts)  (msgs ++ [Deleted  (show(head tts))  pos  exp])  (advance pos [(head tts)]) True ))
                       in if null tts then  Fail [msg] [ins]
                                      else  Fail [msg] (ins: if del_ok then [del] else [])
          Just rest -> show_tokens ("Accepting token: " ++ show as ++"\n") 
                       (Step l (k as (Str rest msgs (advance pos as) True)))
          )

-- | Parse a list of primitive tokens (for example characters).
pToken :: (Provides state (Token a) token) => [a] -> P state token
pToken     as   =   pTokenCost as 5

-- | Parse a list of primitive tokens (for example characters) with a certain cost.
pTokenCost :: (Provides state (Token a) token) => [a] -> Int -> P state token
pTokenCost as c =   if L.null as then error "call to pToken with empty token"
                    else pSymExt (length as) Nothing (Token as c)
                    where length [] = Zero
                          length (_:as) = Succ (length as)

show_tokens :: String -> b -> b
show_tokens m v =   {- trace m -}  v

show_munch :: String -> b -> b
show_munch  m v =   {- trace m -}  v

show_symbol :: String -> b -> b
show_symbol m v =  {-  trace m -}  v

show_attempt m v = {- trace m -} v
