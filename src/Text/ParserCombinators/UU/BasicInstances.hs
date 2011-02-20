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
import Data.Word
import Debug.Trace
import qualified Data.ListLike as LL

data Error  pos =    Inserted String pos        Strings
                   | Deleted  String pos        Strings
                   | Replaced String String pos Strings
                   | DeletedAtEnd String

instance (Show pos) => Show (Error  pos) where 
 show (Inserted s pos expecting)       = "-- >    Inserted  " ++  s ++  show_expecting  pos expecting 
 show (Deleted  t pos expecting)       = "-- >    Deleted   " ++  t ++  show_expecting  pos expecting
 show (Replaced old new pos expecting) = "-- >    Replaced  " ++ old ++ " by "++ new ++  show_expecting  pos expecting
 show (DeletedAtEnd t)                 = "-- >    The token " ++ t ++ " was not consumed by the parsing process."

show_errors :: (Show a) => [a] -> IO ()
show_errors = sequence_ . (map (putStrLn . show))

show_expecting :: (Show a) => a -> [String] -> String
show_expecting pos [a]    = " at position " ++ show pos ++ " expecting " ++ a
show_expecting pos (a:as) = " at position " ++ show pos ++ 
                            " expecting one of [" ++ a ++ concat (map (", " ++) as) ++ "]"
show_expecting pos []     = " expecting nothing"

data Str a s loc = Str { input    :: s
                       , msgs     :: [Error loc]
                       , pos      :: loc
                       , deleteOk :: !Bool}

type GenParser a r = LL.ListLike s a => P (Str a s loc) r

type Parser r = P (Str Char String (Int, Int)) r --GenParser Char r

createStr :: LL.ListLike s a => loc -> s -> Str a s loc
createStr loc ls = Str ls [] loc True

instance IsLocationUpdatedBy Int Char where
   advance pos _ = pos + 1
   
instance IsLocationUpdatedBy Int Word8 where
   advance pos _ = pos + 1
   
instance IsLocationUpdatedBy (Int,Int) Char where
   advance (line,pos) c = case c of
                          '\n' ->  (line+1, 0) 
                          '\t' ->  (line  , pos + 8 - (pos-1) `mod` 8)
                          _    ->  (line  , pos + 1)

instance IsLocationUpdatedBy loc a => IsLocationUpdatedBy loc [a] where
   advance  = foldl advance 

instance (Show a,  loc `IsLocationUpdatedBy` a, LL.ListLike s a) => Provides  (Str a s loc)  (a -> Bool, String, a)  a where
       splitState (p, msg, a) k (Str  tts   msgs pos  del_ok) 
          = show_attempt ("Try Predicate: " ++ msg ++ "\n") (
            let ins exp = (5, k a (Str tts (msgs ++ [Inserted (show a)  pos  exp]) pos  False))
            in if   LL.null tts 
               then Fail [msg] [ins]
               else let t       = LL.head tts
                        ts      = LL.tail tts
                        del exp = (5, splitState (p,msg, a) 
                                    k
                                    (Str ts 
                                         (msgs ++ [Deleted  (show t)  pos  exp]) 
                                         (advance pos t)
                                         True ))
                    in if p t
                       then  show_symbol ("Accepting symbol: " ++ show t ++ " at position: " ++ show pos ++"\n") 
                             (Step 1 (k t (Str ts msgs (advance pos t) True)))
                       else  Fail [msg] (ins: if del_ok then [del] else [])
            )

instance (Ord a, Show a, loc `IsLocationUpdatedBy`  a, LL.ListLike s a) => Provides  (Str  a s loc)  (a,a)  a where
       splitState a@(low, high) = splitState (\ t -> low <= t && t <= high, show low ++ ".." ++ show high, low)

instance (Eq a, Show a, loc `IsLocationUpdatedBy`  a, LL.ListLike s a) => Provides  (Str  a s loc)  a  a where
       splitState a  = splitState ((==a), show a, a) 

instance (Show a, LL.ListLike s a) => Eof (Str a s loc) where
       eof (Str  i        _    _    _    )              = LL.null i
       deleteAtEnd (Str s msgs pos ok )     | LL.null s = Nothing
                                            | otherwise = Just (5, Str (LL.tail s) (msgs ++ [DeletedAtEnd (show (LL.head s))]) pos ok)


instance  Stores (Str a s loc) (Error loc) where
       getErrors   (Str  inp      msgs pos ok    )     = (msgs, Str inp [] pos ok)

instance  HasPosition (Str a s loc) loc where
       getPos   (Str  inp      msgs pos ok    )        = pos

-- pMunch

data Munch a = Munch (a -> Bool) String

instance (Show a, loc `IsLocationUpdatedBy` [a], LL.ListLike s a) => Provides (Str a s loc) (Munch a) [a] where 
       splitState (Munch p x) k inp@(Str tts msgs pos del_ok)
          =    show_attempt ("Try Munch: " ++ x ++ "\n") (
               let (fmunch, rest)  = LL.span p tts
                   munched         = LL.toList fmunch
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

stripPrefixListLike :: (Eq item, LL.ListLike full item) => [item] -> full -> Maybe full
stripPrefixListLike []     s = Just s
stripPrefixListLike (x:xs) s = if   x == LL.head s
                               then stripPrefixListLike xs (LL.tail s)
                               else Nothing


instance (Show a, Eq a, loc `IsLocationUpdatedBy` a, LL.ListLike s a) => Provides (Str a s loc) (Token a) [a] where 
  splitState tok@(Token as cost) k (Str tts msgs pos del_ok)
   =  let l = length as
          msg = show as 
      in  show_attempt ("Try Token: " ++ show as ++ "\n") (
          case stripPrefixListLike as tts of
          Nothing  ->  let ins exp =  (cost, k as (Str tts (msgs ++ [Inserted msg pos exp]) pos False))
                       in if LL.null tts 
                          then  Fail [msg] [ins]
                          else  let t       = LL.head tts
                                    ts      = LL.tail tts
                                    del exp =  (5, splitState tok k 
                                                   (Str ts (msgs ++ [Deleted  (show t) pos exp]) 
                                                    (advance pos t) True))
                                in  Fail [msg] (ins: if del_ok then [del] else [])
          Just rest -> show_tokens ("Accepting token: " ++ show as ++"\n") 
                       (Step l (k as (Str rest msgs (advance pos as) True)))
          )

-- | Parse a list of primitive tokens (for example characters).
pToken :: (Provides state (Token a) token) => [a] -> P state token
pToken     as   =   pTokenCost as 5

-- | Parse a list of primitive tokens (for example characters) with a certain cost.
pTokenCost :: (Provides state (Token a) token) => [a] -> Int -> P state token
pTokenCost as c =   if null as then error "call to pToken with empty token"
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
