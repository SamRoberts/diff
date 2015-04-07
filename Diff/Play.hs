{-# LANGUAGE KindSignatures, GADTs, TypeFamilies #-}

module Diff.Play where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.State (State, evalState)
import Data.Dynamic (Dynamic, cast, fromDynamic)
import qualified Data.Map as M
import Data.Maybe (maybe)
import Data.Typeable (Typeable)


-----------------------------
-- Type of diffs
-----------------------------

-- Ideally would be a closed type family, but need to update GHC and can't be bothered to do that now

class Diff a where
  type D a

instance Diff () where
  type D () = ()

instance Diff Integer where
  type D Integer = Integer

instance (Diff a, Diff b) => Diff (a,b) where
  type D (a,b) = (D a, D b)

instance (Diff a, Diff b) => Diff (Either a b) where
  type D (Either a b) = Either (Either (D a) (D b)) (Either a b)

instance (Diff a, Diff b) => Diff (a -> b) where
  type D (a -> b) = a -> D a -> D b

-----------------------------
-- Syntax
-----------------------------

data Exp :: * -> * where
  -- change structures
  Upd :: Change a => Exp a -> Exp (D a) -> Exp a
  Del :: Change a => Exp a -> Exp a -> Exp (D a)

  -- unit
  U :: Exp ()

  -- integers
  I :: Integer -> Exp Integer
  Add :: Exp Integer -> Exp Integer -> Exp Integer

  -- tuples
  Tup :: Exp a -> Exp b -> Exp (a,b)
  Fst :: Exp (a,b) -> Exp a
  Snd :: Exp (a,b) -> Exp b

  -- eithers
  InL :: Exp a -> Exp (Either a b)
  InR :: Exp b -> Exp (Either a b)
  FoldE :: Exp (a -> c) -> Exp (b -> c) -> Exp (Either a b) -> Exp c

  -- lambda calculus
  Lam :: Exp b -> Exp (a -> b)
  App :: Exp (a -> b) -> Exp a -> Exp b
  Get :: Var -> Exp a


-- VSpace "guarantees" a separate namespace for vars and dvars
-- We don't have Delta in original program: scouts honour!
data Var =
    BVar VSpace Int
  | FVar VSpace String

data VSpace = Whole | Delta

freeNames :: [Var]
freeNames = FVar Whole <$> (flip replicateM ['a'..'z'] =<< [1..])


-----------------------------
-- Evaluation
-----------------------------

-- untyped environment
data Env = Map Var Dynamic

lookup :: Typeable a => Var -> Env -> Maybe (Exp a)
lookup var = fromDynamic <=< M.lookup var

data TypeErr = TypeErr
               { teEnvVal :: Maybe (Var, TypeRep)
               , teGetVal :: (Var, TypeRep)
               }

data ErrUnbound =
  ErrUnbound
  { eUnbound :: Exp ()
  , eDepth   :: Int
  }

validate :: Exp a -> Either ErrUnbound (Exp a)
validate = vmapM checkVar
  where
    checkVar depth (BVar s n) | n <  depth = return $ BVar s n
                              | s >= depth = Left $ ErrUnbound (BVar s n) depth
    checkVar depth (FVar s n)              = Left $ ErrUnbound (FVar s n) depth

-- Is this the signature I want? Need to know what type Var points to to actually map over it ...
vmapM :: (Typeable a, Monad m) => (Int -> Var -> m (Exp b)) -> Exp a -> m (Exp a)
vmapM f = go 0
  where
    tf :: Int -> Exp b -> m (Exp b)
    tf n (Get v) = f n v

    go i (Upd x dx)    = Upd <$> go i x <*> uniq i dx
    go i (Del x y)     = Del <$> go i x <*> go i y
    go _ U             = return U
    go _ (I i)         = return $ I i
    go i (Add x y)     = Add <$> go i x <*> go i y
    go i (Tup x y)     = Tup <$> go i x <*> go i y
    go i (Fst x)       = Fst <$> go i x
    go i (Snd x)       = Snd <$> go i x
    go i (InL x)       = InL <$> go i x
    go i (InR y)       = InR <$> go i y
    go i (FoldE f g x) = FoldE <$> go i f <*> go i g <*> go i x
    go i (App f x)     = App <$> go i f <*> go i x
    go i (Lam b)       = Lam <$> go (i+1) b
    -- Does the cast work? Is it necesary?
    --go i (Get v)       = maybe (return $ Get v) (f i) $ cast (Get v)
    -- this *should* be a compile error, I think
    go i (Get v)       = f i v


-- update and delta
-- these are evaluation functions. constructors are syntax.
{-
update :: Change a => Exp a -> Exp (D a) -> Exp a
update (Add ea dea1) dea2       =
update (InL ea) (InL (InL dea)) = InL $ update ea dea
update (InL ea) (InR (InR eb))  = InR eb
update (InR eb) (InL (InR deb)) = InR $ update eb deb
update (InR eb) (InR (InL ea))  = InL ea
update (Tup ea eb) (Tup dea deb) = Tup (update ea dea) (update eb deb)
update (I x) (I dx) = I (x + dx)
update U U = U


delta :: Change a => Exp a -> Exp a -> Exp (D a)
delta  (InL xa) (InL ya)        = InL $ InL $ delta xa ya
delta  (InL xa) (InR yb)        = InR $ InL xa
delta  (InR xb) (InL ya)        = InR $ InR xb
delta  (InR xb) (InR yb)        = InL $ InR $ delta xb yb
delta  (Tup xa xb) (Tup ya yb)   = Tup (delta  xa ya)  (delta  xb yb)
delta  (I x) (I y)  = I (x - y)
delta  U U = U


-----------------------------
-- Printing
-----------------------------

instance Show Var where
  show (Var x)  = x
  show (DVar x) = "d" ++ x

instance Show Binding where
  show (Bind var term) = show var ++ " = " ++ show term

-- need to have some sort of priority so I can avoid spurious brackets
-- need to have some sort of "margin", so I can properly nest indented things
-- in absense of margin, show let bindings is going to be some ugly all-on-one-line thing
-- doing show on untyped repr, because we need to show let beindings, which
-- are untyped anyway
instance Val a => Show (Exp a) where
  show = show . erase

instance Show Untyped where
  show (UUpd ea dea) = show ea ++ " + " ++ show dea
  show (UDel xa ya)  = show xa ++ " - " ++ show ya
  show UU            = "()"
  show (UI i)        = show i
  show (UTup ea eb)  = "(" ++ show ea ++ "," ++ show eb ++ ")"
  show (UInL ea)     = "↰ " ++ show ea
  show (UInR eb)     = "↱ " ++ show eb
  show (ULam va eb)  = "λ" ++ show va ++ " → " ++ show eb
  show (UApp ef ea)  = "(" ++ show ef ++ ") (" ++ show ea ++ ")"
  show (ULet bs ea)  = "let " ++ intercalate "; " (map show bs) ++ " in " ++ show ea
  show (UGet va)     = show va
-}
