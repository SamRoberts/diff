{-# LANGUAGE DeriveFunctor, ViewPatterns #-}

module Diff.Play where

import           Control.Applicative (Applicative, (<$>), (<*>))
import           Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromJust) -- TODO remove need for this function
import           Data.Text (Text)
import qualified Data.Text as T

-----------------------------
-- Types
-----------------------------

data Typ =
    TU
  | TI
  | Typ :*:  Typ
  | Typ :+:  Typ
  | Typ :->: Typ
  deriving (Show, Eq)

diff :: Typ -> Typ
diff TU         = TU
diff TI         = TI
diff (x :*:  y) = diff x :*: diff y
diff (x :+:  y) = (diff x :+: diff y) :+: (x :+: y)
diff (x :->: y) = x :->: (diff x :->: diff y)

-----------------------------
-- Expressions
-----------------------------

data Exp =
  -- unit
    U                 -- TU

  -- integers
  | I Integer         -- TI
  | Add Exp Exp       -- TI -> TI -> TI

  -- tuples
  | Tup Exp Exp       -- t -> u -> t :*: u
  | Fst Exp           -- t :*: u -> t
  | Snd Exp           -- t :*: u -> u

  -- eithers
  | InL Exp Typ       -- t -> t :+: u
  | InR Typ Exp       -- u -> t :+: u
  | FoldE Exp Exp Exp -- (t :->: a) -> (u :->: a) -> (t :+: u) -> a

  -- changes
  | Upd Exp Exp       -- t -> (diff t) -> t
  | Dif Exp Exp       -- t -> t -> diff t

-- lambda calculus
  | App Exp Exp       -- (a :->: t) -> a -> t
  | Lam Var Exp       -- na -> t -> (a :->: t)
  | Ref Var           -- nt -> t
  deriving (Show, Eq)

data Var = Var Typ Name deriving (Show, Eq)
data Name = Name Text Integer deriving (Show, Eq, Ord)

data Env = Env (Map Name Exp) deriving (Show, Eq)

emptyEnv = Env M.empty

addBind :: Name -> Exp -> Env -> Env
addBind name exp (Env env) = Env $ M.insert name exp env


-----------------------------
-- Constructors
-----------------------------

letIn :: Var -> Exp -> (Exp -> Exp) -> Exp
letIn n a x = App (Lam n (x (Ref n))) a

var :: Text -> Typ -> Var
var name typ = Var typ (Name name 0)

-----------------------------
-- General utilities
-----------------------------

distributeA :: Applicative a => (Exp -> a Exp) -> Exp -> a Exp
distributeA _ U         = pure U
distributeA _ (I i)     = pure $ I i
distributeA f (Add x y) = Add <$> f x <*> f y
distributeA f (Tup x y) = Tup <$> f x <*> f y
distributeA f (Fst x)   = Fst <$> f x
distributeA f (Snd x)   = Snd <$> f x
distributeA f (InL x t) = InL <$> f x <*> pure t
distributeA f (InR t x) = InR <$> pure t <*> f x
distributeA f (FoldE x y z) = FoldE <$> f x <*> f y <*> f z
distributeA f (Upd x y) = Upd <$> f x <*> f y
distributeA f (Dif x y) = Dif <$> f x <*> f y
distributeA f (App x y) = App <$> f x <*> f y
distributeA f (Lam n x) = Lam n <$> f x
distributeA _ (Ref n)   = pure $ Ref n

-----------------------------
-- Sanity checks
-----------------------------

-- placeholder type check error
data TypeError = TypeError deriving (Show, Eq)

-- type check WITHOUT CHECKING NAMES
-- need separate pass to ensure consistency of names
-- suggestion: 1) typCheck, 2) unique names, 3) consistency of names
typeCheck :: Exp ->  Either TypeError Typ
typeCheck = ty
  where
    ty U                                                          = Right TU

    ty (I _)                                                      = Right TI
    ty (Add (ty -> Right TI) (ty -> Right TI))                    = Right TI

    ty (Tup (ty -> Right u) (ty -> Right v))                      = Right (u :*: v)
    ty (Fst (ty -> Right (u :*: _)))                              = Right u
    ty (Snd (ty -> Right (_ :*: v)))                              = Right v

    ty (FoldE (ty -> Right (u1 :->: t1)) (ty -> Right (v2 :->: t2)) (ty -> Right (u3 :+: v3))) | u1 == u3 && v2 == v3 && t1== t2 = Right t1
    ty (InL (ty -> Right u) v)                                    = Right (u :+: v)
    ty (InR u (ty -> Right v))                                    = Right (u :+: v)

    ty (App (ty -> Right (u1 :->: t)) (ty -> Right u2)) | u1 == u2 = Right t
    ty (Lam (Var u _) (ty -> Right t))                            = Right (u :->: t)
    ty (Ref (Var t _))                                            = Right t

    ty (Upd (ty -> Right t) (ty -> Right dt)) | dt == diff t      = Right t
    ty (Dif (ty -> Right t1) (ty -> Right t2)) | t1 == t2         = Right (diff t1)

    ty _                                                          = Left TypeError

-- assumes that the numbers in Names are meaningless
-- and assigns unique
uniqNames :: Exp -> Exp
uniqNames x = S.evalState (go M.empty x) M.empty
  where
    fresh :: Text -> State (Map Text Name) Name
    fresh name = S.state $ \olds ->
      let new = maybe (Name name 0) (\(Name _ i) -> Name name (i+1)) (M.lookup name olds)
          updated = M.insert name new olds
      in (new, updated)

    go :: Map Text Name -> Exp -> State (Map Text Name) Exp
    go fullNames (Lam (Var typ (Name name _)) body) = do
      freshName <- fresh name
      Lam (Var typ freshName) <$> go (M.insert name freshName fullNames) body

    -- TODO need additional effect to handle name not found error!
    go fullNames (Ref (Var typ (Name name _))) = return $ Ref $ Var typ $ fromJust $ M.lookup name fullNames

    go fullNames other = distributeA (go fullNames) other

