{-# LANGUAGE KindSignatures, GADTs, TypeFamilies #-}

module Diff.Play where

-- Type = Unit
--      | Long
--      | Boolean
--      | (Type, Type)
--      | Type => Type
--      | Map[Type, Type]
--      | Or3[Type, Type, Type]
--      | Diff[Type]      // should really be a type level function with Type as input, producing one of the other terms, as per below:
--
-- Note to self re identity changes: the paper does not define a unique identity element. Identity elements are with respect to a particular value.
-- So diff[A] in the worst case could be A, where A just represents the new item
--
--
--   diff[Unit]       = Unit
--   diff[Long]       = Long
--   diff[Boolean]    = Boolean
--   diff[(A,B)]      = (diff[A], diff[B])
--   diff[A => B]     = (A, diff[A]) => diff[B]
--   diff[Map[A,B]]   = Map[A, Or3[Unit, A, diff[A]]]
--   diff[Or3[A,B,C]] = Or3[diff[A], diff[B], diff[C]] or Or3[A,B,C] // need ability to change which alternative is present ... but what about the identity diff?
--   diff[Diff[A]]    = not meaningfull, as Diff shouldn't be an actual type, as per note above
--
-- Future types?
--      | String
--      | List[Type] and/or other collections of Type
--      | Map[Type, Type]
--      | records
--      | tuples of arbitrary arity
--      | optional types
--      | sum types


-- So, what's the plan?
-- GADT representing expressions in the language, type parameter reprenting type of expression
-- Change type class, representing change structures for types
-- type families in Change type class, representing output type of Derive transform
-- actual Derive function in Change type class

data Exp :: * -> * where
  Upd :: Change a => Exp a -> Exp (Derive a) -> Exp a
  Del :: Change a => Exp a -> Exp a -> Exp (Derive a)

  U :: Exp ()
  I :: Integer -> Exp Integer

  Tup :: Exp a -> Exp b -> Exp (a,b)
  InL :: Exp a -> Exp (Either a b)
  InR :: Exp b -> Exp (Either a b)

  -- So, how to evaluate variables?
  -- Maybe a pass to assign globally unique names before doing derivation?
  -- Doesn't guarantee that variable still exists in environment ...
  -- Maybe a pass to make every free variable reference capture variable before doing derivation?
  -- A free variable in what scope? Every variable is free in a small enough scope.
  -- Scope of lambdas? Is that enough? What about let bindings?
  -- Lambda and let are the only things which introduce named variables ... can I show that is enough?
  Lam :: Var -> Exp b -> Exp (a -> b)
  App :: Exp (a -> b) -> Exp a -> Exp b
  Let :: [Binding] -> Exp a -> Exp a
  Get :: Var -> Exp a

-- change structures
-- consider making Deriva a closed type family? Not even sure if current version is open or closed!

class Change a where
  type Derive a
  update :: Exp a -> Exp (Derive a) -> Exp a
  delta  :: Exp a -> Exp a -> Exp (Derive a)

instance (Change a, Change b) => Change (a -> b) where
  type Derive (a -> b) = a -> Derive a -> Derive b
  update f df = Let

instance (Change a, Change b) => Change (Either a b) where
  type Derive (Either a b) = Either (Either (Derive a) (Derive b)) (Either a b)

  update (InL ea) (InL (InL dea)) = InL $ update ea dea
  update (InL ea) (InR (InR eb))  = InR eb
  update (InR eb) (InL (InR deb)) = InR $ update eb deb
  update (InR eb) (InR (InL ea))  = InL ea

  delta  (InL xa) (InL ya)        = InL $ InL $ delta xa ya
  delta  (InL xa) (InR yb)        = InR $ InL xa
  delta  (InR xb) (InL ya)        = InR $ InR xb
  delta  (InR xb) (InR yb)        = InL $ InR $ delta xb yb

instance (Change a, Change b) => Change (a,b) where
  type Derive (a,b) = (Derive a, Derive b)
  update (Tup ea eb) (Tup dea deb) = Tup (update ea dea) (update eb deb)
  delta  (Tup xa xb) (Tup ya yb)   = Tup (delta  xa ya)  (delta  xb yb)

instance Change Integer where
  type Derive Integer = Integer
  update (I x) (I dx) = I (x + dx)
  delta  (I x) (I y)  = I (x - y)

instance Change () where
  type Derive () = ()
  update U U = U
  delta  U U = U

-- Vals
-- Untyped representation because not sure how to do environment any other way

class Val a where
  erase :: Exp a -> Untyped
  cast  :: Untyped -> Exp a

instance (Val a, Val b) => Val (Either a b) where
  erase (InL ea) = UInL $ erase ea
  erase (InR eb) = UInR $ erase eb
  cast (UInL ua) = InL  $ cast  ua
  cast (UInR ub) = InR  $ cast  ub

instance (Val a, Val b) => Val (a,b) where
  erase (Tup ea eb) = UTup (erase ea) (erase eb)
  cast (UTup ua ub) = Tup  (cast ua) (cast ub)

instance Val Integer where
  erase (I i) = UI i
  cast (UI i) = I  i

instance Val () where
  erase U = UU
  cast UU = U


-- all the crap that goes into making it work behind the scenes

data Untyped =
    UUpd Untyped Untyped
  | UDel Untyped Untyped
  | UU
  | UI Integer
  | UTup Untyped Untyped
  | UInL Untyped
  | UInR Untyped
  | ULam Var Untyped
  | UApp Untyped Untyped
  | ULet [Binding] Untyped
  | UGet Var

-- guarantee a separate namespace for vars and dvars
-- We don't have DVars in original program: scouts honour!
data Var = Var String | DVar String

data Binding = Bind Var Untyped

(:=) :: Val a => String -> Exp a -> Binding
name := term = Bind (Var name) $ erase term

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
