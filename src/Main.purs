module Main where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Leibniz (type (~), coerce)
import Debug.Trace (traceM)
import Effect (Effect)
import Prim.Row (class Cons, class Lacks)
import Record (get)
import Type.Data.Symbol (SProxy(..))
import Type.Prelude (class IsSymbol)
import Unsafe.Coerce (unsafeCoerce)

foreign import data Exists2 ∷ (Type → Type → Type) → Type

mkExists2 ∷ ∀ f a b. f a b → Exists2 f
mkExists2 = unsafeCoerce

runExists2 ∷ ∀ f r. (∀ a b. f a b → r) → Exists2 f → r
runExists2 = unsafeCoerce

data Lam ctx o' i o = Lam (Expr ctx i → Expr ctx o) ((i → o) ~ o')
data App ctx o i = App (Expr ctx (i → o)) (Expr ctx i)
data Arr ctx a e = Arr (Array (Expr ctx e)) (Array e ~ a)

data EqExpr ctx i = EqExpr (Expr ctx i) (Expr ctx i) (i → i → Boolean)

data Expr ctx a
  = ELit a
  | EAdd (Expr ctx a) (Expr ctx a) (a → a → a)
  | ESub (Expr ctx a) (Expr ctx a) (a → a → a)
  | EMul (Expr ctx a) (Expr ctx a) (a → a → a)
  | EDiv (Expr ctx a) (Expr ctx a) (a → a → a)
  | EMod (Expr ctx a) (Expr ctx a) (a → a → a)
  | EAppend (Expr ctx a) (Expr ctx a) (a → a → a)
  | EArray (Exists (Arr ctx a))
  | EIfThenElse (Expr ctx Boolean) (Expr ctx a) (Expr ctx a)
  | EEq (Exists (EqExpr ctx)) (Boolean ~ a)
  | ENode
      (Expr ctx String)
      (Expr ctx (Array (Node String)))
      (Node String ~ a)
  | Var (Record ctx → a)
  | ELam (Exists2 (Lam ctx a))
  | EApp (Exists (App ctx a))


data Node n
  = Node n (Array (Node n))
  | Render String

eq' ∷ ∀ ctx a. Eq a ⇒ Expr ctx a → Expr ctx a → Expr ctx Boolean
eq' e1 e2 = EEq (mkExists (EqExpr e1 e2 eq)) identity

_x = SProxy ∷ SProxy "x"
_y = SProxy ∷ SProxy "y"
_z = SProxy ∷ SProxy "z"

var ∷ ∀ a ctx ctx' s
  . Lacks s ctx
  ⇒ Cons s a ctx ctx'
  ⇒ (IsSymbol s) ⇒ SProxy s → Expr ctx' a
var s = Var (get s)

node ∷ ∀ ctx. String → Array (Expr ctx (Node String)) → Expr ctx (Node String)
node tag children = ENode (ELit tag) (EArray (mkExists (Arr children identity))) identity

if_ ∷ ∀ a ctx. Expr ctx Boolean → Expr ctx a → Expr ctx a → Expr ctx a
if_ c t f = EIfThenElse c t f

lambda ∷ ∀ ctx i o. (Expr ctx i →  Expr ctx o) → Expr ctx (i → o)
lambda f = ELam (mkExists2 (Lam f identity))

app ∷ ∀ ctx i o. (Expr ctx (i → o)) → Expr ctx i → Expr ctx o
-- app (ELam l) x =
--   runExists2 (\(Lam f _) → f x) l
-- (runExists2 (\(Lam f proof) → (coerce proof \x → interpret ctx (f x))) l)
app l arg = EApp (mkExists (App l arg))

instance monoidExpr ∷ Monoid a ⇒ Monoid (Expr ctx a) where
  mempty = ELit mempty

instance semigroupExpr ∷ Semigroup a ⇒ Semigroup (Expr ctx a) where
  append e1 e2 = EAppend e1 e2 append

instance semiringExprNum ∷ Semiring a ⇒ Semiring (Expr ctx a) where
  zero = ELit zero
  add e1 e2 = EAdd e1 e2 add
  one = ELit one
  mul e1 e2 = EMul e1 e2 mul

instance ringExpr ∷ Ring a ⇒ Ring (Expr ctx a) where
  sub e1 e2 = ESub e1 e2 sub

instance commutativeRingExprNum ∷ CommutativeRing a ⇒ CommutativeRing (Expr ctx a)

instance euclideanRingExprNum ∷ EuclideanRing (Expr ctx Number) where
  degree _ = 1
  div e1 e2 = EDiv e1 e2 div
  mod e1 e2 = EMod e1 e2 mod

interpretBinary ∷ ∀ a ctx. (a → a → a) → Record ctx → Expr ctx a → Expr ctx a → a
interpretBinary op ctx e1 e2 = op (interpret ctx e1) (interpret ctx e2)

interpret ∷ ∀ a ctx. Record ctx → Expr ctx a → a
interpret ctx (ELit a) = a
interpret ctx (EAdd e1 e2 add) = interpretBinary add ctx e1 e2
interpret ctx (ESub e1 e2 sub) = interpretBinary sub ctx e1 e2
interpret ctx (EMul e1 e2 mul) = interpretBinary mul ctx e1 e2
interpret ctx (EDiv e1 e2 div) = interpretBinary div ctx e1 e2
interpret ctx (EMod e1 e2 mod) = interpretBinary mod ctx e1 e2
interpret ctx (EEq exp proof) =
  runExists (\(EqExpr e1 e2 eq) → coerce proof (eq (interpret ctx e1) (interpret ctx e2))) exp
interpret ctx (EAppend s1 s2 append) = interpretBinary append ctx s1 s2
interpret ctx (EArray a) = runExists (\(Arr arr proof) → coerce proof (map (interpret ctx) arr)) a
interpret ctx (EIfThenElse c t f) =
  if (interpret ctx c)
  then (interpret ctx t)
  else (interpret ctx f)
interpret ctx (Var get) = (get ctx)
interpret ctx (EApp a) = runExists (\(App l arg) → (interpret ctx l) (interpret ctx arg)) a
interpret ctx (ELam l) =
  (runExists2 (\(Lam f proof) → (coerce proof \x → interpret ctx (f (ELit x)))) l)
interpret ctx (ENode name children proof) =
  let
    n = interpret ctx name
    c = interpret ctx children
  in
    coerce proof (Node n c)


template = EIfThenElse (var _x `eq'` ELit 8) (ELit 9) (ELit 10)

boolean = \x → node "div"
  [ if_ (x `eq'` ELit 8)
      (node "true" [])
      (node "false" [])
  ]

html ∷ Expr (x ∷ Int, y ∷ Int) (Node String)
html = node "div"
  [ boolean (var _x)
  , boolean (var _y)
  ]

main ∷ Effect Unit
main = do
  traceM html
