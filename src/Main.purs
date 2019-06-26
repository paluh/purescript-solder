module Main where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Foldable (foldMap)
import Data.Leibniz (type (~), coerce)
import Debug.Trace (traceM)
import Effect (Effect)
import Prim.Row (class Cons, class Lacks)
import Record (get)
import Text.Smolder.Markup (Attr, NS(..))
import Type.Data.Symbol (SProxy(..))
import Type.Prelude (class IsSymbol)

data BinOpExpr ctx a i = BinOpExpr (Expr ctx i) (Expr ctx i) (i → i → a)

data Expr ctx a
  = ELit a
  | BinOp (Exists (BinOpExpr ctx a))
  | EIfThenElse (Expr ctx Boolean) (Expr ctx a) (Expr ctx a)
  | EElem
      NS
      String
      (Array (Expr ctx Markup))
      (Array (Expr ctx Attr))
      (Markup ~ a)
  | EVar (Record ctx → a)

data Markup
  = Element NS String (Array Markup) (Array Attr)
  -- | Content String
  -- | Empty

eq' ∷ ∀ ctx a. Eq a ⇒ Expr ctx a → Expr ctx a → Expr ctx Boolean
eq' e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 eq)

var ∷ ∀ a ctx ctx' s
  . Lacks s ctx
  ⇒ Cons s a ctx ctx'
  ⇒ (IsSymbol s) ⇒ SProxy s → Expr ctx' a
var s = EVar (get s)

elem ∷ ∀ ctx. String → Array (Expr ctx Markup) → Expr ctx Markup
elem el kids = EElem HTMLns el kids [] identity

if_ ∷ ∀ a ctx. Expr ctx Boolean → Expr ctx a → Expr ctx a → Expr ctx a
if_ c t f = EIfThenElse c t f

instance monoidExpr ∷ Monoid a ⇒ Monoid (Expr ctx a) where
  mempty = ELit mempty

instance semigroupExpr ∷ Semigroup a ⇒ Semigroup (Expr ctx a) where
  append e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 (<>))

instance semiringExprNum ∷ Semiring a ⇒ Semiring (Expr ctx a) where
  zero = ELit zero
  add e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 (+))
  one = ELit one
  mul e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 (*))

instance ringExpr ∷ Ring a ⇒ Ring (Expr ctx a) where
  sub e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 (-))

instance commutativeRingExprNum ∷ CommutativeRing a ⇒ CommutativeRing (Expr ctx a)

instance euclideanRingExprNum ∷ EuclideanRing (Expr ctx Number) where
  degree _ = 1
  div e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 (/))
  mod e1 e2 = BinOp (mkExists $ BinOpExpr e1 e2 mod)

interpretBinary ∷ ∀ a ctx. (a → a → a) → Record ctx → Expr ctx a → Expr ctx a → a
interpretBinary op ctx e1 e2 = op (interpret ctx e1) (interpret ctx e2)

interpret ∷ ∀ a ctx. Record ctx → Expr ctx a → a
interpret ctx (ELit a) = a
interpret ctx (BinOp b) =
  runExists (\(BinOpExpr e1 e2 f) → (f (interpret ctx e1) (interpret ctx e2))) b
interpret ctx (EIfThenElse c t f) =
  if (interpret ctx c)
  then (interpret ctx t)
  else (interpret ctx f)
interpret ctx (EVar get) = (get ctx)
interpret ctx (EElem ns el kids attrs proof) =
  let
    kids' = map (interpret ctx) kids
    attrs' = map (interpret ctx) attrs
  in
    coerce proof (Element ns el kids' attrs')

data Eval ctx a
  = Val a
  | Compute a (Record ctx → a) a

instance semigroupEval ∷ Semigroup a ⇒ Semigroup (Eval ctx a) where
  append (Val a1) (Val a2) = Val $ a1 <> a2
  append (Compute a1 f a2) (Val a3) = Compute a1 f (a2 <> a3)
  append (Val a1) (Compute a2 f a3) = Compute (a1 <> a2) f a3
  append (Compute a1 f1 a2) (Compute a3 f2 a4) =
    let
      a' = a2 <> a3
      f ctx = f1 ctx <> a' <> f2 ctx
    in
      Compute a1 f a4

instance monoidEval ∷ Monoid a ⇒ Monoid (Eval ctx a) where
  mempty = Val mempty

run ∷ ∀ a ctx. Semigroup a ⇒ Record ctx → Eval ctx a → a
run _ (Val a) = a
run ctx (Compute a1 f a2) = a1 <> f ctx <> a2

ser :: Markup -> String
ser (Element ns el kids attrs) =
  "<" <> el <> ">" <> foldMap ser kids <> "</" <> el <> ">"

eval ∷ ∀ ctx. Expr ctx Markup → Eval ctx String
eval (EElem ns el kids attrs _) =
  (Val $ "<" <> el <> ">") <> (foldMap eval kids) <> (Val $ "</" <> el <> ">")
eval (EIfThenElse c t f) =
  let
    t' = eval t
    f' = eval f
    g ctx = if (interpret ctx c)
      then run ctx t'
      else run ctx f'
  in
    Compute mempty g mempty
eval (ELit m) = Val (ser m)
eval expr = Compute mempty (\ctx → ser (interpret ctx expr)) mempty

_x = SProxy ∷ SProxy "x"
_y = SProxy ∷ SProxy "y"
_z = SProxy ∷ SProxy "z"

template ∷ Expr ( x ∷ Int) Int
template = EIfThenElse (var _x `eq'` ELit 8) (ELit 9) (ELit 10)

add' ∷ Expr (x ∷ Int, y ∷ Int) Int
add' = var _x  + var _y

boolean ∷ ∀ ctx. Expr ctx Int → Expr ctx Markup
boolean = \x → elem "div"
  [ if_ (x `eq'` ELit 8)
      (elem "true" [])
      (elem "false" [])
  ]

html ∷ Expr (x ∷ Int, y ∷ Int) Markup
html = elem "div"
  [ boolean (var _x)
  , boolean (var _y)
  ]

main ∷ Effect Unit
main = do
  traceM html
  traceM (eval html)
  traceM (interpret { x: 8, y: 10 } add')
