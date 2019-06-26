module Solder.ExprF where

import Prelude

import Control.Monad.Free (Free, foldFree, liftF)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.CatList (CatList)
import Main (Expr(..))
import Text.Smolder.Markup (Attr)

data NS = HTMLns | SVGns

data EventHandler e = EventHandler String e

instance functorEventHandler ∷ Functor EventHandler where
  map f (EventHandler s e) = EventHandler s (f e)

data MarkupM ctx e a
  = Element NS String (Markup ctx e) (CatList (Expr ctx Attr)) (CatList (EventHandler e)) a
  | Content (Expr ctx String) a
  | Empty a

type Markup ctx e = Free (MarkupM ctx e) Unit

instance bifunctorMarkupM :: Bifunctor (MarkupM ctx) where
  bimap l r (Empty a) = Empty (r a)
  bimap l r (Content t a) = Content t (r a)
  bimap l r (Element ns el kids attrs events a) =
    Element ns el (mapEvent l kids) attrs (map l <$> events) (r a)

-- | Change the event type of a markup sequence.
mapEvent :: ∀ ctx l r. (l → r) → Free (MarkupM ctx l) ~> Free (MarkupM ctx r)
mapEvent f fm = foldFree (\m → liftF $ lmap f m) fm

-- | Create a named parent node with a sequence of children.
parent :: ∀ ctx e. NS → String → Markup ctx e → Markup ctx e
parent ns el kids = liftF $ Element ns el kids mempty mempty unit

-- | Create a named leaf node.
leaf :: ∀ ctx e. NS → String → Markup ctx e
leaf ns el = liftF $ Element ns el (liftF $ Empty unit) mempty mempty unit

-- | Create a text node.
text :: ∀ ctx e. String → Markup ctx e
text s = liftF $ Content (ELit s) unit

-- | Used for empty nodes (without text or children)
empty :: ∀ ctx e. Markup ctx e
empty = liftF $ Empty unit

