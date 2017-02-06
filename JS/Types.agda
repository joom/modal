module JS.Types where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  import Data.String
  open import Data.Nat.Show
  open import Data.List
  open import Data.List.Any
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  data Type : Set where
    `Undefined `Bool `Number `String : Type
    `Function : List Type → Type → Type
    `Object : List (Id × Type) → Type
    `Σt[t×[_×t]cont] : Type → Type

  data Hyp : Set where
    _⦂_<_> : (x : Id) (τ : Type) (w : World) → Hyp -- Value

  data Conc : Set where
    _<_> : (τ : Type) (w : World) → Conc -- Expression

  Context = List Hyp
