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
  open import Data.List hiding ([_])
  open import Data.List.Any
  open import Data.Vec
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  data Type : Set where
    `Undefined `Bool `Number `String : Type
    `Function : ∀ {n} → Vec Type n → Type → Type
    `Object : List (Id × Type) → Type

  data Hyp : Set where
    _⦂_<_> : (x : Id) (τ : Type) (w : World) → Hyp -- Value
    -- _∼_ : (u : Id) → (World → Type) → Hyp -- Valid

  data Conc : Set where
    _<_> : (τ : Type) (w : World) → Conc -- Expression
    -- ↓_<_> : (τ : Type) (w : World) → Conc -- Value

  Context = List (List Hyp)

  _∈ⱼ_ : Hyp → Context → Set
  h ∈ⱼ Γ = Data.List.Any.Any (Membership-≡._∈_ h) Γ
