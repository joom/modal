module ML5.Types where

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
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  data Type : Set where
    `Nat `Bool `Unit `String : Type
    `_⇒_ `_×_ `_⊎_ : Type → Type → Type
    `_at_ : Type → World → Type
    `_addr : World → Type
    `⌘ : (World → Type) → Type -- Shamrock
    `∀ `∃ : (World → Type) → Type

  data Hyp : Set where
    _⦂_<_> : (x : Id) (τ : Type) (w : World) → Hyp -- Value
    _∼_ : (u : Id) → (World → Type) → Hyp -- Valid

  data Conc : Set where
    _<_> : (τ : Type) (w : World) → Conc -- Expression
    ↓_<_> : (τ : Type) (w : World) → Conc -- Value

  Context = List Hyp

  data _mobile : Type → Set where
    `Boolᵐ : `Bool mobile
    `Natᵐ : `Nat mobile
    `Unitᵐ : `Unit mobile
    `Stringᵐ : `String mobile
    `_atᵐ_ : ∀ {A w} → (` A at w) mobile
    `_×ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A × B) mobile
    `_⊎ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A ⊎ B) mobile
    `∀ᵐ : ∀ {A} → A mobile → (`∀ (λ _ → A)) mobile
    `∃ᵐ : ∀ {A} → A mobile → (`∃ (λ _ → A)) mobile
    `⌘ᵐ : ∀ {A} → (`⌘ (λ _ → A)) mobile
    _addrᵐ : ∀ {w} → (` w addr) mobile
