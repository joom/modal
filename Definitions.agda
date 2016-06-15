module Definitions where

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
  open import Data.Empty
  open import Function

  isJust : ∀ {ℓ} {A : Set ℓ} → Maybe A → Set
  isJust (just _) = Data.Unit.⊤
  isJust _ = ⊥

  fromJust : ∀ {ℓ} {A : Set ℓ} → (m : Maybe A) → isJust m → A
  fromJust (just x) _ = x
  fromJust nothing ()

  Id = Data.String.String

  data World : Set where
    client : World
    server : World

  postulate
    extensionality : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

  -- Not exactly subset in the mathematical sense,
  -- more like non-strict suffix of a list. This is enough for what we need.
  -- data _⊆_ {A : Set} : List A → List A → Set where
  --   refl : ∀ {xs} → xs ⊆ xs
  --   step : ∀ {y xs ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)

  -- Subset definition that we can also use for our contexts,
  -- since we check membership by named representations.
  _⊆_under_ : {A B : Set} → List A → List A → (_∈_ : B → List A → Set) → Set
  xs ⊆ ys under _∈_ = ∀ {b} → b ∈ xs → b ∈ ys

  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
  cong₃ f refl refl refl = refl
