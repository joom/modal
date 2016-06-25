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
  open import Data.String
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

  concatStr : List String → String
  concatStr = foldl (Data.String._++_) ""

  data World : Set where
    client : World
    server : World

  _decW_ : (w : World) → (w' : World) → Dec (w ≡ w')
  client decW client = yes refl
  server decW server = yes refl
  client decW server = no (λ ())
  server decW client = no (λ ())

  postulate
    extensionality : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
  cong₃ f refl refl refl = refl
