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
  open import Data.List renaming (_++_ to _+++_)
  open import Data.List.Properties using (∷-injective)
  open import Data.List.Any
  import Data.List.Any.Membership
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Vec hiding (_∈_)
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
  concatStr = Data.List.foldl Data.String._++_ ""

  concatVec : ∀ {n} → Vec String n → String
  concatVec = Data.Vec.foldl _ Data.String._++_ ""

  underscorePrefix : String → String
  underscorePrefix s = Data.String._++_ "_" s

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

  eq-replace : ∀ {a}{A B : Set a} → A ≡ B → A → B
  eq-replace refl x = x

  listDec : ∀ {a} {A : Set a}
           → ((x y : A) → Dec (x ≡ y))
           → (xs ys : List A)
           → Dec (xs ≡ ys)
  listDec dec [] [] = yes refl
  listDec dec [] (_ ∷ _) = no (λ ())
  listDec dec (_ ∷ _) [] = no (λ ())
  listDec dec (x ∷ xs) (y ∷ ys) with listDec dec xs ys
  ... | no p = no (p ∘ proj₂ ∘ ∷-injective )
  ... | yes p with dec x y
  listDec dec (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
  ... | no q = no (q ∘ proj₁ ∘ ∷-injective)

  ∷-++-assoc : ∀ {l} {A : Set l} (x : A) (xs ys : List A) → (x ∷ xs) +++ ys ≡ x ∷ (xs +++ ys)
  ∷-++-assoc x [] ys = refl
  ∷-++-assoc x (x' ∷ xs) ys = cong (λ l → x ∷ l) (∷-++-assoc x' xs ys)

  append-rh-[] : ∀ {l} {A : Set l} (xs : List A) → (xs +++ []) ≡ xs
  append-rh-[] [] = refl
  append-rh-[] (x ∷ xs) = cong (λ l → x ∷ l) (append-rh-[] xs)

  append-rh-[]-⊆ : ∀ {l} {A : Set l} (xs : List A) → xs ⊆ (xs +++ [])
  append-rh-[]-⊆ xs rewrite append-rh-[] xs = id
