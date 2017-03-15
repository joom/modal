module ML5.Terms where

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
  open import Data.Integer
  open import Data.List hiding ([_])
  open import Data.List.Any
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import ML5.Types
  open import Definitions

  -- Valid values and values of the primitives of our language.
  data Prim : Hyp → Set where
    `alert : Prim ("alert" ⦂ ` `String ⇒ `Unit  < client >)
    `version : Prim ("version" ⦂ `String < server > )
    `log : Prim ("log" ∼ (λ _ → ` `String ⇒ `Unit))
    `prompt : Prim ("prompt" ⦂ ` `String ⇒ `String < client >)
    `readFile : Prim ("readFile" ⦂ ` `String ⇒ `String < server >)

  -- Terms that have to type check by definition.
  infixl 5 _⊢_
  data _⊢_ (Γ : Context) : Conc → Set where
    `tt : ∀ {w} → Γ ⊢ ↓ `Unit < w >
    `string : ∀ {w} → Data.String.String → Γ ⊢ ↓ `String < w >
    -- Boolean terms
    `true  : ∀ {w} → Γ ⊢ ↓ `Bool < w >
    `false : ∀ {w} → Γ ⊢ ↓ `Bool < w >
    `_∧_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `_∨_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `¬_  : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `if_`then_`else_ : ∀ {τ w} → Γ ⊢ `Bool < w > → Γ ⊢ τ < w > → Γ ⊢ τ < w > → Γ ⊢ τ < w >
    -- ℕ terms
    `n_  : ∀ {w} → ℤ → Γ ⊢ ↓ `Int < w >
    `_≤_ : ∀ {w} → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Bool < w >
    `_+_ : ∀ {w} → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w >
    `_*_ : ∀ {w} → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w >
    -- Abstraction & context terms
    `v : ∀ {τ w} → (x : Id) → x ⦂ τ < w > ∈ Γ → Γ ⊢ ↓ τ < w >
    `vval : ∀ {w C} → (u : Id) → u ∼ C ∈ Γ → Γ ⊢ ↓ C w < w >
    `_·_ : ∀ {τ σ w} → Γ ⊢ (` τ ⇒ σ) < w > → Γ ⊢ τ < w > → Γ ⊢ σ < w >
    `λ_⦂_⇒_ : ∀ {τ w} → (x : Id) (σ : Type) → (x ⦂ σ < w > ∷ Γ) ⊢ τ < w > → Γ ⊢ ↓ (` σ ⇒ τ) < w >
    -- Product and sum terms
    `_,_ : ∀ {τ σ w} → Γ ⊢ ↓ τ < w > →  Γ ⊢ ↓ σ < w > →  Γ ⊢ ↓ (` τ × σ) < w >
    `fst : ∀ {τ σ w} → Γ ⊢ (` τ × σ) < w > → Γ ⊢ τ < w >
    `snd : ∀ {τ σ w} → Γ ⊢ (` τ × σ) < w > → Γ ⊢ σ < w >
    `inl_`as_ : ∀ {τ w} → Γ ⊢ ↓ τ < w > → (σ : Type) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
    `inr_`as_ : ∀ {σ w} → Γ ⊢ ↓ σ < w > → (τ : Type) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
    `case_`of_⇒_||_⇒_ : ∀ {τ σ υ w} → Γ ⊢ (` τ ⊎ σ) < w > → (x : Id) → (x ⦂ τ < w > ∷ Γ) ⊢ υ < w >
                       → (y : Id) → (y ⦂ σ < w > ∷ Γ) ⊢ υ < w > → Γ ⊢ υ < w >
    -- At terms
    `hold : ∀ {τ w w'} → Γ ⊢ ↓ τ < w' > → Γ ⊢ ↓ (` τ at w') < w >
    `leta_`=_`in_ : ∀ {τ σ w w'} → (x : Id) → Γ ⊢ (` τ at w') < w > → ((x ⦂ τ < w' >) ∷ Γ) ⊢ σ < w > → Γ ⊢ σ < w >
    -- Shamrock terms
    `letsham_`=_`in_ : ∀ {σ w} {A : World → Type} → (u : Id) → Γ ⊢ `⌘ A < w > → (u ∼ A ∷ Γ) ⊢ σ < w > → Γ ⊢ σ < w >
    `sham : ∀ {w} {A : World → Type} → ((ω : World) → Γ ⊢ ↓ (A ω) < ω >) → Γ ⊢ ↓ `⌘ A < w >
    -- ∀ terms
    `Λ : ∀ {w} {A : World → Type} → ((ω : World) → Γ ⊢ ↓ A ω < w >) → Γ ⊢ ↓ `∀ A < w >
    _⟨_⟩ : ∀ {w} {A : World → Type} → Γ ⊢ `∀ A < w > → (ω : World) → Γ ⊢ (A ω) < w >
    -- ∃ terms
    `wpair : ∀ {w} {A : World → Type} (ω : World) → Γ ⊢ ↓ A ω < w > → Γ ⊢ ↓ `∃ A < w >
    `unpack_`=_`in_ : ∀ {w τ} {A : World → Type} (x : Id) → Γ ⊢ `∃ A < w > → ((ω : World) → ((x ⦂ A ω < w >) ∷ Γ) ⊢ τ < w >) → Γ ⊢ τ < w >
    -- Other
    `val : ∀ {τ w} → Γ ⊢ ↓ τ < w > → Γ ⊢ τ < w >
    `get : ∀ {τ w w'} {m : τ mobile} → Γ ⊢ τ < w' > → Γ ⊢ τ < w >
    `put : ∀ {C σ w} {m : (C w) mobile} (u : Id) → Γ ⊢ C w < w > → ((u ∼ C) ∷ Γ) ⊢ σ < w > → Γ ⊢ σ < w >
    -- Primitive imports
    `prim_`in_ : ∀ {h w σ} (x : Prim h) → (h ∷ Γ) ⊢ σ < w > → Γ ⊢ σ < w >
