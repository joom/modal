module CPS.Terms where

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

  open import CPS.Types
  open import Definitions

  -- Valid values and values of the primitives of our language.
  primHyp : Id → Maybe Hyp
  primHyp "alert" = just ("alert" ⦂ ` `String cont  < client >)
  primHyp "version" = just ("version" ⦂ `String < server > )
  primHyp "log" = just ("log" ∼ (λ _ → ` `String cont))
  primHyp _ = nothing

  -- Terms that have to type check by definition.
  infixl 5 _⊢_
  data _⊢_ (Γ : Context) : Conc → Set where
    `tt : ∀ {w} → Γ ⊢ ↓ `Unit < w >
    -- Boolean values
    `true  : ∀ {w} → Γ ⊢ ↓ `Bool < w >
    `false : ∀ {w} → Γ ⊢ ↓ `Bool < w >
    `_∧_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `_∨_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `¬_  : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    -- `if_`then_`else_ : ∀ {τ w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ τ < w > → Γ ⊢ τ < w > → Γ ⊢ τ < w >
    -- ℕ values
    `n_  : ∀ {w} → ℕ → Γ ⊢ ↓ `Nat < w >
    `_≤_ : ∀ {w} → Γ ⊢ ↓ `Nat < w > → Γ ⊢ ↓ `Nat < w > → Γ ⊢ ↓ `Bool < w >
    `_+_ : ∀ {w} → Γ ⊢ ↓ `Nat < w > → Γ ⊢ ↓ `Nat < w > → Γ ⊢ ↓ `Nat < w >
    `_*_ : ∀ {w} → Γ ⊢ ↓ `Nat < w > → Γ ⊢ ↓ `Nat < w > → Γ ⊢ ↓ `Nat < w >
    -- Abstraction & context values
    `v : ∀ {τ w} → (x : Id) → x ⦂ τ < w > ∈ Γ → Γ ⊢ ↓ τ < w >
    `vval : ∀ {τ w C} → (u : Id) → u ∼ C ∈ Γ → C w ≡ τ → Γ ⊢ ↓ τ < w >
    `λ_⦂_⇒_ : ∀ {w} → (x : Id) (σ : Type) → (c : (x ⦂ σ < w > ∷ Γ) ⊢ ⋆< w >) → Γ ⊢ ↓ (` σ cont) < w >
    -- Pair and sum values
    `_,_ : ∀ {τ σ w} → Γ ⊢ ↓ τ < w > →  Γ ⊢ ↓ σ < w > →  Γ ⊢ ↓ (` τ × σ) < w >
    -- `fst : ∀ {τ σ w} → Γ ⊢ ↓ (` τ × σ) < w > → Γ ⊢ ↓ τ < w >
    -- `snd : ∀ {τ σ w} → Γ ⊢ ↓ (` τ × σ) < w > → Γ ⊢ ↓ σ < w >
    `inl_`as_ : ∀ {τ w} → Γ ⊢ ↓ τ < w > → (σ : Type) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
    `inr_`as_ : ∀ {σ w} → Γ ⊢ ↓ σ < w > → (τ : Type) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
    --`case_`of_||_ : ∀ {τ σ υ w} → Γ ⊢ (` τ ⊎ σ) < w > → Γ ⊢ (` τ ⇒ υ) < w > → Γ ⊢ (` σ ⇒ υ) < w > → Γ ⊢ υ < w >
    -- At values
    `hold : ∀ {τ w w'} → Γ ⊢ ↓ τ < w' > → Γ ⊢ ↓ (` τ at w') < w >
    -- Shamrock values
    `sham : ∀ {w} {A : World → Type} → ((ω : World) → Γ ⊢ ↓ (A ω) < w >) → Γ ⊢ ↓ `⌘ A < w >
    -- ∀ values
    `Λ : ∀ {w} {A : World → Type} → ((ω : World) → Γ ⊢ ↓ A ω < w >) → Γ ⊢ ↓ `∀ A < w >
    -- ∃ values
    `pack : ∀ {w} {A : World → Type} (ω : World) → Γ ⊢ ↓ A ω < w > → Γ ⊢ ↓ `∃ A < w >
    -- Address values
    `any : ∀ {w w'} → Γ ⊢ ↓ ` w addr < w' >
    -- Continuation expressions
    `leta_`=_`in_ : ∀ {τ w w'} → (x : Id) → Γ ⊢ ↓ (` τ at w') < w > → ((x ⦂ τ < w' >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `lets_`=_`in_ : ∀ {C w} → (u : Id) → Γ ⊢ ↓ (`⌘ C) < w > → ((u ∼ C) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `put_`=_`in_ : ∀ {τ w} {_ : τ mobile} → (u : Id) → Γ ⊢ ↓ τ < w > → ((u ∼ (λ _ → τ)) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=fst_`in_ : ∀ {τ σ w} → (x : Id) → Γ ⊢ ↓ (` τ × σ) < w > → ((x ⦂ τ < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=snd_`in_ : ∀ {τ σ w} → (x : Id) → Γ ⊢ ↓ (` τ × σ) < w > → ((x ⦂ σ < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=localhost`in_ : ∀ {w} → (x : Id) → ((x ⦂ ` w addr < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=_⟨_⟩`in_ : ∀ {C w} → (x : Id) → Γ ⊢ ↓ `∀ C < w > → (w' : World) → ((x ⦂ C w' < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_=`unpack_`=_`in_ : ∀ {w} {A : World → Type} (x : Id) → Γ ⊢ ↓ `∃ A < w > → ((ω : World) → ((x ⦂ A ω < w >) ∷ Γ) ⊢ ⋆< w >) → Γ ⊢ ⋆< w >
    `go[_,_]_ : ∀ {w} → (w' : World) → Γ ⊢ ↓ ` w' addr < w > → Γ ⊢ ⋆< w' > → Γ ⊢ ⋆< w >
    `call : ∀ {τ w} → Γ ⊢ ↓ ` τ cont < w > → Γ ⊢ ↓ τ < w > → Γ ⊢ ⋆< w >
    `halt : ∀ {w} → Γ ⊢ ⋆< w >
    -- Primitive imports
    `prim_`in_ : ∀ {w} → (x : Id) {pf : isJust (primHyp x)} → ((fromJust (primHyp x) pf) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
