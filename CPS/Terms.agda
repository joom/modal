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
  open import Data.Integer
  open import Data.List hiding ([_])
  open import Data.List.Any
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import CPS.Types
  open import Definitions

  -- Valid values and values of the primitives of our language.
  data Prim : Hyp → Set where
    `alert : Prim ("alert" ⦂ ` ` `String × ` `Unit cont cont < client >)
    `version : Prim ("version" ⦂ `String < server > )
    `log : Prim ("log" ∼ (λ ω → ` ` `String × ` `Unit cont cont))
    `prompt : Prim ("prompt" ⦂ ` ` `String × ` `String cont cont < client >)
    `readFile : Prim ("readFile" ⦂ ` ` `String × ` `String cont cont < server >)

  -- Terms that have to type check by definition.
  infixl 5 _⊢_
  data _⊢_ (Γ : Context) : Conc → Set where
    `tt : ∀ {w} → Γ ⊢ ↓ `Unit < w >
    `string : ∀ {w} → Data.String.String → Γ ⊢ ↓ `String < w >
    -- Boolean values
    `true  : ∀ {w} → Γ ⊢ ↓ `Bool < w >
    `false : ∀ {w} → Γ ⊢ ↓ `Bool < w >
    `_∧_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `_∨_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    `¬_  : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ↓ `Bool < w >
    -- ℕ values
    `n_  : ∀ {w} → ℤ → Γ ⊢ ↓ `Int < w >
    `_≤_ : ∀ {w} → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Bool < w >
    `_+_ : ∀ {w} → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w >
    `_*_ : ∀ {w} → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w > → Γ ⊢ ↓ `Int < w >
    -- Abstraction & context values
    `v : ∀ {τ w} → (x : Id) → x ⦂ τ < w > ∈ Γ → Γ ⊢ ↓ τ < w >
    `vval : ∀ {w C} → (u : Id) → u ∼ C ∈ Γ → Γ ⊢ ↓ C w < w >
    `λ_⦂_⇒_ : ∀ {w} → (x : Id) (σ : Type) → (c : (x ⦂ σ < w > ∷ Γ) ⊢ ⋆< w >) → Γ ⊢ ↓ (` σ cont) < w >
    -- Pair and sum values
    `_,_ : ∀ {τ σ w} → Γ ⊢ ↓ τ < w > →  Γ ⊢ ↓ σ < w > →  Γ ⊢ ↓ (` τ × σ) < w >
    `inl_`as_ : ∀ {τ w} → Γ ⊢ ↓ τ < w > → (σ : Type) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
    `inr_`as_ : ∀ {σ w} → Γ ⊢ ↓ σ < w > → (τ : Type) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
    -- At values
    `hold : ∀ {τ w w'} → Γ ⊢ ↓ τ < w' > → Γ ⊢ ↓ (` τ at w') < w >
    -- Shamrock values
    `sham : ∀ {w} {A : World → Type} → ((ω : World) → Γ ⊢ ↓ (A ω) < ω >) → Γ ⊢ ↓ `⌘ A < w >
    -- ∀ values
    `Λ : ∀ {w} {A : World → Type} → ((ω : World) → Γ ⊢ ↓ A ω < w >) → Γ ⊢ ↓ `∀ A < w >
    -- ∃ values
    `pack : ∀ {w} {A : World → Type} (ω : World) → Γ ⊢ ↓ A ω < w > → Γ ⊢ ↓ `∃ A < w >
    -- Continuation expressions
    `if_`then_`else_ : ∀ {w} → Γ ⊢ ↓ `Bool < w > → Γ ⊢ ⋆< w > → Γ ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `letcase_,_`=_`in_`or_ : ∀ {τ σ w} → (x y : Id) → Γ ⊢ ↓ (` τ ⊎ σ) < w >
                           → ((x ⦂ τ < w >) ∷ Γ) ⊢ ⋆< w > → ((y ⦂ σ < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `leta_`=_`in_ : ∀ {τ w w'} → (x : Id) → Γ ⊢ ↓ (` τ at w') < w > → ((x ⦂ τ < w' >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `lets_`=_`in_ : ∀ {C w} → (u : Id) → Γ ⊢ ↓ (`⌘ C) < w > → ((u ∼ C) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `put_`=_`in_ : ∀ {C w} {m : (C w) mobile} → (u : Id) → Γ ⊢ ↓ C w < w > → ((u ∼ C) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=fst_`in_ : ∀ {τ σ w} → (x : Id) → Γ ⊢ ↓ (` τ × σ) < w > → ((x ⦂ τ < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=snd_`in_ : ∀ {τ σ w} → (x : Id) → Γ ⊢ ↓ (` τ × σ) < w > → ((x ⦂ σ < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_`=_⟨_⟩`in_ : ∀ {C w} → (x : Id) → Γ ⊢ ↓ `∀ C < w > → (w' : World) → ((x ⦂ C w' < w >) ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >
    `let_=`unpack_`in_ : ∀ {w} {A : World → Type} (x : Id) → Γ ⊢ ↓ `∃ A < w > → ((ω : World) → ((x ⦂ A ω < w >) ∷ Γ) ⊢ ⋆< w >) → Γ ⊢ ⋆< w >
    `go[_]_ : ∀ {w} → (w' : World) → Γ ⊢ ⋆< w' > → Γ ⊢ ⋆< w >
    `call : ∀ {τ w} → Γ ⊢ ↓ ` τ cont < w > → Γ ⊢ ↓ τ < w > → Γ ⊢ ⋆< w >
    `halt : ∀ {w} → Γ ⊢ ⋆< w >
    -- Primitive imports
    `prim_`in_ : ∀ {h w} → (x : Prim h) → (h ∷ Γ) ⊢ ⋆< w > → Γ ⊢ ⋆< w >

  sub-lemma : ∀ {Γ Δ} {h : Hyp} → Γ ⊆ Δ → (h ∷ Γ) ⊆ (h ∷ Δ)
  sub-lemma {h = h} s {x} i with x decHyp h
  ... | yes p = here p
  sub-lemma s (here px) | no q = ⊥-elim (q px)
  sub-lemma s (there i) | no q = there (s i)

  -- Weakening
  mutual
    ⊆-cont-lemma : ∀ {Γ Γ' w} → Γ ⊆ Γ' → Γ ⊢ ⋆< w > → Γ' ⊢ ⋆< w >
    ⊆-cont-lemma s (`if t `then u `else v) = `if ⊆-term-lemma s t `then ⊆-cont-lemma s u `else ⊆-cont-lemma s v
    ⊆-cont-lemma s (`letcase x , y `= t `in u `or v) =
      `letcase x , y `= ⊆-term-lemma s t `in ⊆-cont-lemma (sub-lemma s) u `or ⊆-cont-lemma (sub-lemma s) v
    ⊆-cont-lemma s (`leta x `= t `in u) = `leta x `= (⊆-term-lemma s t) `in (⊆-cont-lemma (sub-lemma s) u)
    ⊆-cont-lemma s (`lets u `= t `in v) = `lets u `= (⊆-term-lemma s t) `in (⊆-cont-lemma (sub-lemma s) v)
    ⊆-cont-lemma s (`put_`=_`in_ {m = m} u t v) = `put_`=_`in_ {m = m} u (⊆-term-lemma s t) (⊆-cont-lemma (sub-lemma s) v)
    ⊆-cont-lemma s (`let x `=fst t `in u) = `let x `=fst (⊆-term-lemma s t) `in (⊆-cont-lemma (sub-lemma s) u)
    ⊆-cont-lemma s (`let x `=snd t `in u) = `let x `=snd (⊆-term-lemma s t) `in (⊆-cont-lemma (sub-lemma s) u)
    ⊆-cont-lemma s (`let x `= t ⟨ w' ⟩`in u) = `let x `= (⊆-term-lemma s t) ⟨ w' ⟩`in ⊆-cont-lemma (sub-lemma s) u
    ⊆-cont-lemma s (`let_=`unpack_`in_ x t u) =
      `let_=`unpack_`in_ x (⊆-term-lemma s t) (λ ω → ⊆-cont-lemma (sub-lemma s) (u ω))
    ⊆-cont-lemma s (`go[ w' ] u) = `go[ w' ] (⊆-cont-lemma s u)
    ⊆-cont-lemma s (`call t u) = `call (⊆-term-lemma s t) (⊆-term-lemma s u)
    ⊆-cont-lemma s `halt = `halt
    ⊆-cont-lemma s (`prim x `in t) = `prim x `in ⊆-cont-lemma (sub-lemma s) t

    ⊆-term-lemma : ∀ {Γ Γ' τ w} → Γ ⊆ Γ' → Γ ⊢ ↓ τ < w > → Γ' ⊢ ↓ τ < w >
    ⊆-term-lemma s `tt = `tt
    ⊆-term-lemma s (`string x) = `string x
    ⊆-term-lemma s `true = `true
    ⊆-term-lemma s `false = `false
    ⊆-term-lemma s (` t ∧ u) = ` ⊆-term-lemma s t ∧ ⊆-term-lemma s u
    ⊆-term-lemma s (` t ∨ u) = ` ⊆-term-lemma s t ∨ ⊆-term-lemma s u
    ⊆-term-lemma s (`¬ t) = `¬ ⊆-term-lemma s t
    ⊆-term-lemma s (`n x) = `n x
    ⊆-term-lemma s (` t ≤ u) = ` ⊆-term-lemma s t ≤ ⊆-term-lemma s u
    ⊆-term-lemma s (` t + u) = ` ⊆-term-lemma s t + ⊆-term-lemma s u
    ⊆-term-lemma s (` t * u) = ` ⊆-term-lemma s t * ⊆-term-lemma s u
    ⊆-term-lemma s (`v x ∈) = `v x (s ∈)
    ⊆-term-lemma s (`vval u ∈) = `vval u (s ∈)
    ⊆-term-lemma s (`λ x ⦂ σ ⇒ t) = `λ x ⦂ σ ⇒ ⊆-cont-lemma (sub-lemma s) t
    ⊆-term-lemma s (` t , u) = ` ⊆-term-lemma s t , ⊆-term-lemma s u
    ⊆-term-lemma s (`inl t `as σ) = `inl (⊆-term-lemma s t) `as σ
    ⊆-term-lemma s (`inr t `as τ) = `inr (⊆-term-lemma s t) `as τ
    ⊆-term-lemma s (`hold t) = `hold (⊆-term-lemma s t)
    ⊆-term-lemma s (`sham x) = `sham (λ ω → ⊆-term-lemma s (x ω))
    ⊆-term-lemma s (`Λ x) = `Λ (λ ω → ⊆-term-lemma s (x ω))
    ⊆-term-lemma s (`pack ω t) = `pack ω (⊆-term-lemma s t)
