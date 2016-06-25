module JS.Terms where

  open import Data.Bool
  open import Data.Float
  open import Data.Integer
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
  open import Data.List hiding ([_] ; zipWith) renaming (_++_ to _+++_)
  open import Data.List.Any
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Vec hiding (_∈_)
  open import Data.Fin
  open import Data.Empty
  open import Function

  open import JS.Types

  open import Definitions

  infixl 5 _⊢_
  mutual
    data _⊢_ (Γ : Context) : Conc → Set where
      -- Boolean values
      `true  : ∀ {w} → Γ ⊢ `Bool < w >
      `false : ∀ {w} → Γ ⊢ `Bool < w >
      `_∧_ : ∀ {w} → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w >
      `_∨_ : ∀ {w} → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w >
      `¬_  : ∀ {w} → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w >
      -- ℕ terms
      `n_  : ∀ {w} → (ℤ ⊎ Float) → Γ ⊢ `Number < w >
      `_≤_ : ∀ {w} → Γ ⊢ `Number < w > → Γ ⊢ `Number < w > → Γ ⊢ `Bool < w >
      `_+_ : ∀ {w} → Γ ⊢ `Number < w > → Γ ⊢ `Number < w > → Γ ⊢ `Number < w >
      `_*_ : ∀ {w} → Γ ⊢ `Number < w > → Γ ⊢ `Number < w > → Γ ⊢ `Number < w >
      -- Abstraction & context terms
      `v : ∀ {τ w} → (x : Id) → (x ⦂ τ < w >) ∈ⱼ Γ → Γ ⊢ τ < w >
      `_·_ : ∀ {n typeVec τ w} → Γ ⊢ (`Function {n} typeVec τ) < w >
           → (termVec : Vec (Σ Type (λ σ → Γ ⊢ σ < w >)) n)
           → (Data.Vec.map proj₁ termVec ≡ typeVec) → Γ ⊢ τ < w >
      `λ_⇒_ : ∀ {n typeVec τ w} → (ids : Vec Id n) → (toList (zipWith (_⦂_< w >) ids typeVec) ∷ Γ) ⊢ τ < w > → Γ ⊢ `Function {n} typeVec τ < w >
      -- Object terms
      `obj : ∀ {n w} → Vec (Id × Σ Type (λ σ → Γ ⊢ σ < w >)) n → Γ ⊢ `Object < w >
      `proj : ∀ {τ w} → (o : Γ ⊢ `Object < w >) → (key : Id) → {!!} → Γ ⊢ τ < w >

    -- Since we will not use any global variables, this should be enough.
    data Stm_<_> : Context → World → Set where
      `exp : ∀ {Γ τ w} → Γ ⊢ τ < w > → Stm Γ < w >

    data FnStm_⇓_⦂_<_> : Context → Context → Maybe Type → World → Set where
      `var : ∀ {fr Γ τ w mσ} → (id : Id) → (t : (fr ∷ Γ) ⊢ τ < w >) → FnStm (fr ∷ Γ) ⇓ ({!!} ∷ Γ) ⦂ mσ < w >
      `assign : ∀ {Γ τ w mσ} → (id : Id) → (t : Γ ⊢ τ < w >) → FnStm Γ ⇓ {!!} ⦂ mσ < w >
      _；return : ∀ {Γ Γ' τ w} → FnStm Γ ⇓ Γ' ⦂ nothing < w > → Γ' ⊢ τ < w > → FnStm Γ ⇓ Γ' ⦂ (just τ) < w >
      _；_ : ∀ {Γ Γ' Γ'' w} → FnStm Γ ⇓ Γ' ⦂ nothing < w > → FnStm Γ' ⇓ Γ'' ⦂ nothing < w > → FnStm Γ ⇓ Γ'' ⦂ nothing < w >
