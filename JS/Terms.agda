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
  open import Data.String
  open import Data.Nat.Show
  open import Data.List hiding ([_] ; zipWith) renaming (_++_ to _+++_)
  open import Data.List.Any
  open import Data.List.Properties
  open Membership-≡
  open import Data.Vec hiding (_∈_)
  open import Data.Fin
  open import Data.Empty
  open import Function

  open import JS.Types

  open import Definitions

  data Prim : Hyp → Set where
    `alert : Prim (("alert" ⦂ `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `Object (("type" , `String) ∷ []) ] `Undefined) ∷ []) ] `Undefined < client >))
    `version : Prim ("version" ⦂ `String < server >)
    `log : Prim ("log" ∼ (λ ω → `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `Object (("type" , `String) ∷ []) ] `Undefined) ∷ []) ] `Undefined))
    `prompt : Prim ("prompt" ⦂ `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `String ] `Undefined) ∷ []) ] `Undefined < client >)
    `readFile : Prim ("readFile" ⦂ `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `String ] `Undefined) ∷ []) ] `Undefined < server >)

  infixl 5 _⊢_
  mutual
    data _⊢_ (Γ : Context) : Conc → Set where
      `string : ∀ {w} → String → Γ ⊢ `String < w >
      `undefined : ∀ {w} → Γ ⊢ `Undefined < w >
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
      -- `λ_⇒_ : ∀ {n typeVec τ w} → (ids : Vec Id n) → (toList (zipWith (_⦂_< w >) ids typeVec) ∷ Γ) ⊢ τ < w > → Γ ⊢ `Function {n} typeVec τ < w >
      `λ_⇒_ : ∀ {n typeVec τ w fr} → (ids : Vec Id n)
             → FnStm (Data.Vec.toList (zipWith (_⦂_< w >) ids typeVec) ∷ Γ) ⇓ fr ∷ Γ ⦂ (just τ) < w >
             → Γ ⊢ `Function {n} typeVec τ < w >
      -- Object terms
      `obj : ∀ {w} → (terms : List (Id × Σ Type (λ τ → Γ ⊢ τ < w >))) → Γ ⊢ `Object (Data.List.map toTypePair terms) < w >
      --  `obj : ∀ {w} → (terms : List (Id × Σ Type (λ σ → Γ ⊢ σ < w >))) → Γ ⊢ `Object (Data.List.map (λ { (id , τ , ω) → (id , τ)}) terms) < w >
      `proj : ∀ {keys τ w} → (o : Γ ⊢ `Object keys < w >) → (key : Id) → (key , τ) ∈ keys → Γ ⊢ τ < w >
      -- Valid terms
      `vval : ∀ {w C} → (u : Id) → (u ∼ C) ∈ⱼ Γ → Γ ⊢ C w < w >

    -- Since we will not use any global variables, this should be enough.
    data Stm_<_> : Context → World → Set where
      `exp : ∀ {Γ τ w} → Γ ⊢ τ < w > → Stm Γ < w >

    data FnStm_⇓_⦂_<_> : Context → Context → Maybe Type → World → Set where
      `exp : ∀ {Γ τ w mσ} → Γ ⊢ τ < w > → FnStm Γ ⇓ Γ ⦂ mσ < w >
      `var : ∀ {fr Γ τ w mσ} → (id : Id) → (t : (fr ∷ Γ) ⊢ τ < w >) → id ⦂ τ < w > ∉ fr → FnStm (fr ∷ Γ) ⇓ ((id ⦂ τ < w > ∷ fr) ∷ Γ) ⦂ mσ < w >
      `assign : ∀ {Γ τ w mσ} → (id : Id) → (t : Γ ⊢ τ < w >) → (id ⦂ τ < w >) ∈ⱼ Γ → FnStm Γ ⇓ Γ ⦂ mσ < w >
      _；return_ : ∀ {Γ Γ' τ w} → FnStm Γ ⇓ Γ' ⦂ nothing < w > → Γ' ⊢ τ < w > → FnStm Γ ⇓ Γ' ⦂ (just τ) < w >
      _；_ : ∀ {Γ Γ' Γ'' w} → FnStm Γ ⇓ Γ' ⦂ nothing < w > → FnStm Γ' ⇓ Γ'' ⦂ nothing < w > → FnStm Γ ⇓ Γ'' ⦂ nothing < w >
      `prim : ∀ {fr Γ h mσ w} → (x : Prim h) → FnStm (fr ∷ Γ) ⇓ ((h ∷ fr) ∷ Γ) ⦂ mσ < w >

    toTypePair : ∀ {Γ w} → Id × Σ Type (λ τ → Γ ⊢ τ < w >) → Id × Type
    toTypePair = λ { (id , τ , ω) → (id , τ)}

  {-# NON_TERMINATING #-}
  default : ∀ {Γ w} (τ : Type) → Γ ⊢ τ < w >
  default `Undefined = `undefined
  default `Bool = `false
  default `Number = `n (inj₁ (+ 0))
  default `String = `string ""
  default (`Function {n} τs σ) = `λ Data.Vec.tabulate (underscorePrefix ∘ Data.Nat.Show.show ∘ toℕ) ⇒ ((`exp `undefined) ；return (default σ))
  default {Γ}{w} (`Object fields) = eq-replace tEq (`obj (Data.List.map f fields))
    where
      f : Id × Type → Id × Σ Type (λ τ → Γ ⊢ τ < w >)
      f = λ { (id , τ) → (id , τ , default {Γ}{w} τ)}
      pf : (Data.List.map toTypePair ∘ Data.List.map f) fields ≡ fields
      pf = trans (sym (Data.List.Properties.map-compose fields)) (Data.List.Properties.map-id fields)
      tEq : Γ ⊢ (`Object ((Data.List.map toTypePair ∘ Data.List.map f) fields) < w >) ≡ Γ ⊢ (`Object fields < w >)
      tEq = cong (λ x → Γ ⊢ `Object x < w >) pf
