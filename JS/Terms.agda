module JS.Terms where

  open import Data.Bool
  open import Data.Float
  open import Data.Integer
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe hiding (All)
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Data.String
  open import Data.Nat.Show
  open import Data.List renaming (_++_ to _+++_)
  open import Data.List.All
  open import Data.List.Any
  open import Data.List.Properties
  open Membership-≡
  open import Data.List.Any.Properties using (++ʳ ; ++ˡ)
  open import Data.Fin
  open import Data.Empty
  open import Function

  open import JS.Types

  open import Definitions

  data Prim : Hyp → Set where
    `alert : Prim ("alert" ⦂ `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `Object (("type" , `String) ∷ []) ] `Undefined) ∷ []) ] `Undefined < client >)
    `version : Prim ("version" ⦂ `String < server >)
    `log : Prim ("log" ∼ (λ ω → `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `Object (("type" , `String) ∷ []) ] `Undefined) ∷ []) ] `Undefined))
    `prompt : Prim ("prompt" ⦂ `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `String ] `Undefined) ∷ []) ] `Undefined < client >)
    `readFile : Prim ("readFile" ⦂ `Function [ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Function [ `String ] `Undefined) ∷ []) ] `Undefined < server >)
    -- PRIMITIVES FOR WEB SOCKETS (not accessible in ML5 or CPS, only for compilation)
    `socket : Prim ("socket" ⦂ `Object (("on" , `Function (`String ∷ `Function (`String ∷ []) `Undefined ∷ []) `Undefined)
                                       ∷ ("emit" , `Function (`String ∷ `String ∷ []) `Undefined) ∷ []) < client >)
    `io : Prim ("io" ⦂ `Object (("on" , `Function (`String ∷ `Object (("on" , `Function (`String ∷ `Function (`String ∷ []) `Undefined ∷ []) `Undefined) ∷ []) ∷ []) `Undefined)
                               ∷ ("emit" , `Function (`String ∷ `String ∷ []) `Undefined) ∷ []) < server >)

  infixl 5 _⊢_
  infixl 4 _；_
  infixl 4 _；return_
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
      `v : ∀ {τ w} → (x : Id) → (x ⦂ τ < w >) ∈ Γ → Γ ⊢ τ < w >
      `_·_ : ∀ {argTypes τ w} → Γ ⊢ (`Function argTypes τ) < w >
           → All (λ σ → Γ ⊢ σ < w >) argTypes
           → Γ ⊢ τ < w >
      `λ_⇒_ : ∀ {argTypes τ w Γ'} → (ids : List Id)
             → FnStm ((zipWith (_⦂_< w >) ids argTypes) +++ Γ) ⇓ Γ' ⦂ (just τ) < w >
             → Γ ⊢ `Function argTypes τ < w >
      -- Object terms
      `obj : ∀ {w} → (terms : List (Id × Σ Type (λ τ → Γ ⊢ τ < w >))) → Γ ⊢ `Object (Data.List.map toTypePair terms) < w >
      `proj : ∀ {keys τ w} → (o : Γ ⊢ `Object keys < w >) → (key : Id) → (key , τ) ∈ keys → Γ ⊢ τ < w >
      -- Valid terms
      `vval : ∀ {w C} → (u : Id) → (u ∼ C) ∈ Γ → Γ ⊢ C w < w >

    -- Since we will not use any global variables, this should be enough.
    data Stm_<_> : Context → World → Set where
      `exp : ∀ {Γ τ w} → Γ ⊢ τ < w > → Stm Γ < w >

    -- Respectively takes: the initial context, the context added, the return type, the world
    data FnStm_⇓_⦂_<_> : Context → Context → Maybe Type → World → Set where
      `nop : ∀ {Γ w mσ} → FnStm Γ ⇓ [] ⦂ mσ < w >
      `exp : ∀ {Γ τ w mσ} → Γ ⊢ τ < w > → FnStm Γ ⇓ [] ⦂ mσ < w >
      `var : ∀ {Γ τ w mσ} → (id : Id) → (t : Γ ⊢ τ < w >) → FnStm Γ ⇓ (id ⦂ τ < w > ∷ []) ⦂ mσ < w >
      `assign : ∀ {Γ τ w mσ} → (id : Id) → (t : Γ ⊢ τ < w >) → (id ⦂ τ < w >) ∈ Γ → FnStm Γ ⇓ [] ⦂ mσ < w >
      _；return_ : ∀ {Γ γ τ w} → FnStm Γ ⇓ γ ⦂ nothing < w > → (γ +++ Γ) ⊢ τ < w > → FnStm Γ ⇓ γ ⦂ (just τ) < w >
      _；_ : ∀ {Γ γ γ' w mσ} → FnStm Γ ⇓ γ ⦂ mσ < w > → FnStm (γ +++ Γ) ⇓ γ' ⦂ mσ < w > → FnStm Γ ⇓ (γ' +++ γ) ⦂ mσ < w >
      `if_`then_`else_ : ∀ {Γ γ w mσ} → Γ ⊢ `Bool < w > → FnStm Γ ⇓ γ ⦂ mσ < w > → FnStm Γ ⇓ γ ⦂ mσ < w > → FnStm Γ ⇓ γ ⦂ mσ < w >
      `prim : ∀ {Γ h mσ w} → (x : Prim h) → FnStm Γ ⇓ (h ∷ []) ⦂ mσ < w >

    toTypePair : ∀ {Γ w} → Id × Σ Type (λ τ → Γ ⊢ τ < w >) → Id × Type
    toTypePair (id , τ , ω) = (id , τ)

  {-# NON_TERMINATING #-}
  default : ∀ {Γ w} (τ : Type) → Γ ⊢ τ < w >
  default `Undefined = `undefined
  default `Bool = `false
  default `Number = `n (inj₁ (+ 0))
  default `String = `string ""
  default (`Function τs σ) = `λ Data.List.map (underscorePrefix ∘ Data.Nat.Show.show) (downFrom (length τs))  ⇒ ((`exp `undefined ；return default σ))
  default {Γ}{w} (`Object fields) = eq-replace tEq (`obj (Data.List.map f fields))
    where
      f : Id × Type → Id × Σ Type (λ τ → Γ ⊢ τ < w >)
      f (id , τ) = (id , τ , default {Γ}{w} τ)
      pf : (Data.List.map toTypePair ∘ Data.List.map f) fields ≡ fields
      pf = trans (sym (map-compose fields)) (map-id fields)
      tEq : Γ ⊢ (`Object ((Data.List.map toTypePair ∘ Data.List.map f) fields) < w >) ≡ Γ ⊢ (`Object fields < w >)
      tEq = cong (λ x → Γ ⊢ `Object x < w >) pf

  {-# NON_TERMINATING #-}
  mutual
  -- Weakening lemma
    ⊆-exp-lemma : ∀ {Γ Γ' τ w} → Γ ⊆ Γ' → Γ ⊢ τ < w > → Γ' ⊢ τ < w >
    ⊆-exp-lemma s (`string x) = `string x
    ⊆-exp-lemma s `undefined = `undefined
    ⊆-exp-lemma s `true = `true
    ⊆-exp-lemma s `false = `false
    ⊆-exp-lemma s (` t ∧ u) = ` ⊆-exp-lemma s t ∧ ⊆-exp-lemma s u
    ⊆-exp-lemma s (` t ∨ u) = ` ⊆-exp-lemma s t ∨ ⊆-exp-lemma s u
    ⊆-exp-lemma s (`¬ t) = `¬ ⊆-exp-lemma s t
    ⊆-exp-lemma s (`n x) = `n x
    ⊆-exp-lemma s (` t ≤ u) = ` ⊆-exp-lemma s t ≤ ⊆-exp-lemma s u
    ⊆-exp-lemma s (` t + u) = ` ⊆-exp-lemma s t + ⊆-exp-lemma s u
    ⊆-exp-lemma s (` t * u) = ` ⊆-exp-lemma s t * ⊆-exp-lemma s u
    ⊆-exp-lemma s (`v x ∈) = `v x (s ∈)
    ⊆-exp-lemma s ((`_·_) {argTypes} t terms) = ` ⊆-exp-lemma s t · Data.List.All.map (⊆-exp-lemma s) terms
    ⊆-exp-lemma s (`λ ids ⇒ body) =
      `λ ids ⇒ ⊆-fnstm-lemma (sub-lemma-list {γ = zipWith (λ x τ → x ⦂ τ < _ >) ids _} s) body
    ⊆-exp-lemma {Γ}{Γ'}{_}{w} s (`obj terms) = eq-replace (sym termEq) (`obj terms')
      where
        singleWeaken : Id × Σ Type (λ τ → Γ ⊢ τ < w >) → Id × Σ Type (λ τ → Γ' ⊢ τ < w >)
        singleWeaken (id , τ , t) = (id , τ , ⊆-exp-lemma s t)

        terms' : List (Id × Σ Type (λ τ → Γ' ⊢ τ < w >))
        terms' = Data.List.map singleWeaken terms

        goalPf : Data.List.map toTypePair terms ≡ Data.List.map toTypePair terms'
        goalPf = map-compose {g = toTypePair} {f = singleWeaken} terms

        termEq : Γ' ⊢ `Object (Data.List.map toTypePair terms) < w > ≡ Γ' ⊢ `Object (Data.List.map toTypePair terms') < w >
        termEq = cong (λ x → Γ' ⊢ `Object x < w >) goalPf
    ⊆-exp-lemma s (`proj t key x) = `proj (⊆-exp-lemma s t) key x
    ⊆-exp-lemma s (`vval u ∈) = `vval u (s ∈)

    ⊆-stm-lemma : ∀ {Γ Γ' w} → Γ ⊆ Γ' → Stm Γ < w > → Stm Γ' < w >
    ⊆-stm-lemma s (`exp x) = `exp (⊆-exp-lemma s x)

    ⊆-fnstm-lemma : ∀ {Γ Γ' γ mσ w} → Γ ⊆ Γ' → FnStm Γ ⇓ γ ⦂ mσ < w > → FnStm Γ' ⇓ γ ⦂ mσ < w >
    ⊆-fnstm-lemma s `nop = `nop
    ⊆-fnstm-lemma s (`exp x) = `exp (⊆-exp-lemma s x)
    ⊆-fnstm-lemma s (`var id t) = `var id (⊆-exp-lemma s t)
    ⊆-fnstm-lemma s (`assign id t ∈) = `assign id (⊆-exp-lemma s t) (s ∈)
    ⊆-fnstm-lemma s (_；return_ {γ = γ} t x) =
      ⊆-fnstm-lemma s t ；return ⊆-exp-lemma (sub-lemma-list {γ = γ} s) x
    ⊆-fnstm-lemma s (_；_ {γ = γ} t u) = ⊆-fnstm-lemma s t ； ⊆-fnstm-lemma (sub-lemma-list {γ = γ} s) u
    ⊆-fnstm-lemma s (`if x `then t `else u) = `if ⊆-exp-lemma s x `then ⊆-fnstm-lemma s t `else ⊆-fnstm-lemma s u
    ⊆-fnstm-lemma s (`prim x) = `prim x
