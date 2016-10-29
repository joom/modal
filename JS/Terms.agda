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
      `_·_ : ∀ {n typeVec τ w} → Γ ⊢ (`Function {n} typeVec τ) < w >
           → (termVec : Vec (Σ Type (λ σ → Γ ⊢ σ < w >)) n)
           → (Data.Vec.map proj₁ termVec ≡ typeVec) → Γ ⊢ τ < w >
      `λ_⇒_ : ∀ {n typeVec τ w Γ'} → (ids : Vec Id n)
             → FnStm (Data.Vec.toList (zipWith (_⦂_< w >) ids typeVec) +++ Γ) ⇓ Γ' ⦂ (just τ) < w >
             → Γ ⊢ `Function {n} typeVec τ < w >
      -- Object terms
      `obj : ∀ {w} → (terms : List (Id × Σ Type (λ τ → Γ ⊢ τ < w >))) → Γ ⊢ `Object (Data.List.map toTypePair terms) < w >
      `proj : ∀ {keys τ w} → (o : Γ ⊢ `Object keys < w >) → (key : Id) → (key , τ) ∈ keys → Γ ⊢ τ < w >
      -- Valid terms
      `vval : ∀ {w C} → (u : Id) → (u ∼ C) ∈ Γ → Γ ⊢ C w < w >

    -- Since we will not use any global variables, this should be enough.
    data Stm_<_> : Context → World → Set where
      `exp : ∀ {Γ τ w} → Γ ⊢ τ < w > → Stm Γ < w >

    data FnStm_⇓_⦂_<_> : Context → Context → Maybe Type → World → Set where
      `nop : ∀ {Γ w mσ} → FnStm Γ ⇓ Γ ⦂ mσ < w >
      `exp : ∀ {Γ τ w mσ} → Γ ⊢ τ < w > → FnStm Γ ⇓ Γ ⦂ mσ < w >
      `var : ∀ {Γ τ w mσ} → (id : Id) → (t : Γ ⊢ τ < w >) → FnStm Γ ⇓ (id ⦂ τ < w > ∷ Γ) ⦂ mσ < w >
      `assign : ∀ {Γ τ w mσ} → (id : Id) → (t : Γ ⊢ τ < w >) → (id ⦂ τ < w >) ∈ Γ → FnStm Γ ⇓ Γ ⦂ mσ < w >
      _；return_ : ∀ {Γ Γ' τ w} → FnStm Γ ⇓ Γ' ⦂ nothing < w > → Γ' ⊢ τ < w > → FnStm Γ ⇓ Γ' ⦂ (just τ) < w >
      _；_ : ∀ {Γ Γ' Γ'' w mσ} → FnStm Γ ⇓ Γ' ⦂ mσ < w > → FnStm Γ' ⇓ Γ'' ⦂ mσ < w > → FnStm Γ ⇓ Γ'' ⦂ mσ < w >
      `if_`then_`else_ : ∀ {Γ Γ' w mσ} → Γ ⊢ `Bool < w > → FnStm Γ ⇓ Γ' ⦂ mσ < w > → FnStm Γ ⇓ Γ' ⦂ mσ < w > → FnStm Γ ⇓ Γ' ⦂ mσ < w >
      `prim : ∀ {Γ h mσ w} → (x : Prim h) → FnStm Γ ⇓ (h ∷ Γ) ⦂ mσ < w >

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
    ⊆-exp-lemma s ((` t · termVec) x) = (` ⊆-exp-lemma s t · Data.Vec.map (λ { (υ , u) → (υ , ⊆-exp-lemma s u) }) termVec) {!x!}
    ⊆-exp-lemma s (`λ ids ⇒ x) = `λ ids ⇒ {!!}
    ⊆-exp-lemma s (`obj terms) = {!`obj ?!}
    ⊆-exp-lemma s (`proj t key x) = `proj (⊆-exp-lemma s t) key x
    ⊆-exp-lemma s (`vval u ∈) = `vval u (s ∈)

    ⊆-stm-lemma : ∀ {Γ Γ' w} → Γ ⊆ Γ' → Stm Γ < w > → Stm Γ' < w >
    ⊆-stm-lemma s (`exp x) = `exp (⊆-exp-lemma s x)

    ⊆-fnstm-lemma : ∀ {Γ Γ' mσ w} → Γ ⊆ Γ' → Σ _ (λ Δ → FnStm Γ ⇓ Δ ⦂ mσ < w >) → Σ _ (λ Δ' → FnStm Γ' ⇓ Δ' ⦂ mσ < w >)
    ⊆-fnstm-lemma s (Γ , `nop) = _ , `nop
    ⊆-fnstm-lemma s (Γ , `exp x) = _ , `exp (⊆-exp-lemma s x)
    ⊆-fnstm-lemma s (_ , `var id t) = _ , `var id (⊆-exp-lemma s t)
    ⊆-fnstm-lemma s (Γ , `assign id t x) = _ , `assign id (⊆-exp-lemma s t) (s x)
    ⊆-fnstm-lemma s (Γ' , (t ；return x)) with ⊆-fnstm-lemma s (_ , t)
    ... | Γ'' , t' = Γ'' , (t' ；return ⊆-exp-lemma {!!} x)
    -- ⊆-fnstm-lemma {Γ}{Δ} s (Γ'' , (_；_ {Γ' = Γ'} t u)) with ⊆-fnstm-lemma s (Γ' , t)
    -- ... | (Δ' , t' , s') with ⊆-fnstm-lemma s' (Γ'' , u)
    -- ... | (Δ'' , u' , s'') = Δ'' , (t' ； u') , s''
    ⊆-fnstm-lemma s (Γ'' , (_；_ {Γ}{Γ'} t u)) with ⊆-fnstm-lemma {!!} (Γ' , t)
    ... | xs , t' with ⊆-fnstm-lemma {!!} (Γ'' , u)
    ... | ys , u' = {!!}
    -- with ⊆-fnstm-lemma s (_ , t) | ⊆-fnstm-lemma {!s!} (_ , u)
    -- ... | xs , t' | ys , u' = {!!}
    ⊆-fnstm-lemma s (Γ' , (`if x `then t `else u)) with ⊆-fnstm-lemma s (_ , t) | ⊆-fnstm-lemma s (_ , u)
    ... | xs , t' | ys , u' = {!!} , (`if ⊆-exp-lemma s x `then {!!} `else {!!})
    ⊆-fnstm-lemma s (_ , `prim x) = _ , `prim x

    ⊆-fnstm-lemma' : ∀ {Γ Γ' mσ w} → Γ ⊆ Γ'
                   → (t : Σ _ (λ Δ → FnStm Γ ⇓ Δ ⦂ mσ < w >))
                   → Σ _ (λ Δ' → FnStm Γ' ⇓ Δ' ⦂ mσ < w > × (proj₁ t) ⊆ Δ')
    ⊆-fnstm-lemma' s (Γ , `nop) = _ , `nop , s
    ⊆-fnstm-lemma' s (Γ , `exp x) = _ , `exp (⊆-exp-lemma s x) , s
    ⊆-fnstm-lemma' s (_ , `var id t) = _ , `var id (⊆-exp-lemma s t) , sub-lemma s
    ⊆-fnstm-lemma' s (Γ , `assign id t x) = _ , `assign id (⊆-exp-lemma s t) (s x) , s
    ⊆-fnstm-lemma' s (Γ' , (t ；return x)) with ⊆-fnstm-lemma' s (Γ' , t)
    ... | (Δ' , t' , s') = Δ' , (t' ；return ⊆-exp-lemma s' x) , s'
    ⊆-fnstm-lemma' {Γ}{Δ} s (Γ'' , (_；_ {Γ' = Γ'} t u)) with ⊆-fnstm-lemma' s (Γ' , t)
    ... | (Δ' , t' , s') with ⊆-fnstm-lemma' s' (Γ'' , u)
    ... | (Δ'' , u' , s'') = Δ'' , (t' ； u') , s''
    ⊆-fnstm-lemma' s (Δ , (`if x `then t `else u)) with ⊆-fnstm-lemma' s (Δ , t)
    ... | (Δ' , t' , s') with ⊆-fnstm-lemma' s (Δ , u)
    ... | (Δ'' , u' , s'') with reconcile Δ Δ' Δ'' s' s''
    ... | (Δ''' , s''' , s'''') = {!!}
    -- ⊆-fnstm-lemma' s (Γ' , (`if x `then t `else u)) with ⊆-fnstm-lemma' s (Γ' , t)
    -- ... | (Δ' , t' , s') with ⊆-fnstm-lemma' {!!} (Γ' , u)
    -- ... | (Δ'' , u' , s'') = Δ'' , (`if ⊆-exp-lemma {!!} x `then {!t'!} `else u') , s''
    ⊆-fnstm-lemma' s (_ , `prim x) = _ , `prim x , sub-lemma s
