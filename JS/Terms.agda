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
    `alert : Prim ( "alert" ⦂ `Σt[t×[ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Σt[t×[ `Object (("type" , `String) ∷ []) ×t]cont]) ∷ []) ×t]cont] < client > )
    `version : Prim ( "version" ⦂ `String < server > )
    `logCli : Prim ("log" ⦂ `Σt[t×[ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Σt[t×[ `Object (("type" , `String) ∷ []) ×t]cont]) ∷ []) ×t]cont] < client >)
    `logSer : Prim ("log" ⦂ `Σt[t×[ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Σt[t×[ `Object (("type" , `String) ∷ []) ×t]cont]) ∷ []) ×t]cont] < server >)
    `prompt : Prim ( "prompt" ⦂ `Σt[t×[ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Σt[t×[ `String ×t]cont]) ∷ []) ×t]cont] < client > )
    `readFile : Prim ( "readFile" ⦂ `Σt[t×[ `Object (("type" , `String) ∷ ("fst" , `String) ∷ ("snd" , `Σt[t×[ `String ×t]cont]) ∷ []) ×t]cont] < server > )
    -- PRIMITIVES FOR WEB SOCKETS
    -- (not accessible in other intermediate languages, only for compilation to JS)
    `socket : Prim ( "socket" ⦂ `Object (("on" , `Function (`String ∷ `Function (`String ∷ []) `Undefined ∷ []) `Undefined)
                                       ∷ ("emit" , `Function (`String ∷ `String ∷ []) `Undefined) ∷ []) < client > )
    `io : Prim ( "io" ⦂ `Object (("on" , `Function (`String ∷ `Object (("on" , `Function (`String ∷ `Function (`String ∷ []) `Undefined ∷ []) `Undefined) ∷ []) ∷ []) `Undefined)
                               ∷ ("emit" , `Function (`String ∷ `String ∷ []) `Undefined) ∷ []) < server > )


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
      `_===_ : ∀ {τ w} {eq : EqType τ} → Γ ⊢ τ < w > → Γ ⊢ τ < w > → Γ ⊢ `Bool < w >
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
      `obj : ∀ {w} → (terms : List (Id × Σ Type (λ τ → Γ ⊢ τ < w >))) → Γ ⊢ `Object (toTypePairs terms) < w >
      `proj : ∀ {keys τ w} → (o : Γ ⊢ `Object keys < w >) → (key : Id) → (key , τ) ∈ keys → Γ ⊢ τ < w >
      -- Existential pair
      `packΣ : ∀ {σ w} → (τ : Type)
             → Γ ⊢ `Object (("type" , `String) ∷ ("fst" , τ) ∷
                             ("snd" , `Function (`Object (("type" , `String) ∷ ("fst" , σ) ∷ ("snd" , τ) ∷ []) ∷ []) `Undefined) ∷ []) < w >
             → Γ ⊢ `Σt[t×[ σ ×t]cont] < w >
      `proj₁Σ : ∀ {τ σ w} → Γ ⊢ `Σt[t×[ σ ×t]cont] < w > → Γ ⊢ τ < w >
      `proj₂Σ : ∀ {τ σ w} → Γ ⊢ `Σt[t×[ σ ×t]cont] < w > → Γ ⊢ `Function (`Object (("type" , `String) ∷ ("fst" , σ) ∷ ("snd" , τ) ∷ []) ∷ []) `Undefined < w >

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
      `if_`then_`else_ : ∀ {Γ γ γ' w mσ} → Γ ⊢ `Bool < w > → FnStm Γ ⇓ γ ⦂ mσ < w > → FnStm Γ ⇓ γ' ⦂ mσ < w > → FnStm Γ ⇓ γ ∩ γ' ⦂ mσ < w >
      `prim : ∀ {Γ h mσ w} → (x : Prim h) → FnStm Γ ⇓ (h ∷ []) ⦂ mσ < w >

    toTypePairs : ∀ {Γ w} → List (Id × Σ Type (λ τ → Γ ⊢ τ < w >)) → List (Id × Type)
    toTypePairs [] = []
    toTypePairs ((id , τ , ω) ∷ xs) = (id , τ) ∷ toTypePairs xs

  {-# NON_TERMINATING #-}
  default : ∀ {Γ w} (τ : Type) → Γ ⊢ τ < w >
  default `Undefined = `undefined
  default `Bool = `false
  default `Number = `n (inj₁ (+ 0))
  default `String = `string ""
  default (`Function τs σ) = `λ Data.List.map (underscorePrefix ∘ Data.Nat.Show.show) (downFrom (length τs))  ⇒ ((`exp `undefined ；return default σ))
  default {Γ}{w} (`Object fields) = eq-replace (cong (λ l → Γ ⊢ (`Object l) < w >) (pf fields)) (`obj (f fields))
    where
      f : List (Id × Type) → List (Id × Σ Type (λ τ → Γ ⊢ (τ < w >)))
      f [] = []
      f ((id , τ) ∷ xs) = (id , τ , default {Γ}{w} τ) ∷ f xs
      pf : (xs : _) → toTypePairs (f xs) ≡ xs
      pf [] = refl
      pf (x ∷ xs) = cong (λ l → x ∷ l) (pf xs)
  default (`Σt[t×[_×t]cont] τ) =
      `packΣ _ (`obj (("type" , _ , `string "pair") ∷
                      ("fst" , _ , `undefined) ∷
                      ("snd" , _ , (`λ ["o"] ⇒ (`nop ；return `undefined))) ∷ []))

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
    ⊆-exp-lemma s (`_===_ {eq = eq} t u) = `_===_ {eq = eq} (⊆-exp-lemma s t) (⊆-exp-lemma s u)
    ⊆-exp-lemma s (`n x) = `n x
    ⊆-exp-lemma s (` t ≤ u) = ` ⊆-exp-lemma s t ≤ ⊆-exp-lemma s u
    ⊆-exp-lemma s (` t + u) = ` ⊆-exp-lemma s t + ⊆-exp-lemma s u
    ⊆-exp-lemma s (` t * u) = ` ⊆-exp-lemma s t * ⊆-exp-lemma s u
    ⊆-exp-lemma s (`v x ∈) = `v x (s ∈)
    ⊆-exp-lemma s ((`_·_) {argTypes} t terms) = ` ⊆-exp-lemma s t · Data.List.All.map (⊆-exp-lemma s) terms
    ⊆-exp-lemma s (`λ ids ⇒ body) =
      `λ ids ⇒ ⊆-fnstm-lemma (sub-lemma-list {γ = zipWith (λ x τ → x ⦂ τ < _ >) ids _} s) body
    ⊆-exp-lemma {Γ}{Γ'}{_}{w} s (`obj terms) = eq-replace (cong (λ l → Γ' ⊢ (`Object l) < w > ) (pf terms)) (`obj (weaken terms))
      where
        weaken : List (Id × Σ Type (λ τ → Γ ⊢ τ < w >)) → List (Id × Σ Type (λ τ → Γ' ⊢ τ < w >))
        weaken [] = []
        weaken ((id , τ , t) ∷ xs) = (id , τ , ⊆-exp-lemma s t) ∷ weaken xs
        pf : (xs : List _) → toTypePairs (weaken xs) ≡ toTypePairs xs
        pf [] = refl
        pf ((id , τ , t) ∷ xs) = cong (λ l → (id , τ) ∷ l) (pf xs)
    ⊆-exp-lemma s (`proj t key x) = `proj (⊆-exp-lemma s t) key x
    ⊆-exp-lemma s (`packΣ τ u) = `packΣ τ (⊆-exp-lemma s u)
    ⊆-exp-lemma s (`proj₁Σ t) = `proj₁Σ (⊆-exp-lemma s t)
    ⊆-exp-lemma s (`proj₂Σ t) = `proj₂Σ (⊆-exp-lemma s t)

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

    -- ⊆-fnstm-lemma2 : ∀ {Γ γ γ' mσ w} → γ ⊆ γ' → FnStm Γ ⇓ γ ⦂ mσ < w > → FnStm Γ ⇓ γ' ⦂ mσ < w >
    -- ⊆-fnstm-lemma2 s t = {!!}
