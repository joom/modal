module CPStoJS where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation using (contraposition)
  open import Data.String using (_++_)
  open import Data.Nat.Show
  open import Data.List hiding ([_]) renaming (_++_ to _+++_)
  open import Data.List.Any
  open import Data.Vec
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ ; Conc to Concₓ ; Context to Contextₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import JS.Types renaming (Type to Typeⱼ ; Hyp to Hypⱼ ; Conc to Concⱼ ; Context to Contextⱼ)
  open import JS.Terms renaming (_⊢_ to _⊢ⱼ_)

  isValue : Concₓ → Set
  isValue ⋆< _ > = ⊥
  isValue ↓ _ < _ > = Data.Unit.⊤

  isCont : Concₓ → Set
  isCont ⋆< _ > = Data.Unit.⊤
  isCont ↓ _ < _ > = ⊥

  convertType : Typeₓ → Typeⱼ
  convertType `Int = `Number
  convertType `Bool = `Bool
  convertType `Unit = `Object (("type" , `String) ∷ [])
  convertType `String = `String
  convertType ` τ cont = `Function [ convertType τ ] `Undefined
  convertType (` τ × σ) = `Object (("type" , `String) ∷ ("fst" , convertType τ ) ∷ ("snd" , convertType σ) ∷ [])
  convertType (` τ ⊎ σ) = `Object (("type" , `String) ∷ ("dir" , `String) ∷ ("inl" , convertType τ) ∷ ("inr" , convertType σ) ∷ [])
  convertType (` τ at w) = convertType τ
  convertType ` x addr = `Object (("type" , `String) ∷ [])
  convertType (`⌘ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
  convertType (`∀ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
  convertType (`∃ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))

  worldForType : Typeₓ → World → World
  worldForType (` τ at w) _ = w
  worldForType _ w = w

  convertHyp : Hypₓ → Hypⱼ
  convertHyp (x ⦂ τ < w >) = x ⦂ convertType τ < worldForType τ w >
  convertHyp (u ∼ x) = u ∼ (λ ω → convertType (x ω))

  convertCtx : Contextₓ → Contextⱼ
  convertCtx = Data.List.map convertHyp

  convertPrim : ∀ {h} → CPS.Terms.Prim h → JS.Terms.Prim (convertHyp h)
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `log = `log
  convertPrim `prompt = `prompt
  convertPrim `readFile = `readFile

  mutual
    convertCont : ∀ {Γ Δ Δ' Φ Φ' mσ}
                → {s : Δ ⊆ Δ'} {s' : Φ ⊆ Φ'}
                → (w : World)
                → Γ ⊢ₓ ⋆< w >
                → FnStm Δ ⇓ Δ' ⦂ mσ < client > × FnStm Φ ⇓ Φ' ⦂ mσ < server >
    convertCont {s = s} {s' = s'} client (`if t `then u `else v)
      with convertCont {s = s} {s' = s'} client u | convertCont {s = {!s!}} {s' = {!!}} client v
    ... | a , b | c , d = (`if {!convertValue t!} `then a `else c) , (b ； d)
    convertCont server (`if t `then u `else v) = {!!}
    convertCont w (`letcase x , y `= t `in t₁ `or t₂) = {!!}
    convertCont w (`leta x `= t `in t₁) = {!!}
    convertCont w (`lets u `= t `in t₁) = {!!}
    convertCont w (`put u `= t `in t₁) = {!!}
    convertCont w (`let x `=fst t `in t₁) = {!!}
    convertCont w (`let x `=snd t `in t₁) = {!!}
    convertCont w (`let x `=localhost`in t) = {!!}
    convertCont w (`let x `= t ⟨ w' ⟩`in t₁) = {!!}
    convertCont w (`let_=`unpack_`=_`in_ x t x₁) = {!!}
    convertCont w (`go[ w' , t ] t₁) = {!!}
    convertCont w (`call t t₁) = {!!}
    convertCont w `halt = {!!}
    convertCont {s = s} {s' = s'} client (`prim x `in t)
      with convertCont {s = {!!}} {s' = s'} client t
    ... | a , b = {!`prim (convertPrim x) ； a!} , b
    convertCont server (`prim x `in t) = {!!}

    -- convertCont {s = s} {s' = s'} (`if t `then u `else v) client
    --   with convertCont {s = s} {s' = s'} u client | convertCont {s = s} {s' = {!s'!}} v client
    -- ... | a , b | c , d = (`if {!convertValue t!} `then a `else c) , (b ； d)
    -- convertCont (`if t `then u `else v) server = {!!}
    -- convertCont {mσ = mσ} `halt client = {!`exp `undefined ；return ?!} , {!`exp `undefined!}
    -- convertCont `halt server = {!`exp `undefined!} , {!`exp `undefined ；return ?!}
    -- convertCont {s = s} {s' = s'} (`prim x `in t) client
    --   with convertCont {s = s} {s' = s'} t client
    -- ... | a , b = {!`prim (convertPrim x) ； a!} , b
    -- convertCont {s = s} {s' = s'} (`prim x `in t) server
    -- with convertCont {s = s} {s' = s'} t server
    -- ... | a , b = a , {!`prim (convertPrim x) ； b!}

    convertValue : ∀ {Γ τ w} → Γ ⊢ₓ ↓ τ < w > → (convertCtx Γ) ⊢ⱼ (convertType τ) < w >
    convertValue `tt = `obj (("type" , `String , `string "unit") ∷ [])
    convertValue (`string s) = `string s
    convertValue `true = `true
    convertValue `false = `false
    convertValue (` t ∧ u) = ` (convertValue t) ∧ (convertValue u)
    convertValue (` t ∨ u) = ` (convertValue t) ∨ (convertValue u)
    convertValue (`¬ t) = `¬ (convertValue t)
    convertValue (`n x) = `n inj₁ x
    convertValue (` t ≤ u) =  ` (convertValue t) ≤ (convertValue u)
    convertValue (` t + u) =  ` (convertValue t) + (convertValue u)
    convertValue (` t * u) =  ` (convertValue t) * (convertValue u)
    convertValue (`v id ∈) = `v id {!!}
    convertValue (`vval u x) = {!!}
    convertValue (`λ x ⦂ σ ⇒ t) = `λ x ∷ [] ⇒ {!convertCont ? ?!}
    convertValue (` t , u) = `obj (("type" , `String , `string "and") ∷
                                    ("fst" , _ , convertValue t) ∷ ("snd" , _ , convertValue u) ∷ [])
    convertValue (`inl t `as σ) = `obj (("type" , `String , `string "or") ∷
                                        ("dir" , `String , `string "inl") ∷
                                        ("inl" , _ , convertValue t) ∷ ("inr" , _ , default (convertType σ)) ∷ [])
    convertValue (`inr t `as τ) = `obj (("type" , `String , `string "or") ∷
                                        ("dir" , `String , `string "inr") ∷
                                        ("inl" , _ , default (convertType τ)) ∷ ("inr" , _ , convertValue t) ∷ [])
    convertValue (`hold t) = {!!}
    convertValue (`sham x) = {!!}
    convertValue (`Λ x) = {!!}
    convertValue (`pack ω t) = {!!}
    convertValue `any = `obj (("type" , `String , `string "addr") ∷ [])

  entryPoint : [] ⊢ₓ ⋆< client > → (Stm [] < client >) × (Stm [] < server >)
  entryPoint t with convertCont {s = {!!} }{s' = {!!}} client t
  ... | a , b =
      (`exp ((` `λ [] ⇒ (`prim `socket ； a ；return `undefined) · []) refl))
    , (`exp ((` `λ [] ⇒ (`prim `io ； b ；return `undefined) · []) refl))
