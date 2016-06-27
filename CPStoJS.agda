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

  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ ; Context to Contextₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import JS.Types renaming (Type to Typeⱼ ; Hyp to Hypⱼ ; Context to Contextⱼ)
  open import JS.Terms renaming (_⊢_ to _⊢ⱼ_)

  convertType : Typeₓ → Typeⱼ
  convertType `Int = `Number
  convertType `Bool = `Bool
  convertType `Unit = `Object (("type" , `String) ∷ [])
  convertType `String = `String
  convertType ` τ cont = `Function [ convertType τ ] `Undefined
  convertType (` τ × σ) = `Object (("type" , `String) ∷ ("fst" , convertType τ ) ∷ ("snd" , convertType σ) ∷ [])
  convertType (` τ ⊎ σ) = `Object (("type" , `String) ∷ ("dir" , `String) ∷ ("inl" , convertType τ) ∷ ("inr" , convertType σ) ∷ [])
  convertType (` τ at w) = `Object (("type" , `String) ∷ [])
  convertType ` x addr = `Object {!!}
  convertType (`⌘ x) = {!!}
  convertType (`∀ x) = {!!}
  convertType (`∃ x) = {!!}

  convertCtx : Contextₓ → Contextⱼ
  convertCtx = {!!}


  convertCont : ∀ {Γ w} → Γ ⊢ₓ ⋆< w > → Stm (convertCtx Γ) < w >
  convertCont (`if t `then t₁ `else t₂) = {!!}
  convertCont (`letcase x , y `= t `in t₁ `or t₂) = {!!}
  convertCont (`leta x `= t `in t₁) = {!!}
  convertCont (`lets u `= t `in t₁) = {!!}
  convertCont (`put u `= t `in t₁) = {!!}
  convertCont (`let x `=fst t `in t₁) = {!!}
  convertCont (`let x `=snd t `in t₁) = {!!}
  convertCont (`let x `=localhost`in t) = {!!}
  convertCont (`let x `= t ⟨ w' ⟩`in t₁) = {!!}
  convertCont (`let_=`unpack_`=_`in_ x t x₁) = {!!}
  convertCont (`go[ w' , t ] t₁) = {!!}
  convertCont (`call t t₁) = {!!}
  convertCont `halt = {!!}
  convertCont (`prim x `in t) = {!!}

  convertValue : ∀ {Γ τ w} → Γ ⊢ₓ ↓ τ < w > → (convertCtx Γ) ⊢ⱼ (convertType τ) < w >
  convertValue `tt = `obj (("type" , `String , `string "unit") ∷ [])
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
  convertValue (`λ x ⦂ σ ⇒ t) = {!!}
  convertValue (` t , t₁) = {!!}
  convertValue (`inl t `as σ) = {!!}
  convertValue (`inr t `as τ) = {!!}
  convertValue (`hold t) = {!!}
  convertValue (`sham x) = {!!}
  convertValue (`Λ x) = {!!}
  convertValue (`pack ω t) = {!!}
  convertValue `any = {!!}

  entryPoint : [] ⊢ₓ ⋆< client > → (Stm [] < client >) × (Stm [] < server >)
  entryPoint t =
      (`exp ((` `λ [] ⇒ ({!!} ；return `undefined) · []) refl))
    , (`exp ((` `λ [] ⇒ ({!!} ；return `undefined) · []) refl))
