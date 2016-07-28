module CPStoClosure where

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
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions
  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import Closure.Types renaming (Type to Typeₒ ; Hyp to Hypₒ)
  open import Closure.Terms renaming (_⊢_ to _⊢ₒ_)

  convertType : Typeₓ → Typeₒ
  convertType `Int = `Int
  convertType `Bool = `Bool
  convertType `Unit = `Unit
  convertType `String = `String
  convertType ` τ cont = `Σ (λ α → ` α × (` (` convertType τ × α) cont))
  convertType (` τ × σ) = ` (convertType τ) × (convertType σ)
  convertType (` τ ⊎ σ) = ` (convertType τ) ⊎ (convertType σ)
  convertType (` τ at w) = ` (convertType τ) at w
  convertType ` w addr = ` w addr
  convertType (`⌘ C) = `⌘ (λ ω → convertType (C ω))
  convertType (`∀ C) = `∀ (λ ω → convertType (C ω))
  convertType (`∃ C) = `∃ (λ ω → convertType (C ω))

  convertHyp : Hypₓ → Hypₒ
  convertHyp (x ⦂ τ < w >) = x ⦂ (convertType τ) < w >
  convertHyp (u ∼ C) = u ∼ (λ ω → convertType (C ω))

  convertCtx : CPS.Types.Context → Closure.Types.Context
  convertCtx = Data.List.map convertHyp

  hypToType : Hypₓ → Typeₒ
  hypToType (x ⦂ τ < w >) = ` (convertType τ) at w
  hypToType (u ∼ C) = `⌘ (λ ω → convertType (C ω))

  -- freeVars : ∀ {Γ w Δ} → Γ ⊢ₓ ⋆< w > → Σ Typeₒ (λ α → Δ ⊢ₒ ↓ α < w >)

  contextToType : CPS.Types.Context → Typeₒ
  contextToType g = foldr (λ h τ → ` hypToType h × τ) `Unit g

  mutual
    convertCont : ∀ {Γ w} → Γ ⊢ₓ ⋆< w > → (convertCtx Γ) ⊢ₒ ⋆< w >
    -- Interesting cases
    convertCont (`call t u) =
      `let {!!} , "p" `=unpack (convertValue t) `in
      `let "e" `=fst `v "p" (here refl) `in
      `let "f" `=snd `v "p" (there (here refl)) `in
      `call (`v "f" (here refl)) (`v "e" (there (here refl)))
    convertCont (`go[ w' , t ] u) = `go-cc[ w' , `any ] (convertValue (`λ "y" ⦂ `Unit ⇒ {!convertCont u!}))
    -- Trivial cases
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
    convertCont `halt = `halt
    convertCont (`prim x `in t) = {!!}

    convertValue : ∀ {Γ τ w} → Γ ⊢ₓ ↓ τ < w > → (convertCtx Γ) ⊢ₒ ↓ (convertType τ) < w >
    -- Interesting cases
    convertValue (`λ x ⦂ σ ⇒ t) = `packΣ env (` {!!} , (`λ "p" ⦂ ` convertType σ × env ⇒ c ))
      where
        env : Typeₒ
        env = {!!}
        c = `let "x" `=snd `v "p" (here refl) `in
          `let "e" `=fst `v "p" (there (here refl)) `in
          {!!}
    -- Trivial cases
    convertValue `tt = {!!}
    convertValue (`string x) = {!!}
    convertValue `true = {!!}
    convertValue `false = {!!}
    convertValue (` t ∧ t₁) = {!!}
    convertValue (` t ∨ t₁) = {!!}
    convertValue (`¬ t) = {!!}
    convertValue (`n x) = {!!}
    convertValue (` t ≤ t₁) = {!!}
    convertValue (` t + t₁) = {!!}
    convertValue (` t * t₁) = {!!}
    convertValue (`v x x₁) = {!!}
    convertValue (`vval u x) = {!!}
    convertValue (` t , t₁) = {!!}
    convertValue (`inl t `as σ) = {!!}
    convertValue (`inr t `as τ) = {!!}
    convertValue (`hold t) = {!!}
    convertValue (`sham x) = {!!}
    convertValue (`Λ x) = {!!}
    convertValue (`pack ω t) = {!!}
    convertValue `any = {!!}
