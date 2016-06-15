module ML5toCPS where

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
  open import ML5.Types renaming (Type to Type₅ ; Hyp to Hyp₅)
  open import ML5.Terms renaming (_⊢_ to _⊢₅_)
  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)

  convertType : Type₅ → Typeₓ
  convertType `Nat = `Nat
  convertType `Bool = `Bool
  convertType `Unit = `Unit
  convertType `String = `String
  convertType (` τ ⇒ σ) = ` (` (convertType τ) × (` convertType σ cont)) cont
  convertType (` τ × σ) = ` (convertType τ) × (convertType σ)
  convertType (` τ ⊎ σ) = ` (convertType τ) ⊎ (convertType σ)
  convertType (` τ at w) = ` (convertType τ) at w
  convertType ` w addr = ` w addr
  convertType (`⌘ C) = `⌘ (λ ω → convertType (C ω))
  convertType (`∀ C) = `∀ (λ ω → convertType (C ω))
  convertType (`∃ C) = `∃ (λ ω → convertType (C ω))

  convertHyp : ML5.Types.Hyp → CPS.Types.Hyp
  convertHyp (x ⦂ τ < w >) = x ⦂ (convertType τ) < w >
  convertHyp (u ∼ C) = u ∼ (λ ω → convertType (C ω))

  convertCtx : ML5.Types.Context → CPS.Types.Context
  convertCtx = Data.List.map convertHyp

  convert∈ : ∀ {h Γ} → h ∈ Γ → (convertHyp h) ∈ (convertCtx Γ)
  convert∈ (here px) = here (cong convertHyp px)
  convert∈ (there i) = there (convert∈ i)

  ⊆-∈-lemma : ∀ {h} {Γ Γ' : CPS.Types.Context} → Γ ⊆ Γ' → h ∈ Γ → h ∈ Γ'
  ⊆-∈-lemma sub i = sub i

  convert-lemma : ∀ {x σ w Γ} → convertCtx (x ⦂ σ < w > ∷ Γ) ≡ (x ⦂ convertType σ < w > ∷ convertCtx Γ)
  convert-lemma = refl

  -- If there are two things in the context with different names, their order doesn't matter.
  -- We also included subsets to that proposition.
  swap-lemma : ∀ {x y σ τ w w' Γ Γ'} {b : Hypₓ}
             → x ≢ y
             → b ∈ ((x ⦂ σ < w >) ∷ (y ⦂ τ < w' >) ∷ Γ)
             → Γ ⊆ Γ'
             → b ∈ ((y ⦂ τ < w' >) ∷ (x ⦂ σ < w >) ∷ Γ')
  swap-lemma {x}{y}{σ}{τ}{w}{w'}{b = b} neq i s with b decHyp (x ⦂ σ < w >)
  swap-lemma neq i s | yes refl = there (here refl)
  swap-lemma {x}{y}{σ}{τ}{w}{w'}{b = b} neq i s | no q with b decHyp (y ⦂ τ < w' >)
  swap-lemma neq i s | no q | yes refl = here refl
  swap-lemma neq (here px) s | no q | no q' = ⊥-elim (q px)
  swap-lemma neq (there (here px)) s | no q | no q' = ⊥-elim (q' px)
  swap-lemma neq (there (there i)) s | no q | no q' = there (there (s i))

  mutual
    convertValue : ∀ {Γ Γ' τ w } {s : (convertCtx Γ) ⊆ Γ'} → Γ ⊢₅ ↓ τ < w > → Γ' ⊢ₓ ↓ (convertType τ) < w >
    convertValue `tt = `tt
    convertValue `true = `true
    convertValue `false = `false
    convertValue {s = s} (` t ∧ u) = ` (convertValue {s = s} t) ∧ (convertValue {s = s} u)
    convertValue {s = s} (` t ∨ u) = ` (convertValue {s = s} t) ∨ (convertValue {s = s} u)
    convertValue {s = s} (`¬ t) = `¬ (convertValue {s = s} t)
    convertValue (`n x) = `n x
    convertValue {s = s} (` t ≤ u) = ` (convertValue {s = s} t) ≤ (convertValue {s = s} u)
    convertValue {s = s} (` t + u) = ` (convertValue {s = s} t) + (convertValue {s = s} u)
    convertValue {s = s} (` t * u) = ` (convertValue {s = s} t) * (convertValue {s = s} u)
    convertValue {s = s} (`v x ∈) = `v x (⊆-∈-lemma s (convert∈ ∈))
    convertValue {s = s} (`vval u ∈ eq) = `vval u (⊆-∈-lemma s (convert∈ ∈)) (cong convertType eq)
    convertValue {s = s} (`λ x ⦂ σ ⇒ t) =
      `λ (x ++ "_y") ⦂ (` (convertType σ) × ` _ cont) ⇒
      (`let x `=fst (`v (x ++ "_y") (here refl)) `in
       convertExpr {s = λ {b} i → swap-lemma neq-pf (there i) s}
                   (λ {_}{s'} v →
                   `let (x ++ "_k") `=snd `v (x ++ "_y") (⊆-∈-lemma s' (there (here refl)))
                   `in (`call (`v (x ++ "_k") (here refl)) {!v!})) t)
      where
        postulate
         -- TODO prove this sometime! If we convert the strings to lists
         -- then we can do induction on them. This is a very irrelevant part of
         -- the proof so it doesn't matter much.
         -- Hint: https://agda.github.io/agda-stdlib/Data.String.Base.html#1046
         neq-pf : ∀ {s} → s ++ "_y" ≢ s

    convertValue {s = s} (` t , u) = ` (convertValue {s = s} t) , (convertValue {s = s} u)
    convertValue {s = s} (`inl t `as σ) = `inl (convertValue {s = s} t) `as (convertType σ)
    convertValue {s = s} (`inr t `as τ) = `inr (convertValue {s = s} t) `as (convertType τ)
    convertValue {s = s} (`hold t) = `hold (convertValue {s = s} t)
    convertValue {s = s} (`Λ C) = `Λ (λ ω → convertValue {s = s} (C ω))
    convertValue {s = s} (`wpair ω t) = `pack ω (convertValue {s = s} t)
    convertValue `any = `any

    convertExpr : ∀ {Γ Γ' τ w}
                → {s : (convertCtx Γ) ⊆ Γ'}
                → (∀ {Γ''} {s' : Γ' ⊆ Γ''} → Γ'' ⊢ₓ ↓ (convertType τ) < w > → Γ'' ⊢ₓ ⋆< w >)
                → Γ ⊢₅ τ < w >
                → Γ' ⊢ₓ ⋆< w >
    convertExpr K (`if t `then t₁ `else t₂) = {!!}
    convertExpr K (` t · u) = convertExpr (λ v → convertExpr (λ v' → `call {!v!} {!u!}) u) t
    convertExpr K (`case t `of u || v) = {!!}
    convertExpr {s = s} K (`leta x `= t `in u) = convertExpr {s = s} (λ v → `leta x `= v `in convertExpr K u) t
    convertExpr {s = s} K (`letsham x `= t `in u) = convertExpr {s = s} (λ v → `lets x `= v `in convertExpr K u) t
    convertExpr K (`sham x) = {!!}
    convertExpr K (t ⟨ ω ⟩) = {!!}
    convertExpr K (`unpack x `= t `in x₁) = {!!}
    convertExpr K `localhost = `let "x" `=localhost`in K {s' = {!!}} (`v "x" (here refl))
    convertExpr {s = s} K (`val t) = K {!t!}
    convertExpr K (`get a t) = convertExpr (λ vₐ → `let "x" `=localhost`in {!(`put ? `= ? `in ?)!}) a
    convertExpr K (`put u t t₁) = {!!}
    convertExpr {Γ}{Γ'}{s = s} K (`prim_`in_ x {pf} t) =
        `prim_`in_ x {convertPrim {x} pf} (convertExpr {s = sub} (λ {Γ''}{s'} → K {Γ''} {s' ∘ there} ) t)
      where
        convertPrim : ∀ {x} → isJust (ML5.Terms.primHyp x) → isJust (CPS.Terms.primHyp x)
        convertPrim {"alert"} is = Data.Unit.tt
        convertPrim {"version"} is = Data.Unit.tt
        convertPrim {"log"} is = Data.Unit.tt
        convertPrim {x} is with ML5.Terms.primHyp x
        ... | nothing = {!!}
        ... | just h = {!!}
        sub : convertCtx (fromJust (ML5.Terms.primHyp x) pf ∷ Γ) ⊆ fromJust (CPS.Terms.primHyp x) (convertPrim {x} pf) ∷ Γ'
        sub {x = x'} b with x' decHyp (fromJust (CPS.Terms.primHyp x) (convertPrim {x} pf))
        sub b | yes refl = here refl
        ... | no q = there (s (neq-pf b))
          where
            eq : convertHyp (fromJust (ML5.Terms.primHyp x) pf) ≡ fromJust (CPS.Terms.primHyp x) (convertPrim {x} pf)
            eq with convertPrim {x} pf
            ... | n = {!!}
            neq-pf : x' ∈ (convertHyp (fromJust (ML5.Terms.primHyp x) pf) ∷ convertCtx Γ) → x' ∈ convertCtx Γ
            neq-pf (here px) = ⊥-elim (q (trans px eq))
            neq-pf (there i) = i


    convertExpr {s = s} K (`fst t) = convertExpr {s = s} (λ {_}{s''} v → `let "x" `=fst v `in K {s' = there ∘ s''} (`v "x" (here refl))) t
    convertExpr {s = s} K (`snd t) = convertExpr {s = s} (λ {_}{s''} v → `let "x" `=snd v `in K {s' = there ∘ s''} (`v "x" (here refl))) t
