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
  open import Data.List.Any.Properties using (++ʳ ; ++ˡ)
  import Data.List.Any.Membership using (_++-mono_)
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
  convertType ` τ cont = `Σt[t×[ convertType τ ×t]cont]
  convertType (` τ × σ) = ` (convertType τ) × (convertType σ)
  convertType (` τ ⊎ σ) = ` (convertType τ) ⊎ (convertType σ)
  convertType (` τ at w) = ` (convertType τ) at w
  convertType (`⌘ C) = `⌘ (λ ω → convertType (C ω))
  convertType (`∀ C) = `∀ (λ ω → convertType (C ω))
  convertType (`∃ C) = `∃ (λ ω → convertType (C ω))

  convertMobile : ∀ {τ} → CPS.Types._mobile τ → Closure.Types._mobile (convertType τ)
  convertMobile `Boolᵐ = `Boolᵐ
  convertMobile `Intᵐ = `Intᵐ
  convertMobile `Unitᵐ = `Unitᵐ
  convertMobile `Stringᵐ = `Stringᵐ
  convertMobile `_atᵐ_ = `_atᵐ_
  convertMobile (` m ×ᵐ n) = ` convertMobile m ×ᵐ convertMobile n
  convertMobile (` m ⊎ᵐ n) = ` (convertMobile m) ⊎ᵐ (convertMobile n)
  convertMobile (`∀ᵐ m) = `∀ᵐ (convertMobile m)
  convertMobile (`∃ᵐ m) = `∃ᵐ (convertMobile m)
  convertMobile `⌘ᵐ = `⌘ᵐ

  convertHyp : Hypₓ → Hypₒ
  convertHyp (x ⦂ τ < w >) = x ⦂ (convertType τ) < w >
  convertHyp (u ∼ C) = u ∼ (λ ω → convertType (C ω))

  convertPrim : ∀ {h} → CPS.Terms.Prim h → Closure.Terms.Prim (convertHyp h)
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `log = `log
  convertPrim `prompt = `prompt
  convertPrim `readFile = `readFile

  convertCtx : CPS.Types.Context → Closure.Types.Context
  convertCtx = Data.List.map convertHyp

  convert∈ : ∀ {h Γ} → h ∈ Γ → (convertHyp h) ∈ (convertCtx Γ)
  convert∈ (here px) = here (cong convertHyp px)
  convert∈ (there i) = there (convert∈ i)

  hypToType : Hypₓ → Typeₒ
  hypToType (x ⦂ τ < w >) = ` (convertType τ) at w
  hypToType (u ∼ C) = `⌘ (λ ω → convertType (C ω))

  -- freeVars : ∀ {Γ w Δ} → Γ ⊢ₓ ⋆< w > → Σ Typeₒ (λ α → Δ ⊢ₒ ↓ α < w >)

  contextToType : CPS.Types.Context → Typeₒ
  contextToType = foldr (λ h τ → ` hypToType h × τ) `Unit

  contextToTerm : ∀ {w} → (Γ : CPS.Types.Context) → (convertCtx Γ) ⊢ₒ ↓ (contextToType Γ) < w >
  contextToTerm [] = `tt
  contextToTerm {w} (x ∷ xs) with contextToTerm {w} xs
  contextToTerm ((x ⦂ τ < w' >) ∷ xs) | t = ` (`hold (`v x (here refl))) , Closure.Terms.⊆-term-lemma there t
  contextToTerm ((u ∼ C) ∷ xs) | t = ` `sham (λ ω → `vval u (here refl)) , Closure.Terms.⊆-term-lemma there t

  contextHelper : (Γ : CPS.Types.Context) → List (Σ Hypₓ (λ h → h ∈ Γ))
  contextHelper [] = []
  contextHelper (y ∷ ys) = (y , here refl) ∷ Data.List.map (λ { (h , ∈) → h , there ∈ }) (contextHelper ys)

  {-# NON_TERMINATING #-} -- TODO
  mutual
    convertCont : ∀ {Γ w} → Γ ⊢ₓ ⋆< w > → (convertCtx Γ) ⊢ₒ ⋆< w >
    -- Interesting cases
    convertCont {Γ} (`call t u) =
      `let contextToType Γ , "p" `=unpack (convertValue t) `in
      `let "e" `=fst `v "p" (here refl) `in
      `let "f" `=snd `v "p" (there (here refl)) `in
      `call (`v "f" (here refl))
            (` Closure.Terms.⊆-term-lemma (there ∘ there ∘ there) (convertValue u) , `v "e" (there (here refl)))
    convertCont (`go[ w' ] u) = `go-cc[ w' ] (convertValue (`λ "y" ⦂ `Unit ⇒ CPS.Terms.⊆-cont-lemma there u ))
    -- Trivial cases
    convertCont (`if t `then u `else v) = `if convertValue t `then convertCont u `else convertCont v
    convertCont (`letcase x , y `= t `in u `or v) = `letcase x , y `= convertValue t `in convertCont u `or convertCont v
    convertCont (`leta x `= t `in u) = `leta x `= convertValue t `in convertCont u
    convertCont (`lets u `= t `in v) = `lets u `= convertValue t `in convertCont v
    convertCont (`put_`=_`in_ {m = m} u t v) = `put_`=_`in_ {m = convertMobile m} u (convertValue t) (convertCont v)
    convertCont (`let x `=fst t `in u) = `let x `=fst convertValue t `in convertCont u
    convertCont (`let x `=snd t `in u) = `let x `=snd convertValue t `in convertCont u
    convertCont (`let x `= t ⟨ w' ⟩`in u) = `let x `= convertValue t ⟨ w' ⟩`in convertCont u
    convertCont (`let_=`unpack_`in_ x t u) = `let_=`unpack_`in_ x (convertValue t) (λ ω → convertCont (u ω))
    convertCont `halt = `halt
    convertCont (`prim x `in t) = `prim convertPrim x `in convertCont t

    convertValue : ∀ {Γ τ w} → Γ ⊢ₓ ↓ τ < w > → (convertCtx Γ) ⊢ₒ ↓ (convertType τ) < w >
    -- Interesting cases
    convertValue {Γ}{_}{w} (`λ x ⦂ σ ⇒ t) = `packΣ (`Env (convertCtx Γ)) (` `buildEnv id , (`λ "p" ⦂ _ ⇒ c))
      where
        t' : convertCtx ((x ⦂ σ < w >) ∷ Γ) ⊢ₒ ⋆< w >
        t' = convertCont t

        c : (("p" ⦂ ` convertType σ × `Env (convertCtx Γ) < w >) ∷ []) ⊢ₒ ⋆< w >
        c = `let "env" `=snd `v "p" (here refl) `in
            `open `v "env" (here refl) `in
            `let x `=fst `v "p" (++ʳ (convertCtx Γ) (there (here refl))) `in
            (Closure.Terms.⊆-cont-lemma (sub-lemma ++ˡ) t')
    -- Trivial cases
    convertValue `tt = `tt
    convertValue (`string x) = `string x
    convertValue `true = `true
    convertValue `false = `false
    convertValue (` t ∧ u) = ` convertValue t ∧ convertValue u
    convertValue (` t ∨ u) = ` convertValue t ∨ convertValue u
    convertValue (`¬ t) = `¬ convertValue t
    convertValue (`n x) = `n x
    convertValue (` t ≤ u) = ` convertValue t ≤ convertValue u
    convertValue (` t + u) = ` convertValue t + convertValue u
    convertValue (` t * u) = ` convertValue t * convertValue u
    convertValue (`v x ∈) = `v x (convert∈ ∈)
    convertValue (`vval u ∈) = `vval u (convert∈ ∈)
    convertValue (` t , u) = ` convertValue t , convertValue u
    convertValue (`inl t `as σ) = `inl convertValue t `as convertType σ
    convertValue (`inr t `as τ) = `inr convertValue t `as convertType τ
    convertValue (`hold t) = `hold (convertValue t)
    convertValue (`sham x) = `sham (λ ω → convertValue (x ω))
    convertValue (`Λ x) = `Λ (λ ω → convertValue (x ω))
    convertValue (`pack ω t) = `pack ω (convertValue t)
