module LiftedMonomorphize where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  open import Data.Nat.Show
  import Data.Unit
  open import Data.Maybe hiding (All)
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation using (contraposition)
  open import Data.String using (_++_)
  open import Data.Nat.Show
  open import Data.List renaming (_++_ to _+++_)
  open import Data.List.Any.Membership
  open import Data.List.Any
  open import Data.List.Any.Properties using (++ʳ ; ++ˡ)
  open import Data.List.All
  open import Data.Vec hiding (_++_ ; _∈_)
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  open import Closure.Types renaming (Type to Typeₒ ; Hyp to Hypₒ ; Conc to Concₒ ; Context to Contextₒ)
  open import Closure.Terms renaming (_⊢_ to _⊢ₒ_)
  open import LiftedMonomorphic.Types renaming (Type to Typeᵐ ; Hyp to Hypᵐ ; Conc to Concᵐ ; Context to Contextᵐ)
  open import LiftedMonomorphic.Terms renaming (_⊢_ to _⊢ᵐ_)

  mutual
    convertType : Typeₒ → Typeᵐ
    convertType `Int = `Int
    convertType `Bool = `Bool
    convertType `Unit = `Unit
    convertType `String = `String
    convertType ` t cont = ` (convertType t) cont
    convertType (` t × u) = ` convertType t × convertType u
    convertType (` t ⊎ u) = ` convertType t ⊎ convertType u
    convertType (` t at x) = ` convertType t at x
    convertType (`⌘ C) = `⌘ (λ ω → convertType (C ω))
    convertType (`∀ C) = `∀ (λ ω → convertType (C ω))
    convertType (`∃ C) = `∃ (λ ω → convertType (C ω))
    convertType `Σt[t×[ t ×t]cont] = `Σt[t×[ convertType t ×t]cont]
    convertType (`Env Γ) = `Env (convertCtx Γ)

    convertCtx : Contextₒ → Contextᵐ
    convertCtx [] = []
    convertCtx ((x ⦂ τ < w >) ∷ xs) = (x ⦂ convertType τ < w >) ∷ convertCtx xs
    convertCtx ((u ∼ C) ∷ xs) = (u ⦂ convertType (C client) < client >) ∷ (u ⦂ convertType (C server) < server >) ∷ convertCtx xs

  convertPrim : ∀ {h} → Closure.Terms.Prim h → LiftedMonomorphic.Terms.Prim (convertCtx (h ∷ []))
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `log = `log
  convertPrim `prompt = `prompt
  convertPrim `readFile = `readFile

  hypLocalize : Hypₒ → World → Hypᵐ
  hypLocalize (x ⦂ τ < w >) w' = x ⦂ convertType τ < w >
  hypLocalize (u ∼ C) w = u ⦂ convertType (C w) < w >

  convert∈ : ∀ {ω} → (Γ : Contextₒ) → (h : Hypₒ) → h ∈ Γ → hypLocalize h ω ∈ convertCtx Γ
  convert∈ _ (x ⦂ τ < w >) (here refl) = here refl
  convert∈ {client} _ (u ∼ C) (here refl) = here refl
  convert∈ {server} _ (u ∼ C) (here refl) = there (here refl)
  convert∈ {ω} ((x ⦂ τ < w >) ∷ xs) h (there i) = there (convert∈ {ω} xs h i)
  convert∈ {ω} ((u ∼ C) ∷ xs) h (there i) = there (there (convert∈ {ω} xs h i))

  mutual
    convertValue : ∀ {Γ τ w}
                → Γ ⊢ₒ ↓ τ < w >
                → (convertCtx Γ) ⊢ᵐ ↓ convertType τ < w >
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
    convertValue {w = w} (`v x ∈) = `v x (convert∈ {w} _ _ ∈)
    convertValue {w = w} (`vval u ∈) = `v u (convert∈ {w} _ _ ∈)
    convertValue (`λ x ⦂ σ ⇒ t) = `λ x ⦂ convertType σ ⇒ convertCont t
    convertValue (` t , u) = ` convertValue t , convertValue u
    convertValue (`inl t `as σ) = `inl convertValue t `as convertType σ
    convertValue (`inr t `as τ) = `inr convertValue t `as convertType τ
    convertValue (`hold t) = `hold (convertValue t)
    convertValue (`sham C) = {!!}
    convertValue (`Λ C) = `Λ (λ ω → convertValue (C ω))
    convertValue (`pack ω t) = `pack ω (convertValue t)
    convertValue (`packΣ τ t) = `packΣ (convertType τ) (convertValue t)
    convertValue (`buildEnv x) = `buildEnv {!x!}

    convertCont : ∀ {Γ w}
                → Γ ⊢ₒ ⋆< w >
                → (convertCtx Γ) ⊢ᵐ ⋆< w >
    convertCont (`if t `then u `else v) = `if convertValue t `then convertCont u `else convertCont v
    convertCont (`letcase x , y `= t `in u `or v) = `letcase x , y `= convertValue t `in convertCont u `or convertCont v
    convertCont (`leta x `= t `in u) = `leta x `= convertValue t `in convertCont u
    convertCont (`lets u `= t `in v) = `lets u `= convertValue t `in convertCont v
    convertCont (`put u `= t `in v) = {!!} -- `put u `= convertValue t `in convertCont v
    convertCont (`let x `=fst t `in u) = `let x `=fst convertValue t `in convertCont u
    convertCont (`let x `=snd t `in u) = `let x `=snd convertValue t `in convertCont u
    convertCont (`let x `= t ⟨ w' ⟩`in u) = `let x `= convertValue t ⟨ w' ⟩`in convertCont u
    convertCont (`let x =`unpack t `in u) = {!`let x =`unpack convertValue t `in convertCont u!}
    convertCont (`call t u) = `call (convertValue t) (convertValue u)
    convertCont `halt = `halt
    convertCont (`prim x `in t) = `prim convertPrim x `in {!convertCont t!}
    convertCont (`go-cc[ w' ] t) = `go-cc[ w' ] convertValue t
    convertCont (`let τ , x `=unpack t `in u) = `let convertType τ , x `=unpack convertValue t `in convertCont u
    convertCont (`open t `in u) = `open convertValue t `in {!convertCont u!}

  entryPoint : ∀ {Γ w}
             → Σ (List (Id × Typeₒ × World))
                 (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) newbindings × (Γ +++ Closure.Types.toCtx newbindings) ⊢ₒ ⋆< w >)
             → Σ (List (Id × Typeᵐ × World))
                 (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) newbindings × (convertCtx Γ +++ LiftedMonomorphic.Types.toCtx newbindings) ⊢ᵐ ⋆< w >)
  entryPoint (xs , all , t) = {!!}
