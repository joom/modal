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

    convertTuple : Id × Typeₒ × World → Id × Typeᵐ × World
    convertTuple (id , τ , w) = (id , convertType τ , w)

    convertCtx : Contextₒ → Contextᵐ
    convertCtx [] = []
    convertCtx ((x ⦂ τ < w >) ∷ xs) = (LiftedMonomorphic.Types.toHyp (convertTuple (x , τ , w))) ∷ convertCtx xs
    convertCtx ((u ∼ C) ∷ xs) = (u ⦂ convertType (C client) < client >) ∷ (u ⦂ convertType (C server) < server >) ∷ convertCtx xs

  convertCtx∈v : ∀ {x τ w Γ} → (x ⦂ τ < w >) ∈ Γ → (x ⦂ convertType τ < w >) ∈ (convertCtx Γ)
  convertCtx∈v (here refl) = here refl
  convertCtx∈v {Γ = (x ⦂ τ < w >) ∷ xs} (there i) = there (convertCtx∈v i)
  convertCtx∈v {Γ = (u ∼ x) ∷ xs} (there i) = there (there (convertCtx∈v i))

  convertCtx∈vv : ∀ {w u C Γ} → (u ∼ C) ∈ Γ → (u ⦂ convertType (C w) < w >) ∈ (convertCtx Γ)
  convertCtx∈vv {client} (here refl) = here refl
  convertCtx∈vv {server} (here refl) = there (here refl)
  convertCtx∈vv {Γ = (x ⦂ τ < w >) ∷ xs} (there i) = there (convertCtx∈vv i)
  convertCtx∈vv {Γ = (u ∼ x) ∷ xs} (there i) = there (there (convertCtx∈vv i))

  convertCtx⊆ : ∀ {Δ Γ} → Δ ⊆ Γ → convertCtx Δ ⊆ convertCtx Γ
  convertCtx⊆ {[]} s = λ ()
  convertCtx⊆ {(x ⦂ τ < w >) ∷ Δ}{Γ} s =
      ⊆-add (convertCtx⊆ {Δ}{Γ} (s ∘ there)) (convertCtx∈v (s (here refl)))
  convertCtx⊆ {(u ∼ C) ∷ Δ}{Γ} s =
      ⊆-add (⊆-add (convertCtx⊆ {Δ}{Γ} (s ∘ there)) (convertCtx∈vv (s (here refl)))) (convertCtx∈vv (s (here refl)))

  convertCtx++ : ∀ {Δ Γ} → convertCtx Δ +++ convertCtx Γ ≡ convertCtx (Δ +++ Γ)
  convertCtx++ {[]} = refl
  convertCtx++ {(x ⦂ τ < w >) ∷ Δ}{Γ} =
      cong (λ xs → (x ⦂ convertType τ < w >) ∷ xs) (convertCtx++ {Δ}{Γ})
  convertCtx++ {(u ∼ C) ∷ Δ}{Γ} =
      cong (λ xs → (u ⦂ convertType (C client) < client >) ∷ (u ⦂ convertType (C server) < server >) ∷ xs) (convertCtx++ {Δ}{Γ})

  convertMobile : ∀ {τ} → Closure.Types._mobile τ → LiftedMonomorphic.Types._mobile (convertType τ)
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

  hypLocalize : Hypₒ → World → Hypᵐ
  hypLocalize (x ⦂ τ < w >) w' = x ⦂ convertType τ < w >
  hypLocalize (u ∼ C) w = u ⦂ convertType (C w) < w >

  convertPrim : ∀ {h} → Closure.Terms.Prim h → (w : World) → LiftedMonomorphic.Terms.Prim (hypLocalize h w)
  convertPrim `alert w = `alert
  convertPrim `version w = `version
  convertPrim `log client = `logCli
  convertPrim `log server = `logSer
  convertPrim `prompt w = `prompt
  convertPrim `readFile w = `readFile


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
    convertValue (`sham C) = `sham (λ ω → convertValue (C ω))
    convertValue (`Λ C) = `Λ (λ ω → convertValue (C ω))
    convertValue (`pack ω t) = `pack ω (convertValue t)
    convertValue (`packΣ τ t) = `packΣ (convertType τ) (convertValue t)
    convertValue (`buildEnv x) = `buildEnv (convertCtx⊆ x)

    convertCont : ∀ {Γ w}
                → Γ ⊢ₒ ⋆< w >
                → (convertCtx Γ) ⊢ᵐ ⋆< w >
    convertCont (`if t `then u `else v) = `if convertValue t `then convertCont u `else convertCont v
    convertCont (`letcase x , y `= t `in u `or v) = `letcase x , y `= convertValue t `in convertCont u `or convertCont v
    convertCont (`leta x `= t `in u) = `leta x `= convertValue t `in convertCont u
    convertCont (`lets u `= t `in v) = `lets u `= convertValue t `in convertCont v
    convertCont (`put_`=_`in_ {C = C}{m = m} u t v) =
        `put_`=_`in_ {C = λ ω → convertType (C ω)} {m = convertMobile m} u (convertValue t) (convertCont v)
    convertCont (`let x `=fst t `in u) = `let x `=fst convertValue t `in convertCont u
    convertCont (`let x `=snd t `in u) = `let x `=snd convertValue t `in convertCont u
    convertCont (`let x `= t ⟨ w' ⟩`in u) = `let x `= convertValue t ⟨ w' ⟩`in convertCont u
    convertCont (`let x =`unpack t `in u) = `let x =`unpack convertValue t `in (λ ω → convertCont (u ω))
    convertCont (`call t u) = `call (convertValue t) (convertValue u)
    convertCont `halt = `halt
    convertCont (`prim_`in_ {h} p t) with h
    ... | x ⦂ τ < w > = `prim convertPrim p w `in convertCont t
    ... | u ∼ x = `prim convertPrim p server `in (`prim convertPrim p client `in convertCont t)
    convertCont (`go-cc[ w' ] t) = `go-cc[ w' ] convertValue t
    convertCont (`let τ , x `=unpack t `in u) = `let convertType τ , x `=unpack convertValue t `in convertCont u
    convertCont (`open_`in_ {Δ = Δ}{w = w} t u) =
        `open convertValue t `in eq-replace (cong (λ l → l ⊢ᵐ ⋆< w > ) (sym (convertCtx++ {Δ}))) (convertCont u)

  convertTuples : List (Id × Typeₒ × World) → List (Id × Typeᵐ × World)
  convertTuples [] = []
  convertTuples (x ∷ xs) = convertTuple x ∷ convertTuples xs

  entryPoint : ∀ {w}
             → Σ (List (Id × Typeₒ × World))
                 (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) newbindings × (Closure.Types.toCtx newbindings) ⊢ₒ ⋆< w >)
             → Σ (List (Id × Typeᵐ × World))
                 (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) newbindings × (LiftedMonomorphic.Types.toCtx newbindings) ⊢ᵐ ⋆< w >)
  entryPoint {w = w} (xs , all , t) =
        convertTuples xs
      , convertAll all
      , eq-replace (cong (λ l → l ⊢ᵐ ⋆< w >) (ctxEq {xs})) (convertCont t)
    where
      ctxEq : ∀ {xs} → convertCtx (Closure.Types.toCtx xs) ≡ LiftedMonomorphic.Types.toCtx (convertTuples xs)
      ctxEq {[]} = refl
      ctxEq {(x , τ , w) ∷ xs} = cong (λ l → (x ⦂ convertType τ < w >) ∷ l) (ctxEq {xs})

      convertAll : ∀ {xs} → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) xs
                          → All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) (convertTuples xs)
      convertAll {[]} [] = []
      convertAll {x ∷ xs} (px ∷ pxs) = convertValue px ∷ (convertAll pxs)
