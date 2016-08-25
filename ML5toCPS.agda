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
  convertType `Int = `Int
  convertType `Bool = `Bool
  convertType `Unit = `Unit
  convertType `String = `String
  convertType (` τ ⇒ σ) = ` (` (convertType τ) × (` convertType σ cont)) cont
  convertType (` τ × σ) = ` (convertType τ) × (convertType σ)
  convertType (` τ ⊎ σ) = ` (convertType τ) ⊎ (convertType σ)
  convertType (` τ at w) = ` (convertType τ) at w
  convertType (`⌘ C) = `⌘ (λ ω → convertType (C ω))
  convertType (`∀ C) = `∀ (λ ω → convertType (C ω))
  convertType (`∃ C) = `∃ (λ ω → convertType (C ω))

  convertHyp : ML5.Types.Hyp → CPS.Types.Hyp
  convertHyp (x ⦂ τ < w >) = x ⦂ (convertType τ) < w >
  convertHyp (u ∼ C) = u ∼ (λ ω → convertType (C ω))

  convertPrim : ∀ {h} → ML5.Terms.Prim h → CPS.Terms.Prim (convertHyp h)
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `log = `log
  convertPrim `prompt = `prompt
  convertPrim `readFile = `readFile

  convertCtx : ML5.Types.Context → CPS.Types.Context
  convertCtx = Data.List.map convertHyp

  convert∈ : ∀ {h Γ} → h ∈ Γ → (convertHyp h) ∈ (convertCtx Γ)
  convert∈ (here px) = here (cong convertHyp px)
  convert∈ (there i) = there (convert∈ i)

  ⊆-∈-lemma : ∀ {h} {Γ Γ' : CPS.Types.Context} → Γ ⊆ Γ' → h ∈ Γ → h ∈ Γ'
  ⊆-∈-lemma sub i = sub i

  convertMobile : ∀ {τ} → ML5.Types._mobile τ → CPS.Types._mobile (convertType τ)
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

  mutual
    convertValue' : ∀ {Γ Γ' τ w } {s : (convertCtx Γ) ⊆ Γ'} → Γ ⊢₅ ↓ τ < w > → Γ' ⊢ₓ ↓ (convertType τ) < w >
    convertValue' `tt = `tt
    convertValue' (`string s) = `string s
    convertValue' `true = `true
    convertValue' `false = `false
    convertValue' {s = s} (` t ∧ u) = ` (convertValue' {s = s} t) ∧ (convertValue' {s = s} u)
    convertValue' {s = s} (` t ∨ u) = ` (convertValue' {s = s} t) ∨ (convertValue' {s = s} u)
    convertValue' {s = s} (`¬ t) = `¬ (convertValue' {s = s} t)
    convertValue' (`n x) = `n x
    convertValue' {s = s} (` t ≤ u) = ` (convertValue' {s = s} t) ≤ (convertValue' {s = s} u)
    convertValue' {s = s} (` t + u) = ` (convertValue' {s = s} t) + (convertValue' {s = s} u)
    convertValue' {s = s} (` t * u) = ` (convertValue' {s = s} t) * (convertValue' {s = s} u)
    convertValue' {s = s} (`v x ∈) = `v x (⊆-∈-lemma s (convert∈ ∈))
    convertValue' {s = s} (`vval u ∈) = `vval u (⊆-∈-lemma s (convert∈ ∈))
    convertValue' {s = s} (`λ x ⦂ σ ⇒ t) =
      `λ (x ++ "_y") ⦂ (` (convertType σ) × ` _ cont) ⇒
      (`let x `=fst (`v (x ++ "_y") (here refl)) `in
       convertExpr' {s = sub-lemma (there ∘ s)}
                   (λ {_}{s'} v →
                   `let (x ++ "_k") `=snd `v (x ++ "_y") (⊆-∈-lemma s' (there (here refl)))
                   `in (`call (`v (x ++ "_k") (here refl)) (⊆-term-lemma there v))) t)
    convertValue' {s = s} (` t , u) = ` (convertValue' {s = s} t) , (convertValue' {s = s} u)
    convertValue' {s = s} (`inl t `as σ) = `inl (convertValue' {s = s} t) `as (convertType σ)
    convertValue' {s = s} (`inr t `as τ) = `inr (convertValue' {s = s} t) `as (convertType τ)
    convertValue' {s = s} (`hold t) = `hold (convertValue' {s = s} t)
    convertValue' {s = s} (`Λ C) = `Λ (λ ω → convertValue' {s = s} (C ω))
    convertValue' {s = s} (`sham C) = `sham (λ ω → convertValue' {s = s} (C ω))
    convertValue' {s = s} (`wpair ω t) = `pack ω (convertValue' {s = s} t)

    convertExpr' : ∀ {Γ Γ' τ w}
                → {s : (convertCtx Γ) ⊆ Γ'}
                → (∀ {Γ''} {s' : Γ' ⊆ Γ''} → Γ'' ⊢ₓ ↓ (convertType τ) < w > → Γ'' ⊢ₓ ⋆< w >)
                → Γ ⊢₅ τ < w >
                → Γ' ⊢ₓ ⋆< w >
    convertExpr' {s = s} K (`if b `then t `else u) =
      convertExpr' {s = s} (λ {_}{s'} v →
        `if v `then convertExpr' {s = s' ∘ s} (λ {_}{s''} → K {_}{s'' ∘ s'}) t
        `else convertExpr' {s = s' ∘ s} (λ {_}{s''} → K {_}{s'' ∘ s'}) u) b
    convertExpr' {s = s} K (`case p `of x ⇒ t || y ⇒ u) =
      convertExpr' {s = s} (λ {_}{s'} v →
        `letcase x , y `= v `in convertExpr' {s = sub-lemma (s' ∘ s)} (λ {_}{s''} → K {_}{s'' ∘ there ∘  s'}) t
        `or convertExpr' {s = sub-lemma (s' ∘ s)} (λ {_}{s''} → K {_}{s'' ∘ there ∘ s'}) u) p
    convertExpr' {s = s} K (` t · u) =
      convertExpr' {s = s} (λ {_}{s'} v → convertExpr' {s = s' ∘ s}
        (λ {_}{s''} v' → `call (⊆-term-lemma s'' v) (` v' , (`λ "x" ⦂ _ ⇒ K {s' = there ∘ s'' ∘ s'} (`v "x" (here refl))))) u) t
    convertExpr' {s = s} K (`leta x `= t `in u) =
      convertExpr' {s = s} (λ {Γ''}{s'} v → `leta x `= v `in convertExpr' {s = sub-lemma (s' ∘ s) } (λ {Γ'''}{s''} → K {Γ'''}{s'' ∘ there  ∘ s'}) u) t
    convertExpr' {s = s} K (`letsham x `= t `in u) =
      convertExpr' {s = s} (λ {Γ''}{s'} v → `lets x `= v `in convertExpr' {s = sub-lemma (s' ∘ s)} (λ {Γ'''}{s''} → K {Γ'''}{s'' ∘ there ∘ s'}) u) t
    convertExpr' {s = s} K (t ⟨ ω ⟩) = convertExpr' {s = s} (λ {Γ'}{s'} v → `let "x" `= v ⟨ ω ⟩`in K {s' = there ∘ s'} (`v "x" (here refl))) t
    convertExpr' {s = s} K (`unpack x `= t `in C) =
      convertExpr' {s = s} (λ {_}{s'} v → `let_=`unpack_`=_`in_ x v
                  (λ ω → convertExpr' {s = sub-lemma (s' ∘ s) } (λ {_}{s''} → K {_}{s'' ∘ there ∘ s'}) (C ω))) t
    convertExpr' {s = s} K (`val t) = K {s' = id} (convertValue' {s = s} t)
    convertExpr' {w = w}{s = s} K (`get {w' = w'}{m = m} t) =
        `go[ w' ] (convertExpr' {s = s} (λ {_}{s'} v →
          `put_`=_`in_ {m = convertMobile m} "u" v (`go[ w  ] (K {s' = there ∘ s'} (`vval "u" (here refl))))) t)
    convertExpr' {s = s} K (`put {m = m} u t n) =
      convertExpr' {s = s} (λ {_}{s'} v →
        `put_`=_`in_ {m = convertMobile m} u v (convertExpr' {s = sub-lemma (s' ∘ s)} (λ {Γ''}{s''} → K {Γ''}{s'' ∘ there ∘ s'}) n)) t
    convertExpr' {Γ}{Γ'}{s = s} K (`prim x `in t) =
      `prim convertPrim x `in convertExpr' {s = sub-lemma s} (λ {_}{s'} → K {_}{s' ∘ there}) t
    convertExpr' {s = s} K (`fst t) = convertExpr' {s = s} (λ {_}{s''} v → `let "x" `=fst v `in K {s' = there ∘ s''} (`v "x" (here refl))) t
    convertExpr' {s = s} K (`snd t) = convertExpr' {s = s} (λ {_}{s''} v → `let "x" `=snd v `in K {s' = there ∘ s''} (`v "x" (here refl))) t


  -- Corollary
  -- For some reason it was easier to prove the ones above.
  convertExpr : ∀ {Γ τ w}
              → (∀ {Γ'} {s' : (convertCtx Γ) ⊆ Γ'} → Γ' ⊢ₓ ↓ (convertType τ) < w > → Γ' ⊢ₓ ⋆< w >)
              → Γ ⊢₅ τ < w >
              → (convertCtx Γ) ⊢ₓ ⋆< w >
  convertExpr K t = convertExpr' {s = id} (λ {Δ}{s'} → K {_}{s'}) t

  convertValue : ∀ {Γ τ w} → Γ ⊢₅ ↓ τ < w > → (convertCtx Γ) ⊢ₓ ↓ (convertType τ) < w >
  convertValue t = convertValue' {s = id} t
