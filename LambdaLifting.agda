module LambdaLifting where

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
  open import Data.List.Any.Membership using (concat-mono)
  open import Data.List.Any
  open import Data.List.Any.Properties using (++ʳ ; ++ˡ)
  open import Data.Vec
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  open import Closure.Types renaming (Type to Typeₒ ; Hyp to Hypₒ ; Conc to Concₒ ; Context to Contextₒ)
  open import Closure.Terms renaming (_⊢_ to _⊢ₒ_)

  postulate
    trustMe : ∀ {l} {A : Set l} → A

  mutual
    liftValue : ∀ {Γ τ w} → Γ ⊢ₒ ↓ τ < w > → Σ Contextₒ (λ Δ → (Γ +++ Δ) ⊢ₒ ↓ τ < w >)
    -- Interesting case
    liftValue {Γ}{_}{w} (`λ x ⦂ σ ⇒ t) with liftCont t -- there might be nested λ's
    ... | Δ , t' = (x ⦂ ` σ cont < w >) ∷ Δ , `v x (++ʳ Γ (here refl))
    -- Trivial cases
    liftValue `tt = [] , `tt
    liftValue (`string x) = [] , `string x
    liftValue `true = [] , `true
    liftValue `false = [] , `false
    liftValue {Γ} (` t ∧ u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , (` ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t' ∧ ⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftValue {Γ} (` t ∨ u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , (` ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t' ∨ ⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftValue (`¬ t) with liftValue t
    ... | Δ , t' = Δ , `¬ t'
    liftValue (`n x) = [] , `n x
    liftValue {Γ} (` t ≤ u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , (` ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t' ≤ ⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftValue {Γ} (` t + u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , (` ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t' + ⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftValue {Γ} (` t * u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , (` ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t' * ⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftValue (`v x ∈) = [] , `v x (++ˡ ∈)
    liftValue (`vval u ∈) = [] , `vval u (++ˡ ∈)
    liftValue {Γ} (` t , u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , (` ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t' , ⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftValue (`inl t `as σ) = [] , `inl ⊆-term-lemma ++ˡ t `as σ
    liftValue (`inr t `as τ) = [] , `inr ⊆-term-lemma ++ˡ  t `as τ
    liftValue (`hold t) = [] , `hold (⊆-term-lemma ++ˡ t)
    liftValue (`sham x) = [] , `sham (λ ω → ⊆-term-lemma ++ˡ (x ω))
    liftValue (`Λ x) = [] , `Λ (λ ω → ⊆-term-lemma ++ˡ (x ω))
    liftValue (`pack ω t) = [] , `pack ω (⊆-term-lemma ++ˡ t)
    liftValue `any = [] , `any
    liftValue (`packΣ τ t) = [] , `packΣ τ (⊆-term-lemma ++ˡ t)
    liftValue `buildEnv = [] , `buildEnv

    -- Hint: maybe we can use this to prove complex subset holes.
    -- concat-mono {xss = Γ ∷ Δ ∷ []} {yss = Γ ∷ Δ ∷ Φ ∷ Ψ ∷ []}
    -- TODO: replace the assumption proofs later.
    -- They are non-essential for the project so I'm ignoring it for now.

    liftCont : ∀ {Γ w} → Γ ⊢ₒ ⋆< w > → Σ Contextₒ (λ Δ → (Γ +++ Δ) ⊢ₒ ⋆< w >)
    liftCont {Γ} (`if t `then u `else v) with liftValue t | liftCont u | liftCont v
    ... | Δ , t' | Φ , u' | Ψ , v' = Δ +++ Φ +++ Ψ , (`if ⊆-term-lemma trustMe t' `then ⊆-cont-lemma trustMe u' `else ⊆-cont-lemma trustMe v')
    liftCont {Γ} (`letcase x , y `= t `in u `or v) with liftValue t | liftCont u | liftCont v
    ... | Δ , t' | Φ , u' | Ψ , v' = Δ +++ Φ +++ Ψ , (`letcase x , y `= ⊆-term-lemma trustMe t' `in ⊆-cont-lemma trustMe u' `or ⊆-cont-lemma trustMe v')
    liftCont {Γ} (`leta x `= t `in u) with liftValue t | liftCont u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , `leta x `= ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t'
                                       `in ⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) u'
    liftCont {Γ} (`lets u `= t `in v) with liftValue t | liftCont v
    ... | Δ , t' | Φ , v' = Δ +++ Φ , `lets u `= ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t'
                                       `in ⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) v'
    liftCont {Γ} (`put_`=_`in_ {m = m} u t v) with liftValue t | liftCont v
    ... | Δ , t' | Φ , v' = Δ +++ Φ , `put_`=_`in_ {m = m} u (⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t')
                                       (⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) v')
    liftCont {Γ} (`let x `=fst t `in u) with liftValue t | liftCont u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , `let x `=fst ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t'
                                       `in ⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) u'
    liftCont {Γ} (`let x `=snd t `in u) with liftValue t | liftCont u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , `let x `=snd ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t'
                                       `in ⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) u'
    liftCont {Γ} (`let x `=localhost`in t) = [] , `halt
    liftCont {Γ} (`let x `= t ⟨ w' ⟩`in u) with liftValue t | liftCont u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , `let x `= ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t'
                                       ⟨ w' ⟩`in ⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) u'
    liftCont {Γ} (`let_=`unpack_`=_`in_ x t u) with liftValue t | liftCont (u client) | liftCont (u server)
    ... | Δ , t' | Φ , u' | Ψ , v' = Δ +++ Φ +++ Ψ , `let_=`unpack_`=_`in_ x (⊆-term-lemma trustMe t')
      (λ {client → ⊆-cont-lemma (sub-lemma trustMe) u' ; server → ⊆-cont-lemma (sub-lemma trustMe) v'})
    liftCont {Γ} (`call t u) with liftValue t | liftValue u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , `call (⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t') (⊆-term-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ})) u')
    liftCont `halt = [] , `halt
    liftCont (`prim x `in t) = [] , `prim x `in ⊆-cont-lemma ++ˡ t
    liftCont (`go-cc[ w' , t ] u) with liftValue u
    ... | Δ , u' = Δ , (`go-cc[ w' , `any ] u')
    liftCont {Γ} (`let τ , x `=unpack t `in u) with liftValue t | liftCont u
    ... | Δ , t' | Φ , u' = Δ +++ Φ , `let τ , x `=unpack ⊆-term-lemma (proj₂ (≡-⊆ (append-assoc Γ Δ Φ)) ∘ ++ˡ) t'
                                       `in ⊆-cont-lemma (sub-lemma (append-lh-⊆ Γ _ _ (++ʳ (Δ) {ys = Φ}))) u'
    liftCont {Γ} (`open_`in_ {Δ} t u) = [] , `open ⊆-term-lemma ++ˡ t `in ⊆-cont-lemma (proj₂ (≡-⊆ (append-assoc Δ Γ [])) ∘ ++ˡ) u

  collect : ∀ {Γ τ w} → Γ ⊢ₒ ↓ τ < w > → List (Σ _ (λ { (σ , w') → [] ⊢ₒ ↓ σ < w' >}))
  collect t = {!!}
