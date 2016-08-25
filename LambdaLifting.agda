module LambdaLifting where

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
  open import Data.List hiding ([_]) renaming (_++_ to _+++_)
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

  toHyp : Id × Typeₒ × World → Hypₒ
  toHyp (id , τ , w) = id ⦂ τ < w >

  toCtx = Data.List.map toHyp

  -- Accumulating ℕ to generate fresh variable names.
  mutual
    liftValue : ∀ {Γ τ w}
              → ℕ
              → Γ ⊢ₒ ↓ τ < w >
              → ℕ × Σ (List (Id × Typeₒ × World))
                       (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) newbindings × (Γ +++ toCtx newbindings) ⊢ₒ ↓ τ < w >)
    -- Interesting case
    liftValue {Γ}{_}{w} n (`λ x ⦂ σ ⇒ t) with liftCont n t -- there might be nested λ's
    ... | n' , xs , Δ , t' = suc n' , ("_lam" ++ show n' , ` σ cont , w) ∷ xs , (`λ x ⦂ σ ⇒ t) ∷ Δ , `v ("_lam" ++ show n') (++ʳ Γ (here refl))
    -- Trivial cases
    liftValue n `tt = n , [] , [] , `tt
    liftValue n (`string x) = n ,  [] , [] , `string x
    liftValue n `true = n , [] , [] , `true
    liftValue n `false = n , [] , [] , `false
    liftValue {Γ} n (` t ∧ u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , (` ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t' ∧ ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftValue {Γ} n (` t ∨ u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n , xs +++ ys , ++⁺ Δ Φ , (` ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t' ∨ ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftValue n (`¬ t) with liftValue n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `¬ t'
    liftValue n (`n x) = n , [] , [] , `n x
    liftValue {Γ} n (` t ≤ u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , (` ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t' ≤ ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftValue {Γ} n (` t + u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , (` ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t' + ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftValue {Γ} n (` t * u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , (` ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t' * ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftValue n (`v x ∈) = n , [] , [] , `v x (++ˡ ∈)
    liftValue n (`vval u ∈) = n , [] , [] , `vval u (++ˡ ∈)
    liftValue {Γ} n (` t , u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , (` ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t' , ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftValue n (`inl t `as σ) with liftValue n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `inl t' `as σ
    liftValue n (`inr t `as τ) with liftValue n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `inr t' `as τ
    liftValue n (`hold t) with liftValue n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `hold t'
    liftValue {Γ} n (`sham C) with liftValue n (C client)
    ... | n' , xs , Δ , u with liftValue n' (C server)
    ... | n'' , ys , Φ , v = n'' , xs +++ ys , ++⁺ Δ Φ , `sham (λ {client → ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) u ; server → ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) v})
    liftValue {Γ} n (`Λ C) with liftValue n (C client)
    ... | n' , xs , Δ , u with liftValue n' (C server)
    ... | n'' , ys , Φ , v = n'' , xs +++ ys , ++⁺ Δ Φ , `Λ (λ {client → ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) u ; server → ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) v})
    liftValue n (`pack ω t) with liftValue n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `pack ω t'
    liftValue n (`packΣ τ t) with liftValue n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `packΣ τ t'
    liftValue n `buildEnv = n , [] , [] , `buildEnv

    -- Hint: maybe we can use this to prove complex subset holes.
    -- concat-mono {xss = Γ ∷ Δ ∷ []} {yss = Γ ∷ Δ ∷ Φ ∷ Ψ ∷ []}
    -- TODO: replace the assumption proofs later.
    -- They are non-essential for the project so I'm ignoring it for now.

    liftCont : ∀ {Γ w}
             → ℕ
             → Γ ⊢ₒ ⋆< w >
             → ℕ × Σ (List (Id × Typeₒ × World))
                      (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) newbindings × (Γ +++ toCtx newbindings) ⊢ₒ ⋆< w >)
    liftCont {Γ} n (`if t `then u `else v) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' with liftCont n'' v
    ... | n''' , zs , Ψ , v' = n''' , xs +++ ys +++ zs , ++⁺ Δ (++⁺ Φ Ψ) ,
        `if ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
        `then ⊆-cont-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ((proj₂ (≡-⊆ (append-assoc xs ys zs))) ∘ _++-mono_ {_}{_}{ys}{[]}{xs +++ ys}{zs} (++ʳ xs) (λ ()) ∘ proj₂ (≡-⊆ (append-rh-[] _))))) u'
        `else ⊆-cont-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ((proj₂ (≡-⊆ (append-assoc xs ys zs))) ∘ ++ʳ (xs +++ ys)))) v'
    liftCont {Γ} n (`letcase x , y `= t `in u `or v) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' with liftCont n'' v
    ... | n''' , zs , Ψ , v' = n''' , xs +++ ys +++ zs , ++⁺ Δ (++⁺ Φ Ψ) ,
        `letcase x , y `= ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
        `in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ((proj₂ (≡-⊆ (append-assoc xs ys zs))) ∘ _++-mono_ {_}{_}{ys}{[]}{xs +++ ys}{zs} (++ʳ xs) (λ ()) ∘ proj₂ (≡-⊆ (append-rh-[] _)))))) u'
        `or ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ((proj₂ (≡-⊆ (append-assoc xs ys zs))) ∘ ++ʳ (xs +++ ys))))) v'
    liftCont {Γ} n (`leta x `= t `in u) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , `leta x `= ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      `in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) u'
    liftCont {Γ} n (`lets u `= t `in v) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' v
    ... | n'' , ys , Φ , v' = n'' ,  xs +++ ys , ++⁺ Δ Φ , `lets u `= ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      `in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) v'
    liftCont {Γ} n (`put_`=_`in_ {m = m} u t v) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' v
    ... | n'' , ys , Φ , v' = n'' ,  xs +++ ys , ++⁺ Δ Φ , `put_`=_`in_ {m = m} u (⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t')
          (⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) v')
    liftCont {Γ} n (`let x `=fst t `in u) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , `let x `=fst ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      `in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) u'
    liftCont {Γ} n (`let x `=snd t `in u) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , `let x `=snd ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      `in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) u'
    liftCont {Γ} n (`let x `= t ⟨ w' ⟩`in u) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ , `let x `= ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      ⟨ w' ⟩`in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) u'
    liftCont {Γ} n (`let_=`unpack_`in_ x t u) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' (u client)
    ... | n'' , ys , Φ , u' with liftCont n'' (u server)
    ... | n''' , zs , Ψ , v' = n''' , xs +++ ys +++ zs , ++⁺ Δ (++⁺ Φ Ψ) ,
      `let_=`unpack_`in_ x (⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t')
      (λ {client → ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ((proj₂ (≡-⊆ (append-assoc xs ys zs))) ∘ _++-mono_ {_}{_}{ys}{[]}{xs +++ ys}{zs} (++ʳ xs) (λ ()) ∘ proj₂ (≡-⊆ (append-rh-[] _)))))) u' ;
          server → ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ((proj₂ (≡-⊆ (append-assoc xs ys zs))) ∘ ++ʳ (xs +++ ys))))) v'})
    liftCont {Γ} n (`call t u) with liftValue n t
    ... | n' , xs , Δ , t' with liftValue n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ ,
      `call (⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t')
            (⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs))) u')
    liftCont n `halt = n , [] , [] , `halt
    liftCont n (`prim x `in t) with liftCont n t
    ... | n' , xs , Δ , t' = n' , xs , Δ , `prim x `in t'
    liftCont n (`go-cc[ w' ] u) with liftValue n u
    ... | n' , xs , Δ , u' = n' , xs , Δ , (`go-cc[ w' ] u')
    liftCont {Γ} n (`let τ , x `=unpack t `in u) with liftValue n t
    ... | n' , xs , Δ , t' with liftCont n' u
    ... | n'' , ys , Φ , u' = n'' , xs +++ ys , ++⁺ Δ Φ ,
      `let τ , x `=unpack ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      `in ⊆-cont-lemma (sub-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ (++ʳ xs)))) u'
    liftCont {Γ} n (`open_`in_ {Δ} t u) with liftValue n t
    ... | n' , xs , Φ , t' with liftCont n' u
    ... | n'' , ys , Ψ , u' = n'' , xs +++ ys , ++⁺ Φ Ψ ,
      `open ⊆-term-lemma (_++-mono_ {_}{_}{Γ} id (map-mono _ ++ˡ)) t'
      `in ⊆-cont-lemma ((proj₂ (≡-⊆ (append-assoc Δ Γ _))) ∘ _++-mono_ {_}{_}{Δ +++ Γ} id (map-mono _ (++ʳ xs))) u'

  entryPoint : ∀ {Γ w}
             → Γ ⊢ₒ ⋆< w >
             → Σ (List (Id × Typeₒ × World))
                 (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) newbindings × (Γ +++ toCtx newbindings) ⊢ₒ ⋆< w >)
  entryPoint t = proj₂ (liftCont zero t)
