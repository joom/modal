module JS.Types where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  import Data.String
  open import Data.Nat.Show
  open import Data.List
  open import Data.List.Any
  open import Data.List.Properties using (∷-injective)
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  data Type : Set where
    `Undefined `Bool `Number `String : Type
    `Function : List Type → Type → Type
    `Object : List (Id × Type) → Type
    `Σt[t×[_×t]cont] : Type → Type

  data Hyp : Set where
    _⦂_<_> : (x : Id) (τ : Type) (w : World) → Hyp -- Value

  data Conc : Set where
    _<_> : (τ : Type) (w : World) → Conc -- Expression

  Context = List Hyp

  inj≡fn : ∀ {σs τs σ τ} → `Function σs σ ≡ `Function τs τ → σs ≡ τs × σ ≡ τ
  inj≡fn refl = refl , refl
  inj≡obj : ∀ {σs τs} → `Object σs ≡ `Object τs → σs ≡ τs
  inj≡obj refl = refl
  inj≡Σ : ∀ {σ τ} → `Σt[t×[_×t]cont] σ ≡ `Σt[t×[_×t]cont] τ → σ ≡ τ
  inj≡Σ refl = refl
  inj≡⦂ : ∀ {x x' τ τ' w w'} → x ⦂ τ < w > ≡ x' ⦂ τ' < w' > → (x ≡ x') × (τ ≡ τ') × (w ≡ w')
  inj≡⦂ refl = refl , refl , refl
  inj≡, : ∀ {l1 l2}{A : Set l1}{B : Set l2}{x a : A}{y b : B} → (x , y) ≡ (a , b) → x ≡ a × y ≡ b
  inj≡, refl = refl , refl

  mutual
    _dec_ : (τ σ : Type) → Dec (τ ≡ σ)
    `Undefined dec `Undefined = yes refl
    `Bool dec `Bool = yes refl
    `Number dec `Number = yes refl
    `String dec `String = yes refl
    `Function τs σ dec `Function τ's σ' with typesDec τs τ's | σ dec σ'
    `Function τs σ dec `Function .τs .σ | yes refl | yes refl = yes refl
    ... | no p | _ = no (p ∘ proj₁ ∘ inj≡fn)
    ... | _ | no q = no (q ∘ proj₂ ∘ inj≡fn)
    `Object fs dec `Object gs with fieldsDec fs gs
    ... | yes p = yes (cong `Object p)
    ... | no q = no (q ∘ inj≡obj)
    `Σt[t×[ x ×t]cont] dec `Σt[t×[ y ×t]cont] with x dec y
    ... | yes p = yes (cong `Σt[t×[_×t]cont] p)
    ... | no q = no (q ∘ inj≡Σ)
    `Undefined dec `Bool = no (λ ())
    `Undefined dec `Number = no (λ ())
    `Undefined dec `String = no (λ ())
    `Undefined dec `Function _ _ = no (λ ())
    `Undefined dec `Object _ = no (λ ())
    `Undefined dec `Σt[t×[ _ ×t]cont] = no (λ ())
    `Bool dec `Undefined = no (λ ())
    `Bool dec `Number = no (λ ())
    `Bool dec `String = no (λ ())
    `Bool dec `Function _ _ = no (λ ())
    `Bool dec `Object _ = no (λ ())
    `Bool dec `Σt[t×[ _ ×t]cont] = no (λ ())
    `Number dec `Undefined = no (λ ())
    `Number dec `Bool = no (λ ())
    `Number dec `String = no (λ ())
    `Number dec `Function _ _ = no (λ ())
    `Number dec `Object _ = no (λ ())
    `Number dec `Σt[t×[ _ ×t]cont] = no (λ ())
    `String dec `Undefined = no (λ ())
    `String dec `Bool = no (λ ())
    `String dec `Number = no (λ ())
    `String dec `Function _ _ = no (λ ())
    `String dec `Object _ = no (λ ())
    `String dec `Σt[t×[ _ ×t]cont] = no (λ ())
    `Function _ _ dec `Undefined = no (λ ())
    `Function _ _ dec `Bool = no (λ ())
    `Function _ _ dec `Number = no (λ ())
    `Function _ _ dec `String = no (λ ())
    `Function _ _ dec `Object _ = no (λ ())
    `Function _ _ dec `Σt[t×[ _ ×t]cont] = no (λ ())
    `Object _ dec `Undefined = no (λ ())
    `Object _ dec `Bool = no (λ ())
    `Object _ dec `Number = no (λ ())
    `Object _ dec `String = no (λ ())
    `Object _ dec `Function _ _ = no (λ ())
    `Object _ dec `Σt[t×[ _ ×t]cont] = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `Undefined = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `Bool = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `Number = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `String = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `Function _ _ = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `Object _ = no (λ ())

    -- Monomorphic instance of Definitions.listDec
    -- Included here to make it obvious to Agda that it terminates.
    -- We could just say `typesDec = Definitions.listDec _decHyp_`
    typesDec : (τs σs : List Type) → Dec (τs ≡ σs)
    typesDec [] [] = yes refl
    typesDec [] (_ ∷ _) = no (λ ())
    typesDec (_ ∷ _) [] = no (λ ())
    typesDec (x ∷ xs) (y ∷ ys) with typesDec xs ys
    ... | no p = no (p ∘ proj₂ ∘ ∷-injective)
    ... | yes p with x dec y
    typesDec (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
    ... | no q = no (q ∘ proj₁ ∘ ∷-injective)

    fieldsDec : (fs gs : List (Id × Type)) → Dec (fs ≡ gs)
    fieldsDec [] [] = yes refl
    fieldsDec [] (_ ∷ _) = no (λ ())
    fieldsDec (_ ∷ _) [] = no (λ ())
    fieldsDec ((x , τ) ∷ xs) ((y , σ) ∷ ys) with x Data.String.≟ y | τ dec σ | fieldsDec xs ys
    fieldsDec ((x , τ) ∷ xs) ((.x , .τ) ∷ .xs) | yes refl | yes refl | yes refl = yes refl
    ... | no p | _ | _ = no (p ∘ proj₁ ∘ inj≡, ∘ proj₁ ∘ ∷-injective)
    ... | _ | no q | _ = no (q ∘ proj₂ ∘ inj≡, ∘ proj₁ ∘ ∷-injective)
    ... | _ | _ | no r = no (r ∘ proj₂ ∘ ∷-injective)

  _decHyp_ : (x y : Hyp) → Dec (x ≡ y)
  (x ⦂ τ < w >) decHyp (y ⦂ σ < w' >) with x Data.String.≟ y | τ dec σ | w decW w'
  ... | yes p | yes q | yes r = yes (cong₃ _⦂_<_> p q r)
  ... | no  p | _     | _     = no (p ∘ proj₁ ∘ inj≡⦂)
  ... | _     | no  q | _     = no (q ∘ (proj₁ ∘ proj₂) ∘ inj≡⦂)
  ... | _     | _     | no  r = no (r ∘ (proj₂ ∘ proj₂) ∘ inj≡⦂)

  reconcileCtxs : (Γ' Γ'' : Context) → Context
  reconcileCtxs [] ys = ys
  reconcileCtxs xs [] = xs
  reconcileCtxs (x ∷ xs) (y ∷ ys) with x decHyp y
  ... | no q = x ∷ y ∷ reconcileCtxs xs ys
  reconcileCtxs (x ∷ xs) (.x ∷ ys) | yes refl = x ∷ reconcileCtxs xs ys
