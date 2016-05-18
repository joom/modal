module Types where

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
  open import Data.List hiding ([_])
  open import Data.Empty
  open import Function

  Id : Set
  Id = Data.String.String

  data World : Set where
    client : World
    server : World
    WVar : Id → World

  inj-WVar : ∀ {w w'} → (WVar w) ≡ (WVar w') → w ≡ w'
  inj-WVar refl = refl

  _decW_ : (w : World) → (w' : World) → Dec (w ≡ w')
  client decW client = yes refl
  server decW server = yes refl
  client decW server = no (λ ())
  server decW client = no (λ ())
  (WVar _) decW server = no (λ ())
  (WVar _) decW client = no (λ ())
  server decW (WVar _) = no (λ ())
  client decW (WVar _) = no (λ ())
  (WVar id) decW (WVar id') with Data.String._≟_ id id'
  ... | yes p = yes (cong WVar p)
  ... | no q = no (q ∘ inj-WVar)

  data Type : Set where
    `Nat `Bool `Unit : Type
    `_⇒_ `_×_ `_⊎_ : Type → Type → Type
    `□ `◇ : Type → Type -- Modal logic connectives
    `_at_ : Type → World → Type

  Context : Set
  Context = List (Id × Type × World)

  data _∈_<_> : Id → Context → World → Set where
    here  : ∀ {x τ w Γ} → x ∈ ((x , τ , w) ∷ Γ) < w >
    there : ∀ {x y τ w w' Γ} → x ∈ Γ < w > → x ∈ ((y , τ , w') ∷ Γ) < w >

  lookupType : (x : Id) (w : World) (Γ : Context)  → x ∈ Γ < w > → Type
  lookupType x _ [] ()
  lookupType x _ ((_ , τ , _) ∷ Γ) here = τ
  lookupType x w (_ ∷ Γ) (there pf) = lookupType x w Γ pf

  skipOne : ∀ {Γ x y τ w w'} → ((x ≢ y) ⊎ (w ≢ w')) → x ∈ ((y , τ , w') ∷ Γ) < w > → x ∈ Γ < w >
  skipOne (inj₁ xneq) here = ⊥-elim (xneq refl)
  skipOne (inj₂ wneq) here = ⊥-elim (wneq refl)
  skipOne neq (there i) = i

  lookup : (x : Id) (w : World) (Γ : Context)  → Dec (x ∈ Γ < w >)
  lookup x w [] = no (λ ())
  lookup x w ((y , τ , w') ∷ Γ) with x Data.String.≟ y | w decW w'
  lookup x w ((.x , τ , .w) ∷ Γ) | yes refl | yes refl = yes here
  lookup x w ((y , τ , w') ∷ Γ) | yes p | no q with lookup x w Γ
  ... | yes a = yes (there a)
  ... | no b = no (λ wi → b (skipOne (inj₂ q) wi))
  lookup x w ((y , τ , w') ∷ Γ) | no p | _ with lookup x w Γ
  ... | yes a = yes (there a)
  ... | no b = no (λ xi → b (skipOne (inj₁ p) xi))

  data _mobile : Type → Set where
    `Boolᵐ : `Bool mobile
    `Natᵐ : `Nat mobile
    `Unitᵐ : `Unit mobile
    `_atᵐ_ : ∀ {A w} → (` A at w) mobile
    `□ᵐ_ : ∀ {A} → (`□ A) mobile
    `◇ᵐ_ : ∀ {A} → (`◇ A) mobile
    `_×ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A × B) mobile
    `_⊎ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A ⊎ B) mobile

  -- Injectivity of constructors
  inj≡⇒ : ∀ {σ σ′ τ τ′} → ` σ ⇒ τ ≡ ` σ′ ⇒ τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡⇒ refl = refl , refl
  inj≡× : ∀ {σ σ′ τ τ′} → ` σ × τ ≡ ` σ′ × τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡× refl = refl , refl
  inj≡⊎ : ∀ {σ σ′ τ τ′} → ` σ ⊎ τ ≡ ` σ′ ⊎ τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡⊎ refl = refl , refl
  inj≡at : ∀ {σ σ' w w'} → ` σ at w ≡ ` σ' at w' → (σ ≡ σ') × (w ≡ w')
  inj≡at refl = refl , refl

  inj≡□ : ∀ {σ τ} → `□ σ ≡ `□ τ → σ ≡ τ
  inj≡□ refl = refl
  inj≡◇ : ∀ {σ τ} → `◇ σ ≡ `◇ τ → σ ≡ τ
  inj≡◇ refl = refl

  inj×ᵐ : ∀ {τ σ} → (` τ × σ) mobile → τ mobile × σ mobile
  inj×ᵐ (` x ×ᵐ y) = x , y
  inj⊎ᵐ : ∀ {τ σ} → (` τ ⊎ σ) mobile → τ mobile × σ mobile
  inj⊎ᵐ (` x ⊎ᵐ y) = x , y

  decM : (τ : Type) → Dec (τ mobile)
  decM `Nat = yes `Natᵐ
  decM `Bool = yes `Boolᵐ
  decM `Unit = yes `Unitᵐ
  decM (` τ ⇒ σ) = no (λ ())
  decM (` τ × σ) with decM τ | decM σ
  decM (` τ × σ) | yes p | yes q = yes (` p ×ᵐ q)
  decM (` τ × σ) | _ | no p = no (p ∘ proj₂ ∘ inj×ᵐ)
  decM (` τ × σ) | no p | _ = no (p ∘ proj₁ ∘ inj×ᵐ)
  decM (` τ ⊎ σ) with decM τ | decM σ
  decM (` τ ⊎ σ) | yes p | yes q = yes (` p ⊎ᵐ q)
  decM (` τ ⊎ σ) | _ | no p = no (p ∘ proj₂ ∘ inj⊎ᵐ)
  decM (` τ ⊎ σ) | no p | _ = no (p ∘ proj₁ ∘ inj⊎ᵐ)
  decM (`□ τ) = yes `□ᵐ_
  decM (`◇ τ) = yes `◇ᵐ_
  decM (` τ at w) = yes `_atᵐ_

  mutual
    binRelDec : (x y x' y' : Type) → (R : Type → Type → Type)
              → (∀ {σ σ′ τ τ′} → R σ τ ≡ R σ′ τ′ → (σ ≡ σ′) × (τ ≡ τ′))
              → Dec ((R x y) ≡ (R x' y'))
    binRelDec x y x' y' R inj≡R with x dec x' | y dec y'
    binRelDec x y .x .y R inj≡R | yes refl | yes refl = yes refl
    binRelDec x y x' y' R inj≡R | no ¬p | _ = no (¬p ∘ proj₁ ∘ inj≡R)
    binRelDec x y x' y' R inj≡R | _ | no ¬q = no (¬q ∘ proj₂ ∘ inj≡R)

    unRelDec : (x y : Type) → (R : Type → Type)
             → (∀ {σ τ} → R σ ≡ R τ → σ ≡ τ)
             → Dec (R x ≡ R y)
    unRelDec x y R inj≡R with x dec y
    ... | yes p = yes (cong R p)
    ... | no q = no (q ∘ inj≡R)

    _dec_ : (τ σ : Type) → Dec (τ ≡ σ)
    `Nat dec `Nat = yes refl
    `Nat dec `Bool = no (λ ())
    `Nat dec `Unit = no (λ ())
    `Nat dec (` _ ⇒ _) = no (λ ())
    `Nat dec (` _ × _) = no (λ ())
    `Nat dec (` _ ⊎ _) = no (λ ())
    `Nat dec `□ _ = no (λ ())
    `Nat dec `◇ _ = no (λ ())
    `Nat dec (` _ at _) = no (λ ())
    `Bool dec `Nat =  no (λ ())
    `Bool dec `Bool = yes refl
    `Bool dec `Unit = no (λ ())
    `Bool dec (` _ ⇒ _) = no (λ ())
    `Bool dec (` _ × _) = no (λ ())
    `Bool dec (` _ ⊎ _) = no (λ ())
    `Bool dec `□ _ = no (λ ())
    `Bool dec `◇ _ = no (λ ())
    `Bool dec (` _ at _) = no (λ ())
    `Unit dec `Nat = no (λ ())
    `Unit dec `Bool = no (λ ())
    `Unit dec `Unit = yes refl
    `Unit dec (` _ ⇒ _) = no (λ ())
    `Unit dec (` _ × _) = no (λ ())
    `Unit dec (` _ ⊎ _) = no (λ ())
    `Unit dec `□ _ = no (λ ())
    `Unit dec `◇ _ = no (λ ())
    `Unit dec (` _ at _) = no (λ ())
    (` _ ⇒ _) dec `Nat = no (λ ())
    (` _ ⇒ _) dec `Bool = no (λ ())
    (` _ ⇒ _) dec `Unit = no (λ ())
    (` σ ⇒ τ) dec (` σ' ⇒ τ') = binRelDec σ τ σ' τ' `_⇒_ inj≡⇒
    (` _ ⇒ _) dec (` _ × _) = no (λ ())
    (` _ ⇒ _) dec (` _ ⊎ _) = no (λ ())
    (` _ ⇒ _) dec `□ _ = no (λ ())
    (` _ ⇒ _) dec `◇ _ = no (λ ())
    (` _ ⇒ _) dec (` _ at _) = no (λ ())
    (` _ × _) dec `Nat = no (λ ())
    (` _ × _) dec `Bool = no (λ ())
    (` _ × _) dec `Unit = no (λ ())
    (` _ × _) dec (` _ ⇒ _) = no (λ ())
    (` σ × τ) dec (` σ' × τ') = binRelDec σ τ σ' τ' `_×_ inj≡×
    (` _ × _) dec (` _ ⊎ _) = no (λ ())
    (` _ × _) dec `□ _ = no (λ ())
    (` _ × _) dec `◇ _ = no (λ ())
    (` _ × _) dec (` _ at _) = no (λ ())
    (` _ ⊎ _) dec `Nat = no (λ ())
    (` _ ⊎ _) dec `Bool = no (λ ())
    (` _ ⊎ _) dec `Unit = no (λ ())
    (` _ ⊎ _) dec (` _ ⇒ _) = no (λ ())
    (` _ ⊎ _) dec (` _ × _) = no (λ ())
    (` σ ⊎ τ) dec (` σ' ⊎ τ') = binRelDec σ τ σ' τ' `_⊎_ inj≡⊎
    (` _ ⊎ _) dec `□ _ = no (λ ())
    (` _ ⊎ _) dec `◇ _ = no (λ ())
    (` _ ⊎ _) dec (` _ at _) = no (λ ())
    `□ _ dec `Nat = no (λ ())
    `□ _ dec `Bool = no (λ ())
    `□ _ dec `Unit = no (λ ())
    `□ _ dec (` _ ⇒ _) = no (λ ())
    `□ _ dec (` _ × _) = no (λ ())
    `□ _ dec (` _ ⊎ _) = no (λ ())
    `□ σ dec `□ τ = unRelDec σ τ `□ inj≡□
    `□ _ dec `◇ _ = no (λ ())
    `□ _ dec (` _ at _) = no (λ ())
    `◇ _ dec `Nat = no (λ ())
    `◇ _ dec `Bool = no (λ ())
    `◇ _ dec `Unit = no (λ ())
    `◇ _ dec (` _ ⇒ _) = no (λ ())
    `◇ _ dec (` _ × _) = no (λ ())
    `◇ _ dec (` _ ⊎ _) = no (λ ())
    `◇ _ dec `□ _ = no (λ ())
    `◇ σ dec `◇ τ = unRelDec σ τ `◇ inj≡◇
    `◇ _ dec (` _ at _) = no (λ ())
    (` _ at _) dec `Nat = no (λ ())
    (` _ at _) dec `Bool = no (λ ())
    (` _ at _) dec `Unit = no (λ ())
    (` _ at _) dec (` _ ⇒ _) = no (λ ())
    (` _ at _) dec (` _ × _) = no (λ ())
    (` _ at _) dec (` _ ⊎ _) = no (λ ())
    (` _ at _) dec `□ _ = no (λ ())
    (` _ at _) dec `◇ _ = no (λ ())
    (` x at w) dec (` y at w') with x dec y | w decW w'
    (` x at w) dec (` .x at .w) | yes refl | yes refl = yes refl
    ... | _ | no q = no (q ∘ proj₂ ∘ inj≡at)
    ... | no p | _ = no (p ∘ proj₁ ∘ inj≡at)
