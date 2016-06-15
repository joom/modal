module CPS.Types where

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
  open import Data.List.Any
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  _decW_ : (w : World) → (w' : World) → Dec (w ≡ w')
  client decW client = yes refl
  server decW server = yes refl
  client decW server = no (λ ())
  server decW client = no (λ ())

  data Type : Set where
    `Nat `Bool `Unit `String : Type
    `_cont : Type → Type
    `_×_ `_⊎_ : Type → Type → Type
    `_at_ : Type → World → Type
    `_addr : World → Type
    `⌘ : (World → Type) → Type -- Shamrock
    `∀ `∃ : (World → Type) → Type

  data Hyp : Set where
    _⦂_<_> : (x : Id) (τ : Type) (w : World) → Hyp -- Value
    _∼_ : (u : Id) → (World → Type) → Hyp -- Valid

  data Conc : Set where
    ⋆<_> : (w : World) → Conc -- Well-formed continuation
    ↓_<_> : (τ : Type) (w : World) → Conc -- Value

  Context = List Hyp

  data _mobile : Type → Set where
    `Boolᵐ : `Bool mobile
    `Natᵐ : `Nat mobile
    `Unitᵐ : `Unit mobile
    `Stringᵐ : `String mobile
    `_atᵐ_ : ∀ {A w} → (` A at w) mobile
    `_×ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A × B) mobile
    `_⊎ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A ⊎ B) mobile
    `∀ᵐ : ∀ {A} → A mobile → (`∀ (λ _ → A)) mobile
    `∃ᵐ : ∀ {A} → A mobile → (`∃ (λ _ → A)) mobile
    `⌘ᵐ : ∀ {A} → (`⌘ (λ _ → A)) mobile
    _addrᵐ : ∀ {w} → (` w addr) mobile

  -- Injectivity of constructors
  inj≡× : ∀ {σ σ′ τ τ′} → ` σ × τ ≡ ` σ′ × τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡× refl = refl , refl
  inj≡⊎ : ∀ {σ σ′ τ τ′} → ` σ ⊎ τ ≡ ` σ′ ⊎ τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡⊎ refl = refl , refl
  inj≡at : ∀ {σ σ' w w'} → ` σ at w ≡ ` σ' at w' → (σ ≡ σ') × (w ≡ w')
  inj≡at refl = refl , refl

  inj≡cont : ∀ {σ τ} → ` σ cont ≡ ` τ cont → σ ≡ τ
  inj≡cont refl = refl
  inj≡⌘ : ∀ {C D} → `⌘ C ≡ `⌘ D → C ≡ D
  inj≡⌘ refl = refl
  inj≡∀ : ∀ {C D} → `∀ C ≡ `∀ D → C ≡ D
  inj≡∀ refl = refl
  inj≡∃ : ∀ {C D} → `∃ C ≡ `∃ D → C ≡ D
  inj≡∃ refl = refl
  inj≡addr : ∀ {w w'} → ` w addr ≡ ` w' addr → w ≡ w'
  inj≡addr refl = refl

  inj×ᵐ : ∀ {τ σ} → (` τ × σ) mobile → τ mobile × σ mobile
  inj×ᵐ (` x ×ᵐ y) = x , y
  inj⊎ᵐ : ∀ {τ σ} → (` τ ⊎ σ) mobile → τ mobile × σ mobile
  inj⊎ᵐ (` x ⊎ᵐ y) = x , y


  mutual

    -- We can do this because there are a finite number of worlds in
    -- our definitions. Otherwise this would be impossible.
    _decW→T_ : (C D : World → Type) → Dec (C ≡ D)
    C decW→T D = Relation.Nullary.Decidable.map′ extensionality to pf'
      where
        pf : (w : World) → Dec (C w ≡ D w)
        pf w = (C w) dec (D w)
        to : C ≡ D → ((w : World) → C w ≡ D w)
        to eq w = cong (λ f → f w) eq
        pf' : Dec ((w : World) → C w ≡ D w)
        pf' with pf client | pf server
        ... | yes p | yes q = yes (λ {client → p ; server → q})
        ... | no p | _ = no (λ pf → p (pf client))
        ... | _ | no q = no (λ pf → q (pf server))

    binRelDec : (x y x' y' : Type) → (R : Type → Type → Type)
              → (∀ {σ σ′ τ τ′} → R σ τ ≡ R σ′ τ′ → (σ ≡ σ′) × (τ ≡ τ′))
              → Dec ((R x y) ≡ (R x' y'))
    binRelDec x y x' y' R inj≡R with x dec x' | y dec y'
    binRelDec x y .x .y R inj≡R | yes refl | yes refl = yes refl
    binRelDec x y x' y' R inj≡R | no ¬p | _ = no (¬p ∘ proj₁ ∘ inj≡R)
    binRelDec x y x' y' R inj≡R | _ | no ¬q = no (¬q ∘ proj₂ ∘ inj≡R)

    unFnDec : (C D : World → Type) → (R : (World → Type) → Type)
            → (∀ {A B} → R A ≡ R B → A ≡ B)
            → Dec (R C ≡ R D)
    unFnDec C D R inj≡R with C decW→T D
    ... | yes p = yes (cong R p)
    ... | no q = no (q ∘ inj≡R)

    unRelDec : (x y : Type) → (R : Type → Type)
             → (∀ {σ τ} → R σ ≡ R τ → σ ≡ τ)
             → Dec (R x ≡ R y)
    unRelDec x y R inj≡R with x dec y
    ... | yes p = yes (cong R p)
    ... | no q = no (q ∘ inj≡R)

    _dec_ : (τ σ : Type) → Dec (τ ≡ σ)
    `Nat dec `Nat = yes refl
    `Bool dec `Bool = yes refl
    `Unit dec `Unit = yes refl
    `String dec `String = yes refl
    ` x cont dec ` y cont = unRelDec x y `_cont inj≡cont
    (` σ × τ) dec (` σ' × τ') = binRelDec σ τ σ' τ' `_×_ inj≡×
    (` σ ⊎ τ) dec (` σ' ⊎ τ') = binRelDec σ τ σ' τ' `_⊎_ inj≡⊎
    (` x at w) dec (` y at w') with x dec y | w decW w'
    (` x at w) dec (` .x at .w) | yes refl | yes refl = yes refl
    ... | _ | no q = no (q ∘ proj₂ ∘ inj≡at)
    ... | no p | _ = no (p ∘ proj₁ ∘ inj≡at)
    ` w addr dec ` w' addr with w decW w'
    ... | yes p = yes (cong `_addr p)
    ... | no q = no (q ∘ inj≡addr)
    `⌘ C dec `⌘ D = unFnDec C D `⌘ inj≡⌘
    `∀ C dec `∀ D = unFnDec C D `∀ inj≡∀
    `∃ C dec `∃ D = unFnDec C D `∃ inj≡∃
    `Nat dec `Bool = no (λ ())
    `Nat dec `Unit = no (λ ())
    `Nat dec `String = no (λ ())
    `Nat dec ` _ cont = no (λ ())
    `Nat dec (` _ × _) = no (λ ())
    `Nat dec (` _ ⊎ _) = no (λ ())
    `Nat dec (` _ at _) = no (λ ())
    `Nat dec ` _ addr = no (λ ())
    `Nat dec `⌘ _ = no (λ ())
    `Nat dec `∀ _ = no (λ ())
    `Nat dec `∃ _ = no (λ ())
    `Bool dec `Nat = no (λ ())
    `Bool dec `Unit = no (λ ())
    `Bool dec `String = no (λ ())
    `Bool dec ` y cont = no (λ ())
    `Bool dec (` _ × _) = no (λ ())
    `Bool dec (` _ ⊎ _) = no (λ ())
    `Bool dec (` _ at _) = no (λ ())
    `Bool dec ` _ addr = no (λ ())
    `Bool dec `⌘ _ = no (λ ())
    `Bool dec `∀ _ = no (λ ())
    `Bool dec `∃ _ = no (λ ())
    `Unit dec `Nat = no (λ ())
    `Unit dec `Bool = no (λ ())
    `Unit dec `String = no (λ ())
    `Unit dec ` _ cont = no (λ ())
    `Unit dec (` _ × _) = no (λ ())
    `Unit dec (` _ ⊎ _) = no (λ ())
    `Unit dec (` _ at _) = no (λ ())
    `Unit dec ` _ addr = no (λ ())
    `Unit dec `⌘ _ = no (λ ())
    `Unit dec `∀ _ = no (λ ())
    `Unit dec `∃ _ = no (λ ())
    `String dec `Nat = no (λ ())
    `String dec `Bool = no (λ ())
    `String dec `Unit = no (λ ())
    `String dec ` y cont = no (λ ())
    `String dec (` _ × _) = no (λ ())
    `String dec (` _ ⊎ _) = no (λ ())
    `String dec (` _ at _) = no (λ ())
    `String dec ` _ addr = no (λ ())
    `String dec `⌘ _ = no (λ ())
    `String dec `∀ _ = no (λ ())
    `String dec `∃ _ = no (λ ())
    ` _ cont dec `Nat = no (λ ())
    ` _ cont dec `Bool = no (λ ())
    ` _ cont dec `Unit = no (λ ())
    ` _ cont dec `String = no (λ ())
    ` _ cont dec (` _ × _) = no (λ ())
    ` _ cont dec (` _ ⊎ _) = no (λ ())
    ` _ cont dec (` _ at _) = no (λ ())
    ` _ cont dec ` _ addr = no (λ ())
    ` _ cont dec `⌘ _ = no (λ ())
    ` _ cont dec `∀ _ = no (λ ())
    ` _ cont dec `∃ _ = no (λ ())
    (` _ × _) dec `Nat = no (λ ())
    (` _ × _) dec `Bool = no (λ ())
    (` _ × _) dec `Unit = no (λ ())
    (` _ × _) dec `String = no (λ ())
    (` _ × _) dec ` _ cont = no (λ ())
    (` _ × _) dec (` _ ⊎ _) = no (λ ())
    (` _ × _) dec (` _ at _) = no (λ ())
    (` _ × _) dec ` _ addr = no (λ ())
    (` _ × _) dec `⌘ _ = no (λ ())
    (` _ × _) dec `∀ _ = no (λ ())
    (` _ × _) dec `∃ _ = no (λ ())
    (` _ ⊎ _) dec `Nat = no (λ ())
    (` _ ⊎ _) dec `Bool = no (λ ())
    (` _ ⊎ _) dec `Unit = no (λ ())
    (` _ ⊎ _) dec `String = no (λ ())
    (` _ ⊎ _) dec ` _ cont = no (λ ())
    (` _ ⊎ _) dec (` _ × _) = no (λ ())
    (` _ ⊎ _) dec (` _ at _) = no (λ ())
    (` _ ⊎ _) dec ` _ addr = no (λ ())
    (` _ ⊎ _) dec `⌘ _ = no (λ ())
    (` _ ⊎ _) dec `∀ _ = no (λ ())
    (` _ ⊎ _) dec `∃ _ = no (λ ())
    (` _ at _) dec `Nat = no (λ ())
    (` _ at _) dec `Bool = no (λ ())
    (` _ at _) dec `Unit = no (λ ())
    (` _ at _) dec `String = no (λ ())
    (` _ at _) dec ` _ cont = no (λ ())
    (` _ at _) dec (` _ × _) = no (λ ())
    (` _ at _) dec (` _ ⊎ _) = no (λ ())
    (` _ at _) dec ` _ addr = no (λ ())
    (` _ at _) dec `⌘ _ = no (λ ())
    (` _ at _) dec `∀ _ = no (λ ())
    (` _ at _) dec `∃ _ = no (λ ())
    ` _ addr dec `Nat = no (λ ())
    ` _ addr dec `Bool = no (λ ())
    ` _ addr dec `Unit = no (λ ())
    ` _ addr dec `String = no (λ ())
    ` _ addr dec ` y cont = no (λ ())
    ` _ addr dec (` _ × _) = no (λ ())
    ` _ addr dec (` _ ⊎ _) = no (λ ())
    ` _ addr dec (` _ at _) = no (λ ())
    ` _ addr dec `⌘ _ = no (λ ())
    ` _ addr dec `∀ _ = no (λ ())
    ` _ addr dec `∃ _ = no (λ ())
    `⌘ _ dec `Nat = no (λ ())
    `⌘ _ dec `Bool = no (λ ())
    `⌘ _ dec `Unit = no (λ ())
    `⌘ _ dec `String = no (λ ())
    `⌘ _ dec ` _ cont = no (λ ())
    `⌘ _ dec (` _ × _) = no (λ ())
    `⌘ _ dec (` _ ⊎ _) = no (λ ())
    `⌘ _ dec (` _ at _) = no (λ ())
    `⌘ _ dec ` _ addr = no (λ ())
    `⌘ _ dec `∀ _ = no (λ ())
    `⌘ _ dec `∃ _ = no (λ ())
    `∀ _ dec `Nat = no (λ ())
    `∀ _ dec `Bool = no (λ ())
    `∀ _ dec `Unit = no (λ ())
    `∀ _ dec `String = no (λ ())
    `∀ _ dec ` y cont = no (λ ())
    `∀ _ dec (` _ × _) = no (λ ())
    `∀ _ dec (` _ ⊎ _) = no (λ ())
    `∀ _ dec (` _ at _) = no (λ ())
    `∀ _ dec ` _ addr = no (λ ())
    `∀ _ dec `⌘ _ = no (λ ())
    `∀ _ dec `∃ _ = no (λ ())
    `∃ _ dec `Nat = no (λ ())
    `∃ _ dec `Bool = no (λ ())
    `∃ _ dec `Unit = no (λ ())
    `∃ _ dec `String = no (λ ())
    `∃ _ dec ` _ cont = no (λ ())
    `∃ _ dec (` _ × _) = no (λ ())
    `∃ _ dec (` _ ⊎ _) = no (λ ())
    `∃ _ dec (` _ at _) = no (λ ())
    `∃ _ dec ` _ addr = no (λ ())
    `∃ _ dec `⌘ _ = no (λ ())
    `∃ _ dec `∀ _ = no (λ ())

  inj≡⦂ : ∀ {x x' τ τ' w w'} → x ⦂ τ < w > ≡ x' ⦂ τ' < w' > → (x ≡ x') × (τ ≡ τ') × (w ≡ w')
  inj≡⦂ refl = refl , refl , refl
  inj≡∼ : ∀ {u u' C C'} → u ∼ C ≡ u' ∼ C' → (u ≡ u') × (C ≡ C')
  inj≡∼ refl = refl , refl

  _decHyp_ : (x y : Hyp) → Dec (x ≡ y)
  (x ⦂ τ < w >) decHyp (y ⦂ σ < w' >) with x Data.String.≟ y | τ dec σ | w decW w'
  ... | yes p | yes q | yes r = yes (cong₃ _⦂_<_> p q r)
  ... | no  p | _     | _     = no (p ∘ proj₁ ∘ inj≡⦂)
  ... | _     | no  q | _     = no (q ∘ (proj₁ ∘ proj₂) ∘ inj≡⦂)
  ... | _     | _     | no  r = no (r ∘ (proj₂ ∘ proj₂) ∘ inj≡⦂)
  (u ∼ C) decHyp (v ∼ D) with u Data.String.≟ v | C decW→T D
  ... | yes p | yes q = yes (cong₂ _∼_ p q)
  ... | no  p | _     = no (p ∘ proj₁ ∘ inj≡∼)
  ... | _     | no  q = no (q ∘ proj₂ ∘ inj≡∼)
  (_ ⦂ _ < _ >) decHyp (_ ∼ _) = no (λ ())
  (_ ∼ _) decHyp (_ ⦂ _ < _ >) = no (λ ())
