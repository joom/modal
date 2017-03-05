module LiftedMonomorphic.Types where

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
  open import Data.List.Properties using (∷-injective)
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  mutual
    data Type : Set where
      `Int `Bool `Unit `String : Type
      `_cont : Type → Type
      `_×_ `_⊎_ : Type → Type → Type
      `_at_ : Type → World → Type
      `⌘ : (World → Type) → Type -- Shamrock
      `∀ `∃ : (World → Type) → Type
      `Σt[t×[_×t]cont] : Type → Type
      `Env : List Hyp → Type

    data Hyp : Set where
      _⦂_<_> : (x : Id) (τ : Type) (w : World) → Hyp -- Value

  data Conc : Set where
    ⋆<_> : (w : World) → Conc -- Well-formed continuation
    ↓_<_> : (τ : Type) (w : World) → Conc -- Value

  Context = List Hyp

  data _mobile : Type → Set where
    `Boolᵐ : `Bool mobile
    `Intᵐ : `Int mobile
    `Unitᵐ : `Unit mobile
    `Stringᵐ : `String mobile
    `_atᵐ_ : ∀ {A w} → (` A at w) mobile
    `_×ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A × B) mobile
    `_⊎ᵐ_ : ∀ {A B} → A mobile → B mobile → (` A ⊎ B) mobile
    `∀ᵐ : ∀ {A} → A mobile → (`∀ (λ _ → A)) mobile
    `∃ᵐ : ∀ {A} → A mobile → (`∃ (λ _ → A)) mobile
    `⌘ᵐ : ∀ {A} → (`⌘ (λ _ → A)) mobile

  -- Injectivity of constructors
  inj≡× : ∀ {σ σ′ τ τ′} → ` σ × τ ≡ ` σ′ × τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡× refl = refl , refl
  inj≡⊎ : ∀ {σ σ′ τ τ′} → ` σ ⊎ τ ≡ ` σ′ ⊎ τ′ → (σ ≡ σ′) × (τ ≡ τ′)
  inj≡⊎ refl = refl , refl
  inj≡at : ∀ {σ σ' w w'} → ` σ at w ≡ ` σ' at w' → (σ ≡ σ') × (w ≡ w')
  inj≡at refl = refl , refl
  inj≡Σ : ∀ {σ τ} → `Σt[t×[_×t]cont] σ ≡ `Σt[t×[_×t]cont] τ → σ ≡ τ
  inj≡Σ refl = refl
  inj≡Env : ∀ {Γ Δ} → `Env Γ ≡ `Env Δ → Γ ≡ Δ
  inj≡Env refl = refl

  inj≡cont : ∀ {σ τ} → ` σ cont ≡ ` τ cont → σ ≡ τ
  inj≡cont refl = refl
  inj≡⌘ : ∀ {C D} → `⌘ C ≡ `⌘ D → C ≡ D
  inj≡⌘ refl = refl
  inj≡∀ : ∀ {C D} → `∀ C ≡ `∀ D → C ≡ D
  inj≡∀ refl = refl
  inj≡∃ : ∀ {C D} → `∃ C ≡ `∃ D → C ≡ D
  inj≡∃ refl = refl

  inj×ᵐ : ∀ {τ σ} → (` τ × σ) mobile → τ mobile × σ mobile
  inj×ᵐ (` x ×ᵐ y) = x , y
  inj⊎ᵐ : ∀ {τ σ} → (` τ ⊎ σ) mobile → τ mobile × σ mobile
  inj⊎ᵐ (` x ⊎ᵐ y) = x , y

  inj≡⦂ : ∀ {x x' τ τ' w w'} → x ⦂ τ < w > ≡ x' ⦂ τ' < w' > → (x ≡ x') × (τ ≡ τ') × (w ≡ w')
  inj≡⦂ refl = refl , refl , refl

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
    `Int dec `Int = yes refl
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
    `⌘ C dec `⌘ D = unFnDec C D `⌘ inj≡⌘
    `∀ C dec `∀ D = unFnDec C D `∀ inj≡∀
    `∃ C dec `∃ D = unFnDec C D `∃ inj≡∃
    `Σt[t×[_×t]cont] x dec `Σt[t×[_×t]cont] y = unRelDec x y `Σt[t×[_×t]cont] inj≡Σ
    `Env Γ dec `Env Δ with contextDec Γ Δ
    `Env Γ dec `Env .Γ | yes refl = yes refl
    ... | no q = no (q ∘ inj≡Env)
    `Int dec `Bool = no (λ ())
    `Int dec `Unit = no (λ ())
    `Int dec `String = no (λ ())
    `Int dec ` _ cont = no (λ ())
    `Int dec (` _ × _) = no (λ ())
    `Int dec (` _ ⊎ _) = no (λ ())
    `Int dec (` _ at _) = no (λ ())
    `Int dec `⌘ _ = no (λ ())
    `Int dec `∀ _ = no (λ ())
    `Int dec `∃ _ = no (λ ())
    `Int dec `Σt[t×[_×t]cont] _ = no (λ ())
    `Bool dec `Int = no (λ ())
    `Bool dec `Unit = no (λ ())
    `Bool dec `String = no (λ ())
    `Bool dec ` y cont = no (λ ())
    `Bool dec (` _ × _) = no (λ ())
    `Bool dec (` _ ⊎ _) = no (λ ())
    `Bool dec (` _ at _) = no (λ ())
    `Bool dec `⌘ _ = no (λ ())
    `Bool dec `∀ _ = no (λ ())
    `Bool dec `∃ _ = no (λ ())
    `Bool dec `Σt[t×[_×t]cont] _ = no (λ ())
    `Unit dec `Int = no (λ ())
    `Unit dec `Bool = no (λ ())
    `Unit dec `String = no (λ ())
    `Unit dec ` _ cont = no (λ ())
    `Unit dec (` _ × _) = no (λ ())
    `Unit dec (` _ ⊎ _) = no (λ ())
    `Unit dec (` _ at _) = no (λ ())
    `Unit dec `⌘ _ = no (λ ())
    `Unit dec `∀ _ = no (λ ())
    `Unit dec `∃ _ = no (λ ())
    `Unit dec `Σt[t×[_×t]cont] _ = no (λ ())
    `String dec `Int = no (λ ())
    `String dec `Bool = no (λ ())
    `String dec `Unit = no (λ ())
    `String dec ` y cont = no (λ ())
    `String dec (` _ × _) = no (λ ())
    `String dec (` _ ⊎ _) = no (λ ())
    `String dec (` _ at _) = no (λ ())
    `String dec `⌘ _ = no (λ ())
    `String dec `∀ _ = no (λ ())
    `String dec `∃ _ = no (λ ())
    `String dec `Σt[t×[_×t]cont] _ = no (λ ())
    ` _ cont dec `Int = no (λ ())
    ` _ cont dec `Bool = no (λ ())
    ` _ cont dec `Unit = no (λ ())
    ` _ cont dec `String = no (λ ())
    ` _ cont dec (` _ × _) = no (λ ())
    ` _ cont dec (` _ ⊎ _) = no (λ ())
    ` _ cont dec (` _ at _) = no (λ ())
    ` _ cont dec `⌘ _ = no (λ ())
    ` _ cont dec `∀ _ = no (λ ())
    ` _ cont dec `∃ _ = no (λ ())
    ` _ cont dec `Σt[t×[_×t]cont] _ = no (λ ())
    (` _ × _) dec `Int = no (λ ())
    (` _ × _) dec `Bool = no (λ ())
    (` _ × _) dec `Unit = no (λ ())
    (` _ × _) dec `String = no (λ ())
    (` _ × _) dec ` _ cont = no (λ ())
    (` _ × _) dec (` _ ⊎ _) = no (λ ())
    (` _ × _) dec (` _ at _) = no (λ ())
    (` _ × _) dec `⌘ _ = no (λ ())
    (` _ × _) dec `∀ _ = no (λ ())
    (` _ × _) dec `∃ _ = no (λ ())
    (` _ × _) dec `Σt[t×[_×t]cont] _ = no (λ ())
    (` _ ⊎ _) dec `Int = no (λ ())
    (` _ ⊎ _) dec `Bool = no (λ ())
    (` _ ⊎ _) dec `Unit = no (λ ())
    (` _ ⊎ _) dec `String = no (λ ())
    (` _ ⊎ _) dec ` _ cont = no (λ ())
    (` _ ⊎ _) dec (` _ × _) = no (λ ())
    (` _ ⊎ _) dec (` _ at _) = no (λ ())
    (` _ ⊎ _) dec `⌘ _ = no (λ ())
    (` _ ⊎ _) dec `∀ _ = no (λ ())
    (` _ ⊎ _) dec `∃ _ = no (λ ())
    (` _ ⊎ _) dec `Σt[t×[_×t]cont] _ = no (λ ())
    (` _ at _) dec `Int = no (λ ())
    (` _ at _) dec `Bool = no (λ ())
    (` _ at _) dec `Unit = no (λ ())
    (` _ at _) dec `String = no (λ ())
    (` _ at _) dec ` _ cont = no (λ ())
    (` _ at _) dec (` _ × _) = no (λ ())
    (` _ at _) dec (` _ ⊎ _) = no (λ ())
    (` _ at _) dec `⌘ _ = no (λ ())
    (` _ at _) dec `∀ _ = no (λ ())
    (` _ at _) dec `∃ _ = no (λ ())
    (` _ at _) dec `Σt[t×[_×t]cont] _ = no (λ ())
    `⌘ _ dec `Int = no (λ ())
    `⌘ _ dec `Bool = no (λ ())
    `⌘ _ dec `Unit = no (λ ())
    `⌘ _ dec `String = no (λ ())
    `⌘ _ dec ` _ cont = no (λ ())
    `⌘ _ dec (` _ × _) = no (λ ())
    `⌘ _ dec (` _ ⊎ _) = no (λ ())
    `⌘ _ dec (` _ at _) = no (λ ())
    `⌘ _ dec `∀ _ = no (λ ())
    `⌘ _ dec `∃ _ = no (λ ())
    `⌘ _ dec `Σt[t×[_×t]cont] _ = no (λ ())
    `∀ _ dec `Int = no (λ ())
    `∀ _ dec `Bool = no (λ ())
    `∀ _ dec `Unit = no (λ ())
    `∀ _ dec `String = no (λ ())
    `∀ _ dec ` y cont = no (λ ())
    `∀ _ dec (` _ × _) = no (λ ())
    `∀ _ dec (` _ ⊎ _) = no (λ ())
    `∀ _ dec (` _ at _) = no (λ ())
    `∀ _ dec `⌘ _ = no (λ ())
    `∀ _ dec `∃ _ = no (λ ())
    `∀ _ dec `Σt[t×[_×t]cont] _ = no (λ ())
    `∃ _ dec `Int = no (λ ())
    `∃ _ dec `Bool = no (λ ())
    `∃ _ dec `Unit = no (λ ())
    `∃ _ dec `String = no (λ ())
    `∃ _ dec ` _ cont = no (λ ())
    `∃ _ dec (` _ × _) = no (λ ())
    `∃ _ dec (` _ ⊎ _) = no (λ ())
    `∃ _ dec (` _ at _) = no (λ ())
    `∃ _ dec `⌘ _ = no (λ ())
    `∃ _ dec `∀ _ = no (λ ())
    `∃ _ dec `Σt[t×[_×t]cont] _ = no (λ ())
    `Σt[t×[_×t]cont] _ dec `Int = no (λ ())
    `Σt[t×[_×t]cont] _ dec `Bool = no (λ ())
    `Σt[t×[_×t]cont] _ dec `Unit = no (λ ())
    `Σt[t×[_×t]cont] _ dec `String = no (λ ())
    `Σt[t×[_×t]cont] _ dec ` y cont = no (λ ())
    `Σt[t×[_×t]cont] _ dec (` _ × _) = no (λ ())
    `Σt[t×[_×t]cont] _ dec (` _ ⊎ _) = no (λ ())
    `Σt[t×[_×t]cont] _ dec (` _ at _) = no (λ ())
    `Σt[t×[_×t]cont] _ dec `⌘ _ = no (λ ())
    `Σt[t×[_×t]cont] _ dec `∀ _ = no (λ ())
    `Σt[t×[_×t]cont] _ dec `∃ _ = no (λ ())
    _dec_ (`Env _) `Int = no (λ ())
    _dec_ (`Env _) `Bool = no (λ ())
    _dec_ (`Env _) `Unit = no (λ ())
    _dec_ (`Env _) `String = no (λ ())
    _dec_ (`Env _) (`_cont _) = no (λ ())
    _dec_ (`Env _) (`_×_ _ _) = no (λ ())
    _dec_ (`Env _) (`_⊎_ _ _) = no (λ ())
    _dec_ (`Env _) (`_at_ _ _) = no (λ ())
    _dec_ (`Env _) (`⌘ _) = no (λ ())
    _dec_ (`Env _) (`∀ _) = no (λ ())
    _dec_ (`Env _) (`∃ _) = no (λ ())
    _dec_ (`Env _) (`Σt[t×[_×t]cont] _) = no (λ ())
    `Int dec `Env _ = no (λ ())
    `Bool dec `Env _ = no (λ ())
    `Unit dec `Env _ = no (λ ())
    `String dec `Env _ = no (λ ())
    ` _ cont dec `Env _ = no (λ ())
    (` _ × _) dec `Env _ = no (λ ())
    (` _ ⊎ _) dec `Env _ = no (λ ())
    (` _ at _) dec `Env _ = no (λ ())
    `⌘ _ dec `Env _ = no (λ ())
    `∀ _ dec `Env _ = no (λ ())
    `∃ _ dec `Env _ = no (λ ())
    `Σt[t×[ _ ×t]cont] dec `Env _ = no (λ ())

    _decHyp_ : (x y : Hyp) → Dec (x ≡ y)
    (x ⦂ τ < w >) decHyp (y ⦂ σ < w' >) with x Data.String.≟ y | τ dec σ | w decW w'
    ... | yes p | yes q | yes r = yes (cong₃ _⦂_<_> p q r)
    ... | no  p | _     | _     = no (p ∘ proj₁ ∘ inj≡⦂)
    ... | _     | no  q | _     = no (q ∘ (proj₁ ∘ proj₂) ∘ inj≡⦂)
    ... | _     | _     | no  r = no (r ∘ (proj₂ ∘ proj₂) ∘ inj≡⦂)

    -- Monomorphic instance of Definitions.listDec
    -- Included here to make it obvious to Agda that it terminates.
    -- We could just say `contextDec = Definitions.listDec _decHyp_`
    contextDec : (Γ Δ : Context) → Dec (Γ ≡ Δ)
    contextDec [] [] = yes refl
    contextDec [] (_ ∷ _) = no (λ ())
    contextDec (_ ∷ _) [] = no (λ ())
    contextDec (x ∷ xs) (y ∷ ys) with contextDec xs ys
    ... | no p = no (p ∘ proj₂ ∘ ∷-injective)
    ... | yes p with x decHyp y
    contextDec (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
    ... | no q = no (q ∘ proj₁ ∘ ∷-injective)

  toHyp : Id × Type × World → Hyp
  toHyp (id , τ , w) = id ⦂ τ < w >

  toCtx : List (Id × Type × World) → Context
  toCtx [] = []
  toCtx (h ∷ hs) = toHyp h ∷ toCtx hs

  hypWorld : Hyp → World
  hypWorld (_ ⦂ _ < w >) = w
