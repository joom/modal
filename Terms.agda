module Terms where

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

  open import Types

  -- Terms that have to type check by definition.
  data _⊢_<_> : Context → Type → World → Set where
    `tt : ∀ {Γ w} → Γ ⊢ `Unit < w >
    -- Boolean terms
    `true : ∀ {Γ w} → Γ ⊢ `Bool < w >
    `false : ∀ {Γ w} → Γ ⊢ `Bool < w >
    `_∧_ : ∀ {Γ w} → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w >
    `_∨_ : ∀ {Γ w} → Γ ⊢ `Bool < w > →  Γ ⊢ `Bool < w > → Γ ⊢ `Bool < w >
    `¬_ : ∀ {Γ w} → Γ ⊢ `Bool < w > →  Γ ⊢ `Bool < w >
    `if_`then_`else_ : ∀ {Γ τ w} → Γ ⊢ `Bool < w > → Γ ⊢ τ < w > → Γ ⊢ τ < w > → Γ ⊢ τ < w >
    -- ℕ terms
    `n_ : ∀ {Γ w} → ℕ → Γ ⊢ `Nat < w >
    `_≤_ : ∀ {Γ w} → Γ ⊢ `Nat < w > → Γ ⊢ `Nat < w > →  Γ ⊢ `Bool < w >
    `_+_ : ∀ {Γ w} → Γ ⊢ `Nat < w > → Γ ⊢ `Nat < w > → Γ ⊢ `Nat < w >
    `_*_ : ∀ {Γ w} → Γ ⊢ `Nat < w > →  Γ ⊢ `Nat < w > → Γ ⊢ `Nat < w >
    -- Abstraction & context terms
    `v : ∀ {Γ} → (x : Id) (w : World) (i : x ∈ Γ < w >) → Γ ⊢ lookupType x w Γ i < w >
    `_·_ : ∀ {Γ τ σ w} → Γ ⊢ (` τ ⇒ σ) < w > → Γ ⊢ τ < w > → Γ ⊢ σ < w >
    `λ_`:_⇒_ : ∀ {Γ τ w} → (x : Id) (σ : Type) → ((x , σ , w) ∷ Γ) ⊢ τ < w > → Γ ⊢ (` σ ⇒ τ) < w >
    -- Product and sum terms
    `_,_ : ∀ {Γ τ σ w} → Γ ⊢ τ < w > →  Γ ⊢ σ < w > →  Γ ⊢ (` τ × σ) < w >
    `fst : ∀ {Γ τ σ w} → Γ ⊢ (` τ × σ) < w > → Γ ⊢ τ < w >
    `snd : ∀ {Γ τ σ w} → Γ ⊢ (` τ × σ) < w > → Γ ⊢ σ < w >
    `inl_`as_ : ∀ {Γ τ w} → Γ ⊢ τ < w > → (σ : Type) → Γ ⊢ (` τ ⊎ σ) < w >
    `inr_`as_ : ∀ {Γ σ w} → Γ ⊢ σ < w > → (τ : Type) → Γ ⊢ (` τ ⊎ σ) < w >
    `case_`of_||_ : ∀ {Γ τ σ υ w} → Γ ⊢ (` τ ⊎ σ) < w > → Γ ⊢ (` τ ⇒ υ) < w > → Γ ⊢ (` σ ⇒ υ) < w > → Γ ⊢ υ < w >
    -- At terms
    `hold : ∀ {Γ τ w} → Γ ⊢ τ < w > → Γ ⊢ (` τ at w) < w >
    `leta_`=_`in_ : ∀ {Γ τ σ w w'} → (x : Id) → Γ ⊢ (` τ at w') < w > → ((x , τ , w') ∷ Γ) ⊢ σ < w > → Γ ⊢ σ < w >
    -- Box terms
    `box : ∀ {Γ τ w} → (id : Id) → Γ ⊢ τ < WVar id > → Γ ⊢ (`□ τ) < w >
    `unbox : ∀ {Γ τ w} → Γ ⊢ (`□ τ) < w > → Γ ⊢ τ < w >
    -- Diamond terms
    `here : ∀ {Γ τ w} → Γ ⊢ τ < w > → Γ ⊢ (`◇ τ) < w >
    `letd_`,_`=_`in_ : ∀ {Γ τ σ w} → (ω : Id) → (x : Id) → Γ ⊢ (`◇ τ) < w > → ((x , τ , (WVar ω)) ∷ Γ) ⊢ σ < w > → Γ ⊢ σ < w >
    -- Other
    `get : ∀ {Γ τ w w'} → τ mobile → Γ ⊢ τ < w' > → Γ ⊢ τ < w >

  Closed : Type → World → Set
  Closed τ w = [] ⊢ τ < w >

  {- Defining an abstract syntax tree.
     Unlike the terms _⊢_<_>, these can fail type checking.
  -}
  data Expr : Set where
    EUnit ETrue EFalse : Expr
    EVar : Id → World → Expr
    ENat : ℕ → Expr
    EAnd EOr EPlus ETimes ELte EApp EPair : Expr → Expr → Expr
    ENot EFst ESnd EHold EUnbox EHere : Expr → Expr
    ECond ECase : Expr → Expr → Expr → Expr
    ELam : Id → Type → Expr → Expr
    EBox : Id → Expr → Expr
    EInl EInr : Expr → Type → Expr
    ELeta : Id → Expr → Expr → Expr
    ELetd : Id → Id → Expr → Expr → Expr
    EGet : World → Expr → Expr

  -- Type erasure. Get a syntactical expr from a type checked term.
  erase : ∀ {τ Γ w} → Γ ⊢ τ < w > → Expr
  erase `tt = EUnit
  erase `true = ETrue
  erase `false = EFalse
  erase (` x ∧ y) = EAnd (erase x) (erase y)
  erase (` x ∨ y) = EOr (erase x) (erase y)
  erase (`¬ x) = ENot (erase x)
  erase (`if c `then x `else y) = ECond (erase c) (erase x) (erase y)
  erase (`n x) = ENat x
  erase (` x ≤ y) = ELte (erase x) (erase y)
  erase (` x + y) = EPlus (erase x) (erase y)
  erase (` x * y) = ETimes (erase x) (erase y)
  erase (`v id w i) = EVar id w
  erase (` f · x) = EApp (erase f) (erase x)
  erase ((`λ id `: σ ⇒ y)) = ELam id σ (erase y)
  erase (` x , y) = EPair (erase x) (erase y)
  erase (`fst p) = EFst (erase p)
  erase (`snd p) = ESnd (erase p)
  erase (`inl x `as σ) = EInl (erase x) σ
  erase (`inr x `as τ) = EInr (erase x) τ
  erase (`case x `of f || g) = ECase (erase x) (erase f) (erase g)
  erase (`hold x) = EHold (erase x)
  erase (`leta id `= x `in y) = ELeta id (erase x) (erase y)
  erase (`box ω x) = EBox ω (erase x)
  erase (`unbox x) = EUnbox (erase x)
  erase (`here x) = EHere (erase x)
  erase (`letd ω `, id `= x `in y) = ELetd ω id (erase x) (erase y)
  erase (`get {w' = w'} m x) = EGet w' (erase x)

  data Check (Γ : Context) : Expr → Set where
    well : (τ : Type) (w : World) (t : Γ ⊢ τ < w >) → Check Γ (erase t)
    ill  : {e : Expr} → Check Γ e

  check : (w : World) (Γ : Context) (e : Expr) → Check Γ e
  check w Γ EUnit = well `Unit w `tt
  check w Γ ETrue = well `Bool w `true
  check w Γ EFalse = well `Bool w `false
  check w Γ (EVar x w') with w decW w'
  check w Γ (EVar x .w) | yes refl with lookup x w Γ
  ... | yes p = well (lookupType x w Γ p) w (`v x w p)
  ... | _ = ill
  check w Γ (EVar x w') | _ = ill
  check w Γ (ENat x) = well `Nat w (`n x)
  check w Γ (EAnd x y) with check w Γ x | check w Γ y
  check w Γ (EAnd .(erase t) .(erase u)) | well `Bool w' t | well `Bool w'' u with w decW w' | w' decW w''
  check w' Γ (EAnd .(erase t) .(erase u)) | well `Bool .w' t | well `Bool .w' u | yes refl | yes refl = well `Bool w' (` t ∧ u)
  ... | _ | _ = ill
  check w Γ (EAnd _ _) | _ | _ = ill
  check w Γ (EOr x y) with check w Γ x | check w Γ y
  check w Γ (EOr .(erase t) .(erase u)) | well `Bool w' t | well `Bool w'' u with w decW w' | w' decW w''
  check w' Γ (EOr .(erase t) .(erase u)) | well `Bool .w' t | well `Bool .w' u | yes refl | yes refl = well `Bool w' (` t ∨ u)
  ... | _ | _ = ill
  check w Γ (EOr _ _) | _ | _ = ill
  check w Γ (EPlus x y) with check w Γ x | check w Γ y
  check w Γ (EPlus .(erase t) .(erase u)) | well `Nat w' t | well `Nat w'' u with w decW w' | w' decW w''
  check w' Γ (EPlus .(erase t) .(erase u)) | well `Nat .w' t | well `Nat .w' u | yes refl | yes refl = well `Nat w' (` t + u)
  ... | _ | _ = ill
  check w Γ (EPlus _ _) | _ | _ = ill
  check w Γ (ETimes x y)  with check w Γ x | check w Γ y
  check w Γ (ETimes .(erase t) .(erase u)) | well `Nat w' t | well `Nat w'' u with w decW w' | w' decW w''
  check w' Γ (ETimes .(erase t) .(erase u)) | well `Nat .w' t | well `Nat .w' u | yes refl | yes refl = well `Nat w' (` t * u)
  ... | _ | _ = ill
  check w Γ (ETimes _ _) | _ | _ = ill
  check w Γ (ELte x y) with check w Γ x | check w Γ y
  check w Γ (ELte .(erase t) .(erase u)) | well `Nat w' t | well `Nat w'' u with w decW w' | w' decW w''
  check w' Γ (ELte .(erase t) .(erase u)) | well `Nat .w' t | well `Nat .w' u | yes refl | yes refl = well `Bool w' (` t ≤ u)
  ... | _ | _ = ill
  check w Γ (ELte _ _) | _ | _ = ill
  check w Γ (EApp f x) with check w Γ f | check w Γ x
  check w Γ (EApp .(erase t) .(erase u)) | well (` σ ⇒ τ) w' t | well σ' w'' u
    with σ dec σ' | w decW w' | w' decW w''
  check w' Γ (EApp .(erase t) .(erase u)) | well (` σ' ⇒ τ) .w' t | well .σ' .w' u | yes refl | yes refl | yes refl = well τ w' (` t · u)
  ... | _ | _ | _ = ill
  check w Γ (EApp _ _) | _ | _ = ill
  check w Γ (EPair x y) with check w Γ x | check w Γ y
  check w Γ (EPair .(erase t) .(erase u)) | well σ w' t | well τ w'' u
    with w decW w' | w' decW w''
  check w' Γ (EPair .(erase t) .(erase u)) | well σ .w' t | well τ .w' u | yes refl | yes refl = well (` σ × τ) w' (` t , u)
  ... | _ | _ = ill
  check w Γ (EPair _ _) | _ | _ = ill
  check w Γ (ENot x) with check w Γ x
  check w Γ (ENot .(erase t)) | well `Bool w' t with w decW w'
  check w' Γ (ENot .(erase t)) | well `Bool .w' t | yes refl = well `Bool w' (`¬ t)
  ... | _ = ill
  check w Γ (ENot x) | _ = ill
  check w Γ (EFst p) with check w Γ p
  check w Γ (EFst .(erase t)) | well (` τ × σ) w' t with w decW w'
  check w' Γ (EFst .(erase t)) | well (` τ × σ) .w' t | yes refl = well τ w' (`fst t)
  ... | _ = ill
  check w Γ (EFst p) | _ = ill
  check w Γ (ESnd p) with check w Γ p
  check w Γ (ESnd .(erase t)) | well (` τ × σ) w' t with w decW w'
  check w' Γ (ESnd .(erase t)) | well (` τ × σ) .w' t | yes refl = well σ w' (`snd t)
  ... | _ = ill
  check w Γ (ESnd p) | _ = ill
  check w Γ (ECond c x y) with check w Γ c | check w Γ x | check w Γ y
  check w Γ (ECond .(erase t) .(erase u) .(erase v)) | well `Bool w' t | well τ w'' u | well τ' w''' v
    with τ dec τ' | w decW w' | w' decW w'' | w'' decW w'''
  check w' Γ (ECond .(erase t) .(erase u) .(erase v)) | well `Bool .w' t | well τ' .w' u | well .τ' .w' v | yes refl | yes refl | yes refl | yes refl =
     well τ' w' (`if t `then u `else v)
  ... | _ | _ | _ | _ = ill
  check w Γ (ECond c x y) | _ | _ | _ = ill
  check w Γ (ECase x f g) with check w Γ x | check w Γ f | check w Γ g
  check w Γ (ECase .(erase t) .(erase u) .(erase v)) | well (` τ ⊎ σ) w' t | well (` τ' ⇒ υ) w'' u | well (` σ' ⇒ υ') w''' v
    with τ dec τ' | σ dec σ' | υ dec υ' | w decW w' | w' decW w'' | w'' decW w'''
  check w' Γ (ECase .(erase t) .(erase u) .(erase v)) | well (` τ' ⊎ σ') .w' t | well (` .τ' ⇒ υ') .w' u | well (` .σ' ⇒ .υ') .w' v | yes refl | yes refl | yes refl | yes refl | yes refl | yes refl = well υ' w' (`case t `of u || v)
  ... | _ | _ | _ | _ | _ | _ = ill
  check w Γ (ECase x f g) | _ | _ | _ = ill
  check w Γ (ELam id σ y) with check w ((id , σ , w) ∷ Γ) y
  check w Γ (ELam id σ .(erase t)) | well τ w' t with w decW w'
  check w Γ (ELam id σ .(erase t)) | well τ .w t | yes refl = well (` σ ⇒ τ) w (`λ id `: σ ⇒ t )
  ... | _ = ill
  check w Γ (ELam id σ y) | ill = ill
  check w Γ (EBox ω e) with check (WVar ω) Γ e
  check w Γ (EBox ω .(erase t)) | well τ w' t with w' decW (WVar ω)
  check w Γ (EBox ω .(erase t)) | well τ .(WVar ω) t | yes refl = well (`□ τ) w (`box ω t)
  ... | _ = ill
  check w Γ (EBox _ _) | ill = ill
  check w Γ (EInl e σ) with check w Γ e
  check w Γ (EInl .(erase t) σ) | well τ w' t with w decW w'
  check w' Γ (EInl .(erase t) σ) | well τ .w' t | yes refl = well (` τ ⊎ σ) w' (`inl t `as σ)
  ... | _ = ill
  check w Γ (EInl e σ) | _ = ill
  check w Γ (EInr e τ) with check w Γ e
  check w Γ (EInr .(erase t) τ) | well σ w' t with w decW w'
  check w' Γ (EInr .(erase t) τ) | well σ .w' t | yes refl = well (` τ ⊎ σ) w' (`inr t `as τ)
  ... | _ = ill
  check w Γ (EInr e τ) | _ = ill
  check w Γ (EHold x) with check w Γ x
  check w Γ (EHold .(erase t)) | well τ w' t with w decW w'
  check w' Γ (EHold .(erase t)) | well τ .w' t | yes refl = well (` τ at w') w' (`hold t)
  ... | _ = ill
  check w Γ (EHold x) | ill = ill
  check w Γ (EUnbox x) with check w Γ x
  check w Γ (EUnbox .(erase t)) | well (`□ τ) w' t with w decW w'
  check w' Γ (EUnbox .(erase t)) | well (`□ τ) .w' t | yes refl = well τ w' (`unbox t)
  ... | _ = ill
  check w Γ (EUnbox x) | _ = ill
  check w Γ (EHere x) with check w Γ x
  check w Γ (EHere .(erase t)) | well τ w' t with w decW w'
  ... | yes p = well (`◇ τ) w' (`here t)
  ... | _ = ill
  check w Γ (EHere x) | ill = ill
  check w Γ (ELeta id x y) with check w Γ x
  check w Γ (ELeta id .(erase t) y) | well (` τ at w'') w' t with check w ((id , τ , w'') ∷ Γ) y
  check w Γ (ELeta id .(erase t) .(erase u)) | well (` τ at w'') w' t | well σ w''' u with w decW w' | w decW w'''
  check w Γ (ELeta id .(erase t) .(erase u)) | well (` τ at w'') .w t | well σ .w u | yes refl | yes refl = well σ w (`leta id `= t `in u)
  ... | _ | _ = ill
  check w Γ (ELeta id .(erase t) y) | well (` τ at w'') w' t | ill = ill
  check w Γ (ELeta id x y) | _ = ill
  check w Γ (ELetd ω id x y) with check w Γ x
  check w Γ (ELetd ω id .(erase t) y) | well (`◇ τ) w' t with check w ((id , τ , WVar ω) ∷ Γ ) y
  check w Γ (ELetd ω id .(erase t) .(erase u)) | well (`◇ τ) w' t | well σ w'' u with w decW w' | w decW w''
  check w' Γ (ELetd ω id .(erase t) .(erase u)) | well (`◇ τ) .w' t | well σ .w' u | yes refl | yes refl = well σ w' (`letd ω `, id `= t `in u)
  ... | _ | _ = ill
  check w Γ (ELetd ω id .(erase t) y) | well (`◇ τ) w' t | ill = ill
  check w Γ (ELetd ω id x y) | _ = ill
  check w Γ (EGet w' e) with check w' Γ e
  check w Γ (EGet w' .(erase t)) | well τ w'' t with w' decW w'' | decM τ
  check w Γ (EGet w' .(erase t)) | well τ .w' t | yes refl | yes m = well τ w (`get m t)
  ... | _ | _ = ill
  check w Γ (EGet w' e) | ill = ill
