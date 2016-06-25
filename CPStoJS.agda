module CPStoJS where

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

  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import JS.Types renaming (Type to Typeⱼ ; Hyp to Hypⱼ)
  open import JS.Terms renaming (_⊢_ to _⊢ⱼ_)

  convertCont : ∀ {Γ Δ w} → Γ ⊢ₓ ⋆< w > → Stm Δ < w >
  convertCont = {! !}
