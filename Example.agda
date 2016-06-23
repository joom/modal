module Example where

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
  open import ML5.Types renaming (Type to Type₅ ; Hyp to Hyp₅)
  open import ML5.Terms renaming (_⊢_ to _⊢₅_)
  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import ML5toCPS

  logVersion : [] ⊢₅ `Unit < client >
  logVersion =
    `prim `version `in
    (`prim `log `in
    (` `val (`vval "log" (here refl))
     · `get {m = `Stringᵐ} (`val `any) (`val (`v "version" (there (here refl))))))

  logVersionCPS : [] ⊢ₓ ⋆< client >
  logVersionCPS = convertExpr (λ v → `halt) logVersion
