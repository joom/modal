module CPS.Example where

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
  open import CPS.Types
  open import CPS.Terms

  logVersion : [] ⊢ ⋆< client >
  logVersion = `prim "version" `in
               (`prim "log" `in
               `call (`vval "log" (here refl) refl) {!`go[ ? , ? ] ?!})
