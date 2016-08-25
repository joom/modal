module Example where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe hiding (All)
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  import Data.String
  open import Data.Nat.Show
  open import Data.List hiding ([_]) renaming (_++_ to _+++_)
  open import Data.List.Any
  open import Data.List.All
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Data.Vec
  open import Function
  open import Data.String
  open import IO

  open import Definitions
  open import ML5.Types renaming (Type to Type₅ ; Hyp to Hyp₅)
  open import ML5.Terms renaming (_⊢_ to _⊢₅_)
  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import Closure.Types renaming (Type to Typeₒ ; Hyp to Hypₒ ; Context to Contextₒ)
  open import Closure.Terms renaming (_⊢_ to _⊢ₒ_)
  open import JS.Types renaming (Type to Typeⱼ ; Hyp to Hypⱼ)
  open import JS.Terms renaming (_⊢_ to _⊢ⱼ_)
  open import JS.Source
  open import ML5toCPS
  open import CPStoClosure
  open import LambdaLifting

  logVersion : [] ⊢₅ `Unit < client >
  logVersion =
    `prim `version `in
    `prim `log `in
    (` `val (`vval "log" (here refl))
     · `get {m = `Stringᵐ} (`val (`v "version" (there (here refl)))))

  logVersionCPS : [] ⊢ₓ ⋆< client >
  logVersionCPS = ML5toCPS.convertExpr (λ v → `halt) logVersion

  logVersionClosure : [] ⊢ₒ ⋆< client >
  logVersionClosure = CPStoClosure.convertCont logVersionCPS

  logVersionLifting : Σ (List (Id × Typeₒ × World))
                        (λ newbindings → All (λ { (_ , σ , w') → [] ⊢ₒ ↓ σ < w' > }) newbindings × ([] +++ toCtx newbindings) ⊢ₒ ⋆< client >)
  logVersionLifting = LambdaLifting.entryPoint logVersionClosure

  logJS-test : Stm [] < client >
  logJS-test =
    `exp ((` (`λ [] ⇒ (
      `prim `alert ；
      `prim `socket ；
      `exp ((` `proj (`v "socket" (here refl)) "on" (here refl)
             · ((_ , `string "version") ∷ ((_ , (`λ "v" ∷ [] ⇒ (`exp ((` `v "alert" (there (there (here refl)))
                                                                        · ((_ , `obj (("type" , _ , `string "and") ∷
                                                                                       ("fst" , _ , `v "v" (here refl)) ∷
                                                                                       ("snd" , _ , (`λ "a" ∷ [] ⇒ (`exp `undefined ；return `undefined)))
                                                                                       ∷ [])) ∷ [])) refl) ；return `undefined))) ∷ []))) refl)
    ；return `undefined
    )) · []) refl)


  logJS-test-source : String
  logJS-test-source = stmSource logJS-test

  ----------------------------------------------------------

  file : [] ⊢₅ `Unit < client >
  file =
    `prim `prompt `in
    `prim `readFile `in
    `prim `alert `in
    (` `val (`v "alert" (here refl))
     · `get {m = `Stringᵐ}  (` `val (`v "readFile" (there (here refl)))
                             · `get {m = `Stringᵐ} (` `val (`v "prompt" (there (there (here refl))))
                                                    · `val (`string "Enter file name"))))

  fileCPS : [] ⊢ₓ ⋆< client >
  fileCPS = convertExpr (λ v → `halt) file
