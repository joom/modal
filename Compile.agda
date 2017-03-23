module Compile where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  open import Data.Unit
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
  open import Function
  open import Data.String
  open import IO
  open import Coinduction

  open import Definitions
  open import ML5.Types renaming (Type to Type₅ ; Hyp to Hyp₅)
  open import ML5.Terms renaming (_⊢_ to _⊢₅_)
  open import CPS.Types renaming (Type to Typeₓ ; Hyp to Hypₓ)
  open import CPS.Terms renaming (_⊢_ to _⊢ₓ_)
  open import Closure.Types renaming (Type to Typeₒ ; Hyp to Hypₒ ; Context to Contextₒ)
  open import Closure.Terms renaming (_⊢_ to _⊢ₒ_)
  open import LiftedMonomorphic.Types renaming (Type to Typeᵐ ; Hyp to Hypᵐ ; Context to Contextᵐ)
  open import LiftedMonomorphic.Terms renaming (_⊢_ to _⊢ᵐ_)
  open import JS.Types renaming (Type to Typeⱼ ; Hyp to Hypⱼ)
  open import JS.Terms renaming (_⊢_ to _⊢ⱼ_)
  open import JS.Source
  open import ML5toCPS
  open import CPStoClosure
  open import LambdaLifting
  open import LiftedMonomorphize
  open import LiftedMonomorphicToJS

  FilePath = String

  compileToJS : [] ⊢₅ `Unit < client > → String × String
  compileToJS = (stmSource *** stmSource)
              ∘ LiftedMonomorphicToJS.entryPoint
              ∘ LiftedMonomorphize.entryPoint
              ∘ LambdaLifting.entryPoint
              ∘ CPStoClosure.convertCont
              ∘ ML5toCPS.convertExpr (λ v → `halt)

  writeToFile : FilePath → String × String → IO ⊤
  writeToFile path (cli , ser) =
    ♯ writeFile (path ++ "cli.js") cli >>
    ♯ writeFile (path ++ "ser.js") cli

  compile : [] ⊢₅ `Unit < client > → IO ⊤
  compile = writeToFile "program_" ∘ compileToJS

  program : [] ⊢₅ `Unit < client >
  program = `prim `alert `in (` `val (`v "alert" (here refl)) · `val (`string "hello world"))
  -- program = `prim `alert `in `val `tt

  main = run (compile program)
