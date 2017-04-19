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
  import CPS.Terms
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
  compileToJS = (clientWrapper *** serverWrapper)
              ∘ (stmSource *** stmSource)
              ∘ LiftedMonomorphicToJS.entryPoint
              ∘ LiftedMonomorphize.entryPoint
              ∘ LambdaLifting.entryPoint
              ∘ CPStoClosure.convertCont
              ∘ ML5toCPS.convertExpr (λ v → CPS.Terms.`halt)

  writeToFile : FilePath → String × String → IO ⊤
  writeToFile path (cli , ser) =
    ♯ writeFile (path ++ "index.html") cli >>
    ♯ writeFile (path ++ "app.js") ser

  compile : [] ⊢₅ `Unit < client > → IO ⊤
  compile = writeToFile "" ∘ compileToJS

  program : [] ⊢₅ `Unit < client >
  -- program = `prim `alert `in (` `val (`v "alert" (here refl)) · `val (`string "hello world"))
  -- program = `prim `alert `in `val `tt
  -- program = ` `val (`λ "x" ⦂ `Unit ⇒ `val `tt) · `val `tt
  -- program = `prim `alert `in `prim `prompt `in
  --           (` `val (`v "alert" (there (here refl))) · (` `val (`v "prompt" (here refl)) · `val (`string "Write something")))
  -- program = ` `val (`λ "x" ⦂ `String ⇒ (`prim `alert `in (` `val (`v "alert" (here refl)) · `val (`v "x" (there (here refl))))))
  --              · `val (`string "hello world")
  -- program = `prim `alert `in `prim `prompt `in
  --              (` `val (`v "alert" (there (here refl))) · (` `val (`v "prompt" (here refl)) · `val (`string "Write something")))
  -- program = `prim `readFile `in `prim `alert `in (` `val (`v "alert" (here refl)) · `val (`string "hello world"))
  -- program = `prim `log `in (` `val (`vval "log" (here refl)) · `val (`string "hello there"))
  -- program = ` `val (`λ "x" ⦂ `Unit ⇒ `val `tt) · `val `tt
  -- program = `prim `alert `in (` `val (`v "alert" (here refl)) · `val (`string "hello world"))
  -- program = `prim `write `in (` `val (`v "write" (here refl)) · (`if `val `true `then `val (`string "yes") `else `val (`string "no")))
  program = `prim `version `in
            `prim `write `in
            (` `val (`v "write" (here refl))
            · `get {m = `Stringᵐ} (`val (`v "version" (there (here refl)))))

  output : String × String
  output = compileToJS program

  main = run (compile program)
