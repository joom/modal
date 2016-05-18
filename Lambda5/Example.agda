module Lambda5.Example where
  open import Data.List
  open import Relation.Binary.PropositionalEquality hiding ([_])

  open import Lambda5.Types
  open import Lambda5.Terms

  w = client

  2+2 : Closed `Nat w
  2+2 = ` (`λ "x" `: `Nat ⇒ (` (`v "x" w here) + (`v "x" w here))) · `n 2

  expr+double : Expr
  expr+double = ELam "x" `Nat (EPlus (EVar "x" w) (EVar "x" w))

  term+double : Closed ( ` `Nat ⇒ `Nat) w
  term+double = `λ "x" `: `Nat ⇒ (` (`v "x" w here) + (`v "x" w here))

  check+double : check w [] expr+double ≡ well (` `Nat ⇒ `Nat) w term+double
  check+double = refl

  nat-ex : Closed (` `Nat ⇒ `□ `Nat) w
  nat-ex = `λ "x" `: `Nat ⇒ `box "ω" (`get `Natᵐ (`v "x" w here))

  nat-ex-erase-check : check w [] (erase nat-ex) ≡ well (` `Nat ⇒ `□ `Nat) w nat-ex
  nat-ex-erase-check = refl

  -- Examples from "Modal Types for Mobile Code" by Tom Murphy VII, page 19.
  ex1 : ∀ {τ} → Closed (` `□ τ ⇒ τ) w
  ex1 = `λ "x" `: _ ⇒ `unbox (`v "x" client here)

  ex2 : ∀ {τ} → Closed (` τ ⇒ `◇ τ) w
  ex2 = `λ "x" `: _ ⇒ `here (`v "x" client here)

  ex3 : ∀ {τ} → Closed (` `◇ (`◇ τ) ⇒ `◇ τ) w
  ex3 = `λ "x" `: _ ⇒ (`letd "ω" `, "y" `= `v "x" w here `in `get `◇ᵐ_ (`v "y" (WVar "ω") here))

  ex4 : ∀ {τ} → Closed (` `◇ (`□ τ) ⇒ `□ τ) w
  ex4 = `λ "x" `: _ ⇒ (`letd "ω" `, "y" `= `v "x" w here `in `get `□ᵐ_ (`v "y" (WVar "ω") here))

  ex5 : ∀ {τ} → Closed (` `□ τ ⇒ `□ (`□ τ)) w
  ex5 = `λ "x" `: _ ⇒ `box "ω" (`get `□ᵐ_ (`v "x" w here))

  ex6 : ∀ {τ} → Closed (` `◇ τ ⇒ `□ (`◇ τ)) w
  ex6 = `λ "x" `: _ ⇒ `box "ω" (`get `◇ᵐ_ (`v "x" w here))

  ex7 : ∀ {α β} → Closed (` `□ (` α ⇒ β) ⇒ (` `◇ α ⇒ `◇ β)) w
  ex7 = `λ "f" `: _ ⇒ (`λ "x" `: _ ⇒ (`letd "ω" `, "y" `= `v "x" w here `in `get `◇ᵐ_ (`here (` `unbox (`get `□ᵐ_ (`v "f" w (there (there here)))) · `v "y" (WVar "ω") here))))
