module Example where
  open import Data.List
  open import Relation.Binary.PropositionalEquality hiding ([_])

  open import Types
  open import Terms

  w = client

  2+2 : Closed `Nat w
  2+2 = ` (`λ "x" `: `Nat ⇒ (` (`v "x" w here) + (`v "x" w here))) · `n 2

  expr+double : Expr
  expr+double = ELam "x" `Nat (EPlus (EVar "x" w) (EVar "x" w))

  term+double : Closed ( ` `Nat ⇒ `Nat) w
  term+double = `λ "x" `: `Nat ⇒ (` (`v "x" w here) + (`v "x" w here))

  check+double : check w [] expr+double ≡ well (` `Nat ⇒ `Nat) w term+double
  check+double = refl
