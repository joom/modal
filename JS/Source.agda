module JS.Source where

  open import Data.Bool
  open import Data.Float
  open import Data.Integer
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Data.String
  open import Data.Nat.Show
  open import Data.List hiding ([_] ; zipWith ; _++_)
  open import Data.List.Any
  open Membership-≡
  open import Data.Vec hiding (_∈_ ; _++_)
  open import Data.Fin
  open import Data.Empty
  open import Function

  open import JS.Types
  open import JS.Terms

  open import Definitions


  mutual
    {-# NON_TERMINATING #-}
    termSource : ∀ {Γ c} → Γ ⊢ c → String
    termSource `undefined = "undefined"
    termSource (`string s) = "\"" ++ s ++ "\""
    termSource `true = "true"
    termSource `false = "false"
    termSource (` t ∧ u) = termSource t ++ " && " ++  termSource u
    termSource (` t ∨ u) =  termSource t ++ " || " ++ termSource u
    termSource (`¬ t) = "! " ++ termSource t
    termSource (`n inj₁ x) = Data.Integer.show x
    termSource (`n inj₂ y) = Data.Float.show y
    termSource (` t ≤ u) = termSource t ++ " <= " ++ termSource u
    termSource (` t + u) = termSource t ++ " + " ++ termSource u
    termSource (` t * u) = termSource t ++ " * " ++ termSource u
    termSource (`v id ∈) = id
    termSource (`vval {w}{C} u ∈) = u
    termSource ((` f · args) x) =
      termSource f ++ "(" ++ concatStr (intersperse ", " (Data.Vec.toList (Data.Vec.map (λ {(τ , t) → termSource t}) args))) ++ ")"
    termSource (`λ ids ⇒ t) =
      "(function (" ++ concatStr (intersperse ", " (Data.Vec.toList ids)) ++ ") {\n" ++ fnStmSource t ++ "\n})"
    termSource (`obj terms) =
      "{" ++ concatStr (intersperse ", " (Data.List.map (λ {(id , _ , t) → "\"" ++ id ++ "\" : " ++ termSource t }) terms)) ++ "}"
    termSource (`proj t key x) = "(" ++ termSource t ++ ")[\"" ++ key ++ "\"]"

    stmSource : ∀ {Γ w} → Stm Γ < w > → String
    stmSource (`exp x) = termSource x ++ ";"

    -- TODO update with primitives
    primSource : ∀ {h} → Prim h → String
    primSource ()

    fnStmSource : ∀ {Γ Γ' mσ w} → FnStm Γ ⇓ Γ' ⦂ mσ < w > → String
    fnStmSource (`exp x) = termSource x ++ ";"
    fnStmSource (`var id t x) = "var " ++ id ++ " = " ++ termSource t
    fnStmSource (`assign id t x) = id ++ " = " ++ termSource t
    fnStmSource (s ；return x) = fnStmSource s ++ ";\nreturn " ++ termSource x ++ ";"
    fnStmSource (s₁ ； s₂) = fnStmSource s₁ ++ ";\n" ++ fnStmSource s₂
    fnStmSource (`prim x) = primSource x
