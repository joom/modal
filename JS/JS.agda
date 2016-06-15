module JS.JS where

module SimplyJS-TypedLambdaCalculus where

  open import Data.Bool
  open import Data.Float
  open import Data.Integer
  open import Data.Nat hiding (erase)
  open import Data.String
  import Data.Unit
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  import Data.String
  open import Data.Nat.Show
  open import Data.List hiding ([_]) renaming (_++_ to _·_)
  open import Data.Empty
  open import Function

  Id : Set
  Id = String

  mutual
    data JS-Expr : Set where
      JSBool : Bool → JS-Expr
      JSNumber : (ℤ ⊎ Float) → JS-Expr
      JSString : String → JS-Expr
      JSVar : Id → JS-Expr
      JSAbst : List Id → JS-Stm → JS-Expr
      JSApp : List JS-Expr → JS-Expr → JS-Expr

    data JS-Stm : Set where
      JSExpStm : JS-Expr → JS-Stm

  data JS-Program : Set where
    JS-Prog : List JS-Stm → JS-Program

  mutual
    renderStm : JS-Stm → String
    renderStm (JSExpStm x) = render x ++ ";"

    render : JS-Expr → String
    render (JSBool true) = "true"
    render (JSBool false) = "false"
    render (JSNumber (inj₁ x)) = Data.Integer.show x
    render (JSNumber (inj₂ x)) = Data.Float.show x
    render (JSString x) = "\"" ++ x ++ "\""
    render (JSVar x) = x
    render (JSAbst x stm) = "(function (" ++ x ++ ") {return "  ++ renderStm stm ++ ";})"
    render (JSApp expr1 expr2) = render expr1 ++ "(" ++ render expr2 ++ ")"

  renderProg : JS-Program → String
  renderProg (JS-Prog l) = unlines (Data.List.map renderStm l)
