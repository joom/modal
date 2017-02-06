module JS.Source where

  open import Data.Bool
  open import Data.Float
  open import Data.Integer
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe hiding (All)
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Data.String
  open import Data.Nat.Show
  open import Data.List hiding ([_] ; zipWith ; _++_)
  open import Data.List.Any
  open import Data.List.All
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
    termSource {Γ} (`_·_ {argTypes}{_}{w} f args) =
        termSource f ++ "(" ++ concatStr (intersperse ", " (argsSource argTypes args)) ++ ")"
      where
        argsSource : (xs : List Type) → All (λ σ → Γ ⊢ σ < w >) xs → List String
        argsSource [] [] = []
        argsSource (x ∷ xs) (px ∷ ts) = termSource px ∷ argsSource xs ts
    termSource (`λ ids ⇒ t) =
      "(function (" ++ concatStr (intersperse ", " ids) ++ ") {\n" ++ fnStmSource t ++ "\n})"
    termSource (`obj terms) =
      "{" ++ concatStr (intersperse ", " (Data.List.map (λ {(id , _ , t) → "\"" ++ id ++ "\" : " ++ termSource t }) terms)) ++ "}"
    termSource (`proj t key x) = "(" ++ termSource t ++ ")[\"" ++ key ++ "\"]"
    termSource (`packΣ τ t) = termSource t
    termSource (`proj₁Σ t) = "(" ++ termSource t ++ ")[\"fst\"]"
    termSource (`proj₂Σ t) = "(" ++ termSource t ++ ")[\"snd\"]"

    stmSource : ∀ {Γ w} → Stm Γ < w > → String
    stmSource (`exp x) = termSource x ++ ";"

    primSource : ∀ {h} → Prim h → String
    primSource `alert = "var _alert = function(obj) {alert(obj.fst); obj.snd({\"type\" : \"unit\"});};"
    primSource `version = "var _version = \"0.0.1\";"
    primSource `log = "var _log = function(obj) {console.log(obj.fst); obj.snd({\"type\" : \"unit\"});};"
    primSource `prompt = "var _prompt = function(obj) {obj.snd(prompt(obj.fst));};"
    primSource `readFile = "var _readFile = function(obj) {require(\"fs\").readFile(obj.fst, \"utf-8\", function (err, data) {if(err) {throw err;} obj.snd(data);});}"
    primSource `socket = "var _socket = io();"
    primSource `io = "var app = require('express')();"
                  ++ "var http = require('http').Server(app);"
                  ++ "app.get('/', function(req, res) {res.sendFile(__dirname + '/index.html');});"
                  ++ "http.listen(3000, function() {console.log('listening on *:3000');});"
                  ++ "var _io = require('socket.io')(http);"

    fnStmSource : ∀ {Γ Γ' mσ w} → FnStm Γ ⇓ Γ' ⦂ mσ < w > → String
    fnStmSource `nop = ""
    fnStmSource (`exp x) = termSource x ++ ";"
    fnStmSource (`var id t) = "var " ++ id ++ " = " ++ termSource t
    fnStmSource (`assign id t x) = id ++ " = " ++ termSource t
    fnStmSource (s ；return x) = fnStmSource s ++ ";\nreturn " ++ termSource x ++ ";"
    fnStmSource (s₁ ； s₂) = fnStmSource s₁ ++ ";\n" ++ fnStmSource s₂
    fnStmSource (`if b `then t `else u) = "if (" ++ termSource b ++ ") {" ++ fnStmSource t ++ "\n} then {" ++ fnStmSource u ++ "\n}"
    fnStmSource (`prim x) = primSource x
