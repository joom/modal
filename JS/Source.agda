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
    termSource (` t === u) =  termSource t ++ " === " ++ termSource u
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
    termSource (`proj t key x) = termSource t ++ "[\"" ++ key ++ "\"]"
    termSource (`packΣ τ t) = termSource t
    termSource (`proj₁Σ t) = termSource t ++ "[\"fst\"]"
    termSource (`proj₂Σ t) = termSource t ++ "[\"snd\"]"
    termSource (`serialize t) = "JSON.stringify(" ++ termSource t ++ ")"
    termSource (`deserialize t) = "JSON.parse(" ++ termSource t ++ ")"

    stmSource : ∀ {Γ w} → Stm Γ < w > → String
    stmSource (`exp x) = termSource x ++ ";"

    primSource : ∀ {h} → Prim h → String
    primSource `alert = "var alert = {'type' : 'pair', 'fst' : {}, 'snd' : (function(obj) {window.alert(obj.fst.fst); obj.fst.snd.snd({'type' : 'pair', 'fst' : {'type' : 'unit'}, 'snd' : obj.snd});})};"
    primSource `write = "var write = {'type' : 'pair', 'fst' : {}, 'snd' : (function(obj) {window.document.querySelector('#result').innerHTML = obj.fst.fst; obj.fst.snd.snd({'type' : 'pair', 'fst' : {'type' : 'unit'}, 'snd' : obj.snd});})};"
    primSource `version = "var version = '0.0.1';"
    primSource `logCli = "var log = {'type' : 'pair', 'fst' : {}, 'snd' : (function(obj) {console.log(obj.fst.fst); obj.fst.snd.snd({'type' : 'pair', 'fst' : {'type' : 'unit'}, 'snd' : obj.snd});})};"
    primSource `logSer = "var log = {'type' : 'pair', 'fst' : {}, 'snd' : (function(obj) {console.log(obj.fst.fst); obj.fst.snd.snd({'type' : 'pair', 'fst' : {'type' : 'unit'}, 'snd' : obj.snd});})};"
    primSource `prompt = "var prompt = {'type' : 'pair', 'fst' : {}, 'snd' : (function(obj) {obj.fst.snd.snd({'type' : 'pair', 'fst' : window.prompt(obj.fst.fst), 'snd' : obj.fst.snd.fst});})};"
    primSource `readFile = "var readFile = {'type' : 'pair', 'fst' : {}, 'snd' : (function(obj) {obj.fst.snd.snd({'type' : 'pair', 'fst' : require('fs').readFileSync(obj.fst.fst), 'snd' : obj.fst.snd.fst});})};"
    primSource `socketCli = ""
    primSource `socketSer = ""

    fnStmSource : ∀ {Γ Γ' mσ w} → FnStm Γ ⇓ Γ' ⦂ mσ < w > → String
    fnStmSource (`comment x) = "/* " ++ x ++ " */"
    fnStmSource `nop = ""
    fnStmSource (`exp x) = termSource x ++ ";"
    fnStmSource (`var id t) = "var " ++ id ++ " = " ++ termSource t ++ ";"
    fnStmSource (s ；return x) = fnStmSource s ++ ";\nreturn " ++ termSource x ++ ";"
    fnStmSource (s₁ ； s₂) = fnStmSource s₁ ++ fnStmSource s₂
    fnStmSource (`if b `then t `else u) = "if (" ++ termSource b ++ ") {" ++ fnStmSource t ++ "\n} else {" ++ fnStmSource u ++ "\n}"
    fnStmSource (`prim x) = primSource x

  clientWrapper : String → String
  clientWrapper s = "<!doctype html>
<html>
<head>
<title>Compiled program</title>
</head>
<body>
<div id=\"result\"></div>
<script src=\"https://cdn.socket.io/socket.io-1.4.5.js\"></script>
<script>
var socket = io();
" ++ s ++ "
</script>
</html>"

  serverWrapper : String → String
  serverWrapper s = "
var port = 3000;
var app = require('express')();
var http = require('http').Server(app);
var io = require('socket.io')(http);

app.get('/', function(req, res){
  res.sendfile('index.html');
});

io.on('connection', function(socket){
  console.log('a user connected');

  socket.on('disconnect', function(){
    console.log('user disconnected');
  });

" ++ s ++ "
});

http.listen(port, function(){
  console.log('listening on *:' + port);
});"
