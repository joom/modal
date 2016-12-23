module LiftedMonomorphicToJS where

  open import Data.Bool
  open import Data.Nat hiding (erase)
  import Data.Unit
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation using (contraposition)
  open import Data.String using (_++_)
  open import Data.Nat.Show
  open import Data.List renaming (_++_ to _+++_)
  open import Data.List.Any
  import Data.List.All
  open Membership-≡ using (_∈_; _⊆_)
  open import Data.Empty
  open import Function

  open import Definitions

  open import LiftedMonomorphic.Types renaming (Type to Typeᵐ ; Hyp to Hypᵐ ; Conc to Concᵐ ; Context to Contextᵐ)
  open import LiftedMonomorphic.Terms renaming (_⊢_ to _⊢ᵐ_)
  open import JS.Types renaming (Type to Typeⱼ ; Hyp to Hypⱼ ; Conc to Concⱼ ; Context to Contextⱼ)
  open import JS.Terms renaming (_⊢_ to _⊢ⱼ_)

  isValue : Concᵐ → Set
  isValue ⋆< _ > = ⊥
  isValue ↓ _ < _ > = Data.Unit.⊤

  isCont : Concᵐ → Set
  isCont ⋆< _ > = Data.Unit.⊤
  isCont ↓ _ < _ > = ⊥

  tripleToHyp : Σ (Id × Typeᵐ × World) (λ { (id , σ , w') → [] ⊢ᵐ ↓ σ < w' >}) → Hypᵐ
  tripleToHyp ((id , σ , w) , t) = id ⦂ σ < w >

  mutual
    -- Taking advantage of that we only have two worlds here.
    hypToPair : Hypᵐ → Id × Typeⱼ
    hypToPair (x ⦂ τ < w >) = x , convertType τ

    -- because Agda thinks mapping a list doesn't terminate.
    hypsToPair : List Hypᵐ → List (Id × Typeⱼ)
    hypsToPair [] = []
    hypsToPair (x ∷ xs) with hypsToPair xs
    ... | xs' = hypToPair x ∷ xs'

    convertType : Typeᵐ → Typeⱼ
    convertType `Int = `Number
    convertType `Bool = `Bool
    convertType `Unit = `Object (("type" , `String) ∷ [])
    convertType `String = `String
    convertType ` τ cont = `Function [ convertType τ ] `Undefined
    convertType (` τ × σ) = `Object (("type" , `String) ∷ ("fst" , convertType τ ) ∷ ("snd" , convertType σ) ∷ [])
    convertType (` τ ⊎ σ) = `Object (("type" , `String) ∷ ("dir" , `String) ∷ ("inl" , convertType τ) ∷ ("inr" , convertType σ) ∷ [])
    convertType (` τ at w) = convertType τ
    convertType (`⌘ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
    convertType (`∀ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
    convertType (`∃ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
    convertType (`Σt[t×[_×t]cont] τ) =
      `Object (("type" , `String)
              ∷ ("fst" , {!!})
              ∷ ("snd" , `Function (`Object (("type" , `String)
                                            ∷ ("fst" , convertType τ )
                                            ∷ ("snd" , {!!}) ∷ []) ∷ []) `Undefined) ∷ [])
    convertType (`Env Γ) = `Object (hypsToPair Γ)

  worldForType : Typeᵐ → World → World
  worldForType (` τ at w) _ = w
  worldForType _ w = w

  convertHyp : World → Hypᵐ → Hypⱼ
  convertHyp _ (x ⦂ τ < w >) = x ⦂ convertType τ < worldForType τ w >

  convertCtx : World → Contextᵐ → Contextⱼ
  convertCtx w [] = []
  convertCtx w (h ∷ hs) with h
  ... | _ ⦂ _ < _ > = convertHyp w h ∷ convertCtx w hs


  convertPrim : ∀ {h} → LiftedMonomorphic.Terms.Prim h → List (JS.Terms.Prim {!h!}) × List (JS.Terms.Prim {!!})
  convertPrim `alert = {!!}
  convertPrim `version = {!!}
  convertPrim `log = {!!}
  convertPrim `prompt = {!!}
  convertPrim `readFile = {!!}

  -- convertPrim : ∀ {h} → LiftedMonomorphic.Terms.Prim h → JS.Terms.Prim {!h!}
  -- convertPrim `alert = {!!}
  -- convertPrim `version = {!!}
  -- convertPrim `log = {!!}
  -- convertPrim `prompt = {!!}
  -- convertPrim `readFile = {!!}

  mutual
    convertCont : ∀ {Γ Δ Φ mσ}
                → (w : World)
                → Γ ⊢ᵐ ⋆< w >
                → Σ _ (λ δ → FnStm Δ ⇓ δ ⦂ mσ < client >) × Σ _ (λ φ → FnStm Φ ⇓ φ ⦂ mσ < server >)
                -- → FnStm Δ ⇓ δ ⦂ mσ < client > × FnStm Φ ⇓ φ ⦂ mσ < server >
    convertCont {Γ}{Δ}{Φ}{mσ} client (`if t `then u `else v)
      with convertCont {Γ}{Δ}{Φ} client u | convertCont {Γ}{Δ}{Φ} client v
    ... | (δ , a) , (φ , b) | (δ' , c) , (φ' , d) =
        ({!!} , (`if {!convertValue t!} `then {!a!} `else {!c!} ))
      , (φ' +++ φ , ((b ； ⊆-fnstm-lemma {!!} d)))

    -- (`if {!convertValue t!} `then a `else c) , (b ； d)
    convertCont server (`if t `then u `else v) = {!!}
    convertCont w (`letcase x , y `= t `in t₁ `or t₂) = {!!}
    convertCont w (`leta x `= t `in u) = {!!}
    convertCont w (`lets u `= t `in v) = {!!}
    convertCont w (`put u `= t `in v) = {!!}
    convertCont w (`let x `=fst t `in u) = {!!}
    convertCont w (`let x `=snd t `in u) = {!!}
    convertCont w (`let x `= t ⟨ w' ⟩`in u) = {!!}
    convertCont w (`let_=`unpack_`in_ x t u) = {!!}
    convertCont w (`go-cc[ w' ] t₁) = {!!}
    convertCont w (`call t t₁) = {!!}
    convertCont w `halt = ([] , `nop) , ([] , `nop)
    convertCont client (`prim x `in t)
      with convertCont {_}{{!!}}{_}{_} client t
    ... | (ctxCli , fnStmCli) , ser = ({!!} , {!!}) , ser
    convertCont server (`prim x `in t) = {!!}
    convertCont w (`let τ , x `=unpack v `in t) = {!!}
    convertCont w (`open t `in u) = {!!}

    convertValue : ∀ {Γ τ w} → Γ ⊢ᵐ ↓ τ < w > → (convertCtx w Γ) ⊢ⱼ (convertType τ) < w >
    convertValue `tt = `obj (("type" , `String , `string "unit") ∷ [])
    convertValue (`string s) = `string s
    convertValue `true = `true
    convertValue `false = `false
    convertValue (` t ∧ u) = ` (convertValue t) ∧ (convertValue u)
    convertValue (` t ∨ u) = ` (convertValue t) ∨ (convertValue u)
    convertValue (`¬ t) = `¬ (convertValue t)
    convertValue (`n x) = `n inj₁ x
    convertValue (` t ≤ u) =  ` (convertValue t) ≤ (convertValue u)
    convertValue (` t + u) =  ` (convertValue t) + (convertValue u)
    convertValue (` t * u) =  ` (convertValue t) * (convertValue u)
    convertValue (`v id ∈) = `v id {!!}
    convertValue (`λ x ⦂ σ ⇒ t) = `λ x ∷ [] ⇒ {!convertCont ? ?!}
    convertValue (` t , u) = `obj (("type" , `String , `string "and") ∷
                                    ("fst" , _ , convertValue t) ∷ ("snd" , _ , convertValue u) ∷ [])
    convertValue (`inl t `as σ) = `obj (("type" , `String , `string "or") ∷
                                        ("dir" , `String , `string "inl") ∷
                                        ("inl" , _ , convertValue t) ∷ ("inr" , _ , default (convertType σ)) ∷ [])
    convertValue (`inr t `as τ) = `obj (("type" , `String , `string "or") ∷
                                        ("dir" , `String , `string "inr") ∷
                                        ("inl" , _ , default (convertType τ)) ∷ ("inr" , _ , convertValue t) ∷ [])
    convertValue (`hold t) = {!convertValue t!}
    convertValue (`sham x) = {!!}
    convertValue (`Λ x) = {!!}
    convertValue (`pack ω t) = {!!}
    convertValue (`packΣ τ t) = {!!}
    convertValue {Γ} (`buildEnv {Δ} pf) = {!!}

  convertλ : ∀ {Γ mσ} → (id : Id) (τ : Typeᵐ) (w : World) → [] ⊢ᵐ ↓ τ < w > → FnStm Γ ⇓ ((id ⦂ convertType τ < w >) ∷ []) ⦂ mσ < w >
  convertλ id τ w t = `var id (⊆-exp-lemma (λ ()) (convertValue t))

  convertλs : ∀ {mτ mσ}
            → (lifted : List (Σ (Id × Typeᵐ × World) (λ { (id , σ , w') → [] ⊢ᵐ ↓ σ < w' >})))
            → Σ _ (λ Γ → FnStm [] ⇓ Γ ⦂ mτ < client >) × Σ _ (λ Δ → FnStm [] ⇓ Δ ⦂ mσ < server >)
  convertλs [] = ([] , `nop) , ([] , `nop)
  convertλs {mτ}{mσ} (((id , σ , client) , t) ∷ xs) with convertλ {[]}{mτ} id σ client t | convertλs {mτ}{mσ} xs
  ... | fnStm | (Γ' , cliFnStm) , (Δ' , serFnStm) = (_ , (fnStm ； ⊆-fnstm-lemma (λ ()) cliFnStm)) , (_ , serFnStm)
  convertλs {mτ}{mσ} (((id , σ , server) , t) ∷ xs) with convertλ {[]}{mσ} id σ server t | convertλs {mτ}{mσ} xs
  ... | fnStm | (Γ' , cliFnStm) , (Δ' , serFnStm) = (_ , cliFnStm) , (_ , (fnStm ； ⊆-fnstm-lemma (λ ()) serFnStm))

  -- Takes a list of λ lifted list of functions and a term that runs on the client.
  -- Returns JS code for client and server.
  -- entryPoint : List (Σ (Id × Typeᵐ × World) (λ { (id , σ , w') → [] ⊢ᵐ ↓ σ < w' >})) × Σ Contextᵐ (λ Δ → Δ ⊢ᵐ ⋆< client >)
  --            → (Stm [] < client >) × (Stm [] < server >)
  -- entryPoint (xs , (Δ , t)) with convertλs {nothing}{nothing} xs
  -- ... | (Γ' , cliFnStmLifted) , (Δ' , serFnStmLifted) with convertCont {Δ}{Γ' +++ []}{Δ' +++ []}{nothing} client t
  -- ... | (δ , cliFnStm) , (φ , serFnStm) =
  --     `exp ((` `λ [] ⇒ (cliFnStmLifted ； cliFnStm ；return `undefined) · Data.List.All.[]))
  --   , `exp ((` `λ [] ⇒ (serFnStmLifted ； serFnStm ；return `undefined) · Data.List.All.[]))

  -- TODO add `prim `socket to client and `prim `io to server
  entryPoint : ∀ {w}
             → Σ (List (Id × Typeᵐ × World))
                  (λ newbindings → Data.List.All.All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) newbindings × (toCtx newbindings) ⊢ᵐ ⋆< w >)
             → (Stm [] < client >) × (Stm [] < server >)
  entryPoint (xs , all , t) = {!!}
  -- entryPoint (xs , all , t) with convertλs {nothing}{nothing} ?
  -- ... | (Γ' , cliFnStmLifted) , (Δ' , serFnStmLifted) with convertCont {?}{Γ' +++ []}{Δ' +++ []}{nothing} client t
  -- ... | (δ , cliFnStm) , (φ , serFnStm) =
  --     `exp ((` `λ [] ⇒ (cliFnStmLifted ； cliFnStm ；return `undefined) · Data.List.All.[]))
  --   , `exp ((` `λ [] ⇒ (serFnStmLifted ； serFnStm ；return `undefined) · Data.List.All.[]))
