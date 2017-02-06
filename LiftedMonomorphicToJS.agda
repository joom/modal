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
  open import Data.List.Any.Properties using (++ʳ ; ++ˡ)
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
    convertType (` τ at w) = {!!} -- todo
    convertType (`⌘ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
    convertType (`∀ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
    convertType (`∃ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType (C client))
    convertType (`Σt[t×[_×t]cont] τ) = `Σt[t×[_×t]cont] (convertType τ)
    convertType (`Env Γ) = `Object (hypsToPair Γ)

  convertHyp : Hypᵐ → Hypⱼ
  convertHyp (x ⦂ τ < w >) = x ⦂ convertType τ < w >

  convertCtx : Contextᵐ → Contextⱼ
  convertCtx [] = []
  convertCtx (h ∷ hs) = convertHyp h ∷ convertCtx hs

  convert∈ : ∀ {h Γ} → h ∈ Γ → (convertHyp h) ∈ (convertCtx Γ)
  convert∈ (here refl) = here refl
  convert∈ (there i) = there (convert∈ i)

  convertPrim : ∀ {hs} → LiftedMonomorphic.Terms.Prim hs → JS.Terms.Prim (convertCtx hs)
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `log = `log
  convertPrim `prompt = `prompt
  convertPrim `readFile = `readFile

  mutual
    convertCont : ∀ {Γ Δ Φ mτ}
                → (w : World)
                → Γ ⊢ᵐ ⋆< w >
                → Σ _ (λ δ → FnStm Δ ⇓ δ ⦂ mτ < client >) × Σ _ (λ φ → FnStm Φ ⇓ φ ⦂ mτ < server >)
    convertCont {Γ}{Δ}{Φ}{mσ} client (`if t `then u `else v) with convertValue t
    ... | t' , (tCliCtx , tCli) , (tSerCtx , tSer)
      with convertCont {Γ}{Δ}{Φ} client u | convertCont {Γ}{Δ}{Φ} client v
    ... | (δ , a) , (φ , b) | (δ' , c) , (φ' , d) =
        (δ +++ tCliCtx , (tCli ； `if {!t'!} `then ⊆-fnstm-lemma (++ʳ tCliCtx) a `else {!c!}))
      , (_ , (tSer ； ⊆-fnstm-lemma (++ʳ tSerCtx) (b ； ⊆-fnstm-lemma (++ʳ φ) d)))

    --   with convertValue t | convertCont {Γ}{Δ}{Φ} client u | convertCont {Γ}{Δ}{Φ} client v
    -- ... | t' , (tCliCtx , tCli) , (tSerCtx , tSer) | (δ , a) , (φ , b) | (δ' , c) , (φ' , d) =
    --     ({!!} , (tCli ； `if {!t'!} `then ⊆-fnstm-lemma (++ʳ tCliCtx) a `else {!c!}))
    --   , (_ , (tSer ； ⊆-fnstm-lemma (++ʳ tSerCtx) (b ； ⊆-fnstm-lemma (++ʳ φ) d)))


      --   ({!!} , (`if {!convertValue t!} `then {!a!} `else {!c!} ))
      -- , (φ' +++ φ , ((b ； ⊆-fnstm-lemma {!!} d)))
    convertCont server (`if t `then u `else v) = {!!}
    convertCont w (`letcase x , y `= t `in u `or v) = {!!}
    convertCont w (`leta x `= t `in u) = {!!}
    convertCont w (`lets u `= t `in v) = {!!}
    convertCont w (`put u `= t `in v) = {!!}
    convertCont w (`let x `=fst t `in u) with convertValue t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) with convertCont w u
    ... | (Δ'' , uCli) , (Φ'' , uSer) with w
    ... | client = (_ +++ Δ' , (tCli ； {!!})) , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    ... | server = {!!} (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , (_ +++ Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer ； {!!}))
    convertCont w (`let x `=snd t `in u) = {!!}
    convertCont w (`let x `= t ⟨ w' ⟩`in u) = {!!}
    convertCont w (`let_=`unpack_`in_ x t u) = {!!}
    convertCont client (`go-cc[ client ] t) = {!convertValue t!}
    convertCont server (`go-cc[ server ] t) = {!convertValue t!}
    convertCont client (`go-cc[ server ] t) with convertValue t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = ({!!} , {!!}) , ({!!} , {!!})
    convertCont server (`go-cc[ client ] t) = {!!}
    convertCont w (`call t u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) with w
    ... | client = ({!!} +++ Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli ； {!!})) , (_ , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    ... | server = (_ , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , ({!!} +++ Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer ； {!!}))
    convertCont w `halt = ([] , `nop) , ([] , `nop)
    convertCont w (`prim x `in t) with convertCont w t
    convertCont client (`prim x `in t) | (Δ' , tCli) , (Φ' , tSer) = ({!!} , {!!}) , (Φ' , tSer)
    convertCont server (`prim x `in t) | (Δ' , tCli) , (Φ' , tSer) = (Δ' , tCli) , ({!!} , {!!})
    convertCont w (`let τ , x `=unpack v `in t) = {!!}
    convertCont w (`open t `in u) with convertValue t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) with convertCont w u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = ({!!} , {!!}) , ({!!} , {!!})

    convertValue : ∀ {Γ Δ Φ τ w mτ} → Γ ⊢ᵐ ↓ τ < w >
                 → convertCtx Γ ⊢ⱼ (convertType τ) < w >
                   × Σ _ (λ δ → FnStm Δ ⇓ δ ⦂ mτ < client >)
                   × Σ _ (λ φ → FnStm Φ ⇓ φ ⦂ mτ < server >)
    convertValue `tt = `obj (("type" , `String , `string "unit") ∷ []) , ([] , `nop) , ([] , `nop)
    convertValue (`string s) = `string s , ([] , `nop) , ([] , `nop)
    convertValue `true = `true , ([] , `nop) , ([] , `nop)
    convertValue `false = `false , ([] , `nop) , ([] , `nop)
    convertValue (` t ∧ u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
          (` t' ∧ u') , (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    convertValue (` t ∨ u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
          (` t' ∨ u') , (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    convertValue (`¬ t) with convertValue t
    ... | (t' , tCliPair , tSerPair) = (`¬ t') , tCliPair , tSerPair
    convertValue (`n x) = `n inj₁ x , ([] , `nop) , ([] , `nop)
    convertValue (` t ≤ u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
          (` t' ≤ u') , (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    convertValue (` t + u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
          (` t' + u') , (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    convertValue (` t * u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
          (` t' * u') , (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli)) , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    convertValue (`v id ∈) = `v id (convert∈ ∈) , ([] , `nop) , ([] , `nop)
    convertValue {Γ}{Δ}{Φ}{_}{client}{mτ} (`λ x ⦂ σ ⇒ t) with convertCont {(x ⦂ σ < client >) ∷ []}{_}{_}{mτ} client t
    convertValue {w = client} (`λ x ⦂ σ ⇒ t) | (Δ' , tCli) , (Φ' , tSer) = (`λ x ∷ [] ⇒ {!tCli!}) , ([] , `nop) , (Φ' , tSer)
    convertValue {Γ}{Δ}{Φ}{_}{server}{mτ} (`λ x ⦂ σ ⇒ t) with convertCont {(x ⦂ σ < server >) ∷ []}{_}{_}{mτ} server t
    convertValue {w = server} (`λ x ⦂ σ ⇒ t) | (Δ' , tCli) , (Φ' , tSer) = (`λ x ∷ [] ⇒ {!tSer!}) , (Δ' , tCli) , ([] , `nop)
    convertValue (` t , u) with convertValue t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ'}{Φ'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
            `obj (("type" , _ , `string "and") ∷ ("fst" , _ , t') ∷ ("snd" , _ , u') ∷ [])
          , (Δ'' +++ Δ' , (tCli ； ⊆-fnstm-lemma ++ˡ uCli))
          , (Φ'' +++ Φ' , (tSer ； ⊆-fnstm-lemma ++ˡ uSer))
    convertValue (`inl t `as σ) with convertValue t
    ... | (t' , tCliPair , tSerPair) =
          `obj (("type" , `String , `string "or") ∷
                ("dir" , `String , `string "inl") ∷
                ("inl" , _ , t') ∷ ("inr" , _ , default (convertType σ)) ∷ [])
        , tCliPair , tSerPair
    convertValue (`inr t `as τ) with convertValue t
    ... | (t' , tCliPair , tSerPair) =
          `obj (("type" , `String , `string "or") ∷
                ("dir" , `String , `string "inr") ∷
                ("inl" , _ , default (convertType τ)) ∷ ("inr" , _ , t') ∷ [])
          , tCliPair , tSerPair
    convertValue (`hold {w = w} t) with convertValue t
    ... | (t' , tCliPair , tSerPair) = {!t'!} , tCliPair , tSerPair
    convertValue {w = w} (`sham C) with convertValue (C w)
    ... | (t' , tCliPair , tSerPair) = (`λ "a" ∷ [] ⇒ {!!}) , tCliPair , tSerPair
    convertValue {w = w} (`Λ C) with convertValue (C w)
    ... | (t' , tCliPair , tSerPair) = (`λ "a" ∷ [] ⇒ {!!}) , tCliPair , tSerPair
    convertValue (`pack ω t) with convertValue t
    ... | (t' , tCliPair , tSerPair) = (`λ "a" ∷ [] ⇒ {!t'!}) , tCliPair , tSerPair
    convertValue (`packΣ τ t) with convertValue t
    ... | (t' , tCliPair , tSerPair) = `packΣ (convertType τ) t' , tCliPair , tSerPair
    convertValue {Γ}{w = w} (`buildEnv {Δ} pf) = {! `obj (envList {!Δ!} {!!}) !} , ([] , `nop) , ([] , `nop)
      where
        envList : (Δ : Contextᵐ) → Δ ⊆ Γ → List (Id × Σ Typeⱼ (λ τ → convertCtx Γ ⊢ⱼ (τ < w >)))
        envList [] s = []
        envList ((x ⦂ τ < w' >) ∷ hs) s with w decW w'
        ... | yes p = (x , convertType τ , `v x (eq-replace (cong _ (sym p)) (convert∈ (s (here refl))))) ∷ envList hs (s ∘ there)
        ... | no q = (x , convertType τ , {!!}) ∷ envList hs (s ∘ there)

        -- pf' : (xs : _) (s : xs ⊆ Γ) → hypsToPair xs ≡ toTypePairs (envList xs s)
        -- pf' [] s = refl
        -- pf' ((x ⦂ τ < w' >) ∷ xs) s = {!!}

  convertλ : ∀ {Γ mτ} → (id : Id) (τ : Typeᵐ) (w : World) → [] ⊢ᵐ ↓ τ < w >
           → FnStm Γ ⇓ ((id ⦂ convertType τ < w >) ∷ []) ⦂ mτ < w >
             × Σ _ (λ Γ → FnStm [] ⇓ Γ ⦂ mτ < client >)
             × Σ _ (λ Δ → FnStm [] ⇓ Δ ⦂ mτ < server >)
  convertλ id τ w t with convertValue t
  ... | t' , tCliPair , tSerPair = `var id (⊆-exp-lemma (λ ()) t') , tCliPair , tSerPair

  convertλs : ∀ {mτ}
            → (lifted : List (Σ (Id × Typeᵐ × World) (λ { (id , σ , w') → [] ⊢ᵐ ↓ σ < w' >})))
            → Σ _ (λ Γ → FnStm [] ⇓ Γ ⦂ mτ < client >) × Σ _ (λ Δ → FnStm [] ⇓ Δ ⦂ mτ < server >)
  convertλs [] = ([] , `nop) , ([] , `nop)
  convertλs {mτ} (((id , σ , client) , t) ∷ xs) with convertλ {[]}{mτ} id σ client t | convertλs {mτ} xs
  ... | fnStm , (Γ , cli) , (Δ , ser) | (Γ' , cliFnStm) , (Δ' , serFnStm) =
        (_ , (cliFnStm ； ⊆-fnstm-lemma (λ ()) cli ； ⊆-fnstm-lemma (λ ()) fnStm)) , (_ , (serFnStm ； ⊆-fnstm-lemma (λ ()) ser))
  convertλs {mτ} (((id , σ , server) , t) ∷ xs) with convertλ {[]}{mτ} id σ server t | convertλs {mτ} xs
  ... | fnStm , (Γ , cli) , (Δ , ser) | (Γ' , cliFnStm) , (Δ' , serFnStm) =
        (_ , (cliFnStm ； ⊆-fnstm-lemma (λ ()) cli)) , (_ , (serFnStm ； ⊆-fnstm-lemma (λ ()) ser ； ⊆-fnstm-lemma (λ ()) fnStm))

  convertAll : ∀ {l1 l2} {A : Set l1} {P : A → Set l2} → (xs : List A) → Data.List.All.All (λ a → P a) xs → List (Σ A (λ a → P a))
  convertAll .[] Data.List.All.[] = []
  convertAll _ (px Data.List.All.∷ all) = (_ , px) ∷ convertAll _ all

  -- TODO add `prim `socket to client and `prim `io to server
  -- Takes a list of λ lifted list of functions and a term that runs on the client.
  -- Returns JS code for client and server.
  entryPoint : ∀ {w}
             → Σ (List (Id × Typeᵐ × World))
                  (λ newbindings → Data.List.All.All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) newbindings × (toCtx newbindings) ⊢ᵐ ⋆< w >)
             → (Stm [] < client >) × (Stm [] < server >)
  entryPoint (xs , all , t) with convertλs {nothing} (convertAll _ all)
  ... | (Γ' , cliFnStmLifted) , (Δ' , serFnStmLifted) with convertCont {toCtx xs}{Γ' +++ []}{Δ' +++ []}{nothing} _ t
  ... | (δ , cliFnStm) , (φ , serFnStm) =
      `exp ((` `λ [] ⇒ (cliFnStmLifted ； cliFnStm ；return `undefined) · Data.List.All.[]))
    , `exp ((` `λ [] ⇒ (serFnStmLifted ； serFnStm ；return `undefined) · Data.List.All.[]))
