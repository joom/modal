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
    hypToPair (x ⦂ τ < w >) = x , convertType {w} τ

    -- because Agda thinks mapping a list doesn't terminate.
    hypsToPair : {w : World} → List Hypᵐ → List (Id × Typeⱼ)
    hypsToPair [] = []
    hypsToPair {w} ((x ⦂ τ < w' >) ∷ xs) with w decW w'
    hypsToPair ((x ⦂ τ < w >) ∷ xs) | yes refl = hypToPair (x ⦂ τ < w >) ∷ hypsToPair {w} xs
    ... | no q = hypsToPair {w} xs

    convertType : {w : World} → Typeᵐ → Typeⱼ
    convertType `Int = `Number
    convertType `Bool = `Bool
    convertType `Unit = `Object (("type" , `String) ∷ [])
    convertType `String = `String
    convertType {w} ` τ cont = `Function [ convertType {w} τ ] `Undefined
    convertType {w} (` τ × σ) = `Object (("type" , `String) ∷ ("fst" , convertType {w} τ ) ∷ ("snd" , convertType {w} σ) ∷ [])
    convertType {w} (` τ ⊎ σ) = `Object (("type" , `String) ∷ ("dir" , `String) ∷ ("inl" , convertType {w} τ) ∷ ("inr" , convertType {w} σ) ∷ [])
    convertType {w} (` τ at w') = {!!} -- todo
    convertType {w} (`⌘ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    convertType {w} (`∀ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    convertType {w} (`∃ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    convertType {w} (`Σt[t×[_×t]cont] τ) = `Σt[t×[_×t]cont] (convertType {w} τ)
    convertType {w} (`Env Γ) = `Object (hypsToPair {w} Γ)

  convertHyp : Hypᵐ → Hypⱼ
  convertHyp (x ⦂ τ < w >) = x ⦂ convertType {w} τ < w >

  convertCtx : Contextᵐ → Contextⱼ
  convertCtx [] = []
  convertCtx (h ∷ hs) = convertHyp h ∷ convertCtx hs

  convert∈ : ∀ {h Γ} → h ∈ Γ → (convertHyp h) ∈ only (hypWorld h) (convertCtx Γ)
  convert∈ {x ⦂ τ < client >} (here refl) = here refl
  convert∈ {x ⦂ τ < server >} (here refl) = here refl
  convert∈ {x ⦂ τ < client >} {(y ⦂ σ < client >) ∷ xs} (there i) = there (convert∈ i)
  convert∈ {x ⦂ τ < client >} {(y ⦂ σ < server >) ∷ xs} (there i) = convert∈ i
  convert∈ {x ⦂ τ < server >} {(y ⦂ σ < client >) ∷ xs} (there i) = convert∈ i
  convert∈ {x ⦂ τ < server >} {(y ⦂ σ < server >) ∷ xs} (there i) = there (convert∈ i)

  convertPrim : ∀ {hs} → LiftedMonomorphic.Terms.Prim hs → JS.Terms.Prim (convertCtx hs)
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `log = `log
  convertPrim `prompt = `prompt
  convertPrim `readFile = `readFile

  mutual
    convertCont : ∀ {Γ Δ Φ}
                → {s : only client (convertCtx Γ) ⊆ Δ}
                → {s' : only server (convertCtx Γ) ⊆ Φ}
                → (w : World)
                → Γ ⊢ᵐ ⋆< w >
                → Σ _ (λ δ → FnStm Δ ⇓ δ ⦂ nothing < client >) × Σ _ (λ φ → FnStm Φ ⇓ φ ⦂ nothing < server >)

    -- Conditional cases
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`if t `then u `else v) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {Γ}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} client u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {Γ}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} client v
    ... | (Δ''' , vCli) , (Φ''' , vSer)
      with reconcileTerms uCli vCli | reconcileTerms uSer vSer
    ... | uCli' , vCli' | uSer' , vSer' =
          (_ , (tCli ； (`if ⊆-exp-lemma (++ʳ Δ' ∘ s) t' `then uCli' `else vCli')))
        , (_ , (tSer ； (uSer ； ⊆-fnstm-lemma (++ʳ Φ'') vSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`if t `then u `else v) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {Γ}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {Γ}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} server v
    ... | (Δ''' , vCli) , (Φ''' , vSer)
      with reconcileTerms uCli vCli | reconcileTerms uSer vSer
    ... | uCli' , vCli' | uSer' , vSer' =
          (_ , (tCli ； (uCli ； ⊆-fnstm-lemma (++ʳ Δ'') vCli)))
        , (_ , (tSer ； (`if ⊆-exp-lemma (++ʳ Φ' ∘ s') t' `then uSer' `else vSer')))

    -- ∨ case
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`letcase x , y `= t `in u `or v) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`letcase x , y `= t `in u `or v) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{_ ∷ _ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = {!!}}{s' = ++ʳ Φ' ∘ s'} client u
      -- with convertCont {_}{_ ∷ _ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (sub-lemma (++ʳ Δ' ∘ s))}{s' = ++ʳ Φ' ∘ s'} client u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {_}{_ ∷ _ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = {!!}}{s' = ++ʳ Φ' ∘ s'} client v
    ... | (Δ''' , vCli) , (Φ''' , vSer) =
            (_ , (tCli ； (`if `_===_ {eq = `StringEq} (⊆-exp-lemma {!!} (`proj t' "dir" (there (here refl)))) (`string "inl")
                           `then (`var x (⊆-exp-lemma (++ʳ Δ' ∘ s) (`proj t' "inl" (there (there (here refl)))))
                                  ； `var y (default _) ； {!uCli!})
                           `else (`var x (default _)
                                  ； `var y (⊆-exp-lemma (there ∘ ++ʳ Δ' ∘ s) (`proj t' "inr" (there (there (there (here refl)))))) ； {!!}) )))
          , (_ , (tSer ； (uSer ； ⊆-fnstm-lemma (++ʳ Φ'') vSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`letcase x , y `= t `in u `or v) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (++ʳ Φ' ∘ s')} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (++ʳ Φ' ∘ s')} server v
    ... | (Δ''' , vCli) , (Φ''' , vSer) = {!!}

    --   with reconcileTerms uCli vCli | reconcileTerms uSer vSer
    -- ... | uCli' , vCli' | uSer' , vSer' =
        --   (_ , (tCli ； (?)))
        -- , (_ , (tSer ； (uSer ； ⊆-fnstm-lemma (++ʳ Φ'') vSer)))

    -- convertCont server (`letcase x , y `= t `in u `or v) = {!!}
    convertCont w (`leta x `= t `in u) = {!!}
    convertCont w (`lets u `= t `in v) = {!!}
    convertCont w (`put u `= t `in v) = {!!}
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`let x `=fst t `in u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`let x `=fst t `in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{_ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (++ʳ Δ' ∘ s)}{s' = ++ʳ Φ' ∘ s'} client u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = (_ , (tCli ； (`var x (`proj (⊆-exp-lemma (++ʳ Δ' ∘ s) t') "fst" (there (here refl))) ； uCli))) , (_ , (tSer ； uSer))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`let x `=fst t `in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (++ʳ Φ' ∘ s')} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = (_ , (tCli ； uCli)) , (_ , (tSer ； (`var x (`proj (⊆-exp-lemma (++ʳ Φ' ∘ s') t') "fst" (there (here refl))) ； uSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`let x `=snd t `in u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`let x `=snd t `in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{_ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (++ʳ Δ' ∘ s)}{s' = ++ʳ Φ' ∘ s'} client u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = (_ , (tCli ； (`var x (`proj (⊆-exp-lemma (++ʳ Δ' ∘ s) t') "snd" (there (there (here refl)))) ； uCli))) , (_ , (tSer ； uSer))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`let x `=snd t `in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (++ʳ Φ' ∘ s')} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = (_ , (tCli ； uCli)) , (_ , (tSer ； (`var x (`proj (⊆-exp-lemma (++ʳ Φ' ∘ s') t') "snd" (there (there (here refl)))) ； uSer)))

    -- ∀ elim
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`let x `= t ⟨ w' ⟩`in u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`let x `= t ⟨ w' ⟩`in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{_ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (++ʳ Δ' ∘ s)}{s' = ++ʳ Φ' ∘ s'} client u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = (_ , (tCli ； (`var x (⊆-exp-lemma {!!} (` {!t'!} · {!!})) ； uCli))) , (_ , (tSer ； uSer))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`let x `= t ⟨ w' ⟩`in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = {!!}}{s' = {!!}} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = {!!}

-- with convertCont {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = {!!}}{s' = {!!}} w u
--     ... | (Δ'' , uCli) , (Φ'' , uSer) with w
--     ... | client = (_ , (tCli ； {!!})) , (_ , (tSer ； uSer))
--     ... | server = (_ , (tCli ； uCli)) , (_ , {!!})

    -- ∃ elim
    convertCont w (`let_=`unpack_`in_ x t u) = {!!}
    -- `exp `undefined ；return (⊆-exp-lemma (++ʳ Δ'' ∘ ++ʳ Δ' ∘ s) t')

-- uCli ； `exp (`λ_⇒_ {_}{{!!}}{_}{_} ("a" ∷ []) (`nop ；return ⊆-exp-lemma (++ʳ Δ'' ∘ ++ʳ Δ' ∘ s) t'))

    -- Uninteresting cases of go-cc
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`go-cc[ client ] t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = (_ , (tCli ； `exp (⊆-exp-lemma (++ʳ Δ' ∘ s) t'))) , (_ , tSer)
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`go-cc[ server ] t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = (_ , tCli) , (_ , (tSer ； `exp (⊆-exp-lemma (++ʳ Φ' ∘ s') t')))

    -- Interesting cases of go-cc
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`go-cc[ server ] t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = ({!!} , {!!}) , ({!!} , {!!})
    convertCont server (`go-cc[ client ] t) = {!!}

    -- Function call
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`call t u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) with w
    ... | client = (_ , (tCli ； (uCli ； `exp (⊆-exp-lemma (++ʳ Δ'' ∘ ++ʳ Δ' ∘ s) (` t' · (u' Data.List.All.∷ Data.List.All.[])))))) , (_ , (tSer ； uSer))
    ... | server = (_ , (tCli ； uCli)) , (_ , (tSer ； (uSer ； `exp (⊆-exp-lemma (++ʳ Φ'' ∘ ++ʳ Φ' ∘ s') (` t' · (u' Data.List.All.∷ Data.List.All.[]))))))
    convertCont w `halt = ([] , `nop) , ([] , `nop)
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`prim_`in_ {hs = hs} x t) with convertCont {hs +++ Γ}{Δ}{Φ}{s = {!s!}}{s' = {!!}} w t
    convertCont client (`prim_`in_ {hs = hs} x t) | (Δ' , tCli) , (Φ' , tSer) = (_ , (tCli ； `prim (convertPrim x))) , (_ , tSer)
    convertCont server (`prim_`in_ {hs = hs} x t) | (Δ' , tCli) , (Φ' , tSer) = (_ , tCli) , (_ , (tSer ； `prim (convertPrim x)))
    convertCont w (`let τ , x `=unpack v `in t) = {!!}
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`open t `in u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) with convertCont {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = {!!}}{s' = {!!}} w u
    ... | (Δ'' , uCli) , (Φ'' , uSer) with w
    ... | client = (_ +++ Δ'' +++ Δ' , (tCli ； uCli ； {!t'!})) , (_ , (tSer ； uSer))
    ... | server = (_ , (tCli ； uCli)) , (_ +++ Φ'' +++ Φ' , (tSer ； uSer ； {!!}))

    convertValue : ∀ {Γ Δ Φ τ w}
                 → {s : only client (convertCtx Γ) ⊆ Δ}
                 → {s' : only server (convertCtx Γ) ⊆ Φ}
                 → Γ ⊢ᵐ ↓ τ < w >
                 → (only w (convertCtx Γ)) ⊢ⱼ (convertType {w} τ) < w >
                   × Σ _ (λ δ → FnStm Δ ⇓ δ ⦂ nothing < client >)
                   × Σ _ (λ φ → FnStm Φ ⇓ φ ⦂ nothing < server >)
    convertValue `tt = `obj (("type" , `String , `string "unit") ∷ []) , ([] , `nop) , ([] , `nop)
    convertValue (`string s) = `string s , ([] , `nop) , ([] , `nop)
    convertValue `true = `true , ([] , `nop) , ([] , `nop)
    convertValue `false = `false , ([] , `nop) , ([] , `nop)
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (` t ∧ u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
        (` t' ∧ u') , (_ , (tCli ； uCli)) , (_ , (tSer ； uSer))
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (` t ∨ u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
        (` t' ∨ u') , (_ , (tCli ； uCli)) , (_ , (tSer ； uSer))
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (`¬ t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , tCliPair , tSerPair) = (`¬ t') , tCliPair , tSerPair
    convertValue (`n x) = `n inj₁ x , ([] , `nop) , ([] , `nop)
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (` t ≤ u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
        (` t' ≤ u') , (_ , (tCli ； uCli)) , (_ , (tSer ； uSer))
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (` t + u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
        (` t' + u') , (_ , (tCli ； uCli)) , (_ , (tSer ； uSer))
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (` t * u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
        (` t' * u') , (_ , (tCli ； uCli)) , (_ , (tSer ； uSer))
    convertValue (`v id ∈) = `v id (convert∈ ∈) , ([] , `nop) , ([] , `nop)
    convertValue {Γ}{Δ}{Φ}{_}{client}{s = s}{s' = s'} (`λ x ⦂ σ ⇒ t)
      with convertCont {(x ⦂ σ < client >) ∷ []}{_}{_}{s = sub-lemma (λ ())}{s' = λ ()} client t
    convertValue {w = client} (`λ x ⦂ σ ⇒ t) | (Δ' , tCli) , (Φ' , tSer) =
        (`λ x ∷ [] ⇒ (tCli ；return `undefined)) , ([] , `nop) , (_ , tSer)
    convertValue {Γ}{Δ}{Φ}{_}{server}{s = s}{s' = s'} (`λ x ⦂ σ ⇒ t)
      with convertCont {(x ⦂ σ < server >) ∷ []}{_}{_}{s = λ ()}{s' = sub-lemma (λ ())} server t
    convertValue {w = server} (`λ x ⦂ σ ⇒ t) | (Δ' , tCli) , (Φ' , tSer) =
        (`λ x ∷ [] ⇒ (tSer ；return `undefined)) , (_ , tCli) , ([] , `nop)
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (` t , u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) =
        (`obj (("type" , _ , `string "and") ∷ ("fst" , _ , t') ∷ ("snd" , _ , u') ∷ [])) , (_ , (tCli ； uCli)) , (_ , (tSer ； uSer))
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (`inl t `as σ) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , tCliPair , tSerPair) =
          `obj (("type" , `String , `string "or") ∷
                ("dir" , `String , `string "inl") ∷
                ("inl" , _ , t') ∷ ("inr" , _ , default (convertType σ)) ∷ [])
        , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (`inr t `as τ) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , tCliPair , tSerPair) =
          `obj (("type" , `String , `string "or") ∷
                ("dir" , `String , `string "inr") ∷
                ("inl" , _ , default (convertType τ)) ∷ ("inr" , _ , t') ∷ [])
          , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (`hold {w = w} t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , tCliPair , tSerPair) = {!t'!} , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{w = w}{s = s}{s' = s'}  (`sham C) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (C w) -- TODO revise
    ... | (t' , tCliPair , tSerPair) = (`λ "a" ∷ [] ⇒ `exp (⊆-exp-lemma there t')) , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{w = w}{s = s}{s' = s'} (`Λ C) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (C w) -- TODO revise
    ... | (t' , tCliPair , tSerPair) = (`λ "a" ∷ [] ⇒ `exp (⊆-exp-lemma there t')) , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{w = w}{s = s}{s' = s'} (`pack ω t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t -- TODO revise
    ... | (t' , tCliPair , tSerPair) = (`λ "a" ∷ [] ⇒ `exp (⊆-exp-lemma there t')) , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (`packΣ τ t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , tCliPair , tSerPair) = `packΣ (convertType τ) t' , tCliPair , tSerPair
    convertValue {Γ}{w = w} (`buildEnv {Δ} pf) =
          eq-replace (cong (λ v → _ ⊢ⱼ (`Object v < w >)) (pf' Δ pf w)) (`obj (envList Δ pf w))  , ([] , `nop) , ([] , `nop)
      where
        envList : (Δ : Contextᵐ) → Δ ⊆ Γ → (w : World) → List (Id × Σ Typeⱼ (λ τ → only w (convertCtx Γ) ⊢ⱼ (τ < w >)))
        envList [] s w = []
        envList ((x ⦂ τ < w' >) ∷ hs) s w with w decW w'
        ... | no q = envList hs (s ∘ there) w
        envList ((x ⦂ τ < w' >) ∷ hs) s .w' | yes refl =
                (x , convertType {w'} τ , `v x (convert∈ (s (here refl)))) ∷ envList hs (s ∘ there) w'
        pf' : (xs : _) (s : xs ⊆ Γ) (w : World) → toTypePairs (envList xs s w) ≡ hypsToPair {w} xs
        pf' [] s w = refl
        pf' ((x ⦂ τ < w' >) ∷ xs) s w with w decW w'
        ... | no q = pf' xs (s ∘ there) w
        pf' ((x ⦂ τ < w' >) ∷ xs) s .w' | yes refl = cong (λ l → (x , convertType τ) ∷ l) (pf' xs (s ∘ there) w')

  convertλ : ∀ {Γ} → (id : Id) (τ : Typeᵐ) (w : World) → [] ⊢ᵐ ↓ τ < w >
           → FnStm Γ ⇓ ((id ⦂ convertType τ < w >) ∷ []) ⦂ nothing < w >
             × Σ _ (λ Γ → FnStm [] ⇓ Γ ⦂ nothing < client >)
             × Σ _ (λ Δ → FnStm [] ⇓ Δ ⦂ nothing < server >)
  convertλ id τ w t with convertValue {[]}{[]}{[]}{s = λ ()}{s' = λ ()} t
  ... | t' , (Γ , tCli) , (Δ , tSer) = `var id (⊆-exp-lemma pf t'), (Γ , tCli) , (Δ , tSer)
    where
      pf : ∀ {xs} → only w [] ⊆ xs
      pf rewrite onlyEmpty {w} = λ ()

  convertλs : ∀ {xs} → Data.List.All.All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) xs
            → Σ _ (λ { (Γ , Δ) → (FnStm [] ⇓ Γ ⦂ nothing < client > × only client (convertCtx (toCtx xs)) ⊆ Γ)
                                 × (FnStm [] ⇓ Δ ⦂ nothing < server > × only server (convertCtx (toCtx xs)) ⊆ Δ) })
  convertλs Data.List.All.[] = ([] , []) , ((`nop , (λ ())) , (`nop , (λ ())) )
  convertλs (Data.List.All._∷_ {id , τ , client} t rest) with convertλ {[]} id τ client t | convertλs rest
  ... | fnStm , (Γ , cli) , (Δ , ser) | (Γ' , Δ') , (cliFnStm , s) , (serFnStm , s') =
      (_ , _) , ((cliFnStm ； ⊆-fnstm-lemma (λ ()) cli ； ⊆-fnstm-lemma (λ ()) fnStm) , sub-lemma (++ʳ Γ ∘ s))
              , ((serFnStm ； ⊆-fnstm-lemma (λ ()) ser) , ++ʳ Δ ∘ s')
  convertλs (Data.List.All._∷_ {id , τ , server} t rest) with convertλ {[]} id τ server t | convertλs rest
  ... | fnStm , (Γ , cli) , (Δ , ser) | (Γ' , Δ') , (cliFnStm , s) , (serFnStm , s') =
      (_ , _) , ((cliFnStm ； ⊆-fnstm-lemma (λ ()) cli ) , ++ʳ Γ ∘ s)
              , ((serFnStm ； ⊆-fnstm-lemma (λ ()) ser ； ⊆-fnstm-lemma (λ ()) fnStm) , sub-lemma (++ʳ Δ ∘ s'))

  convertAll : ∀ {l1 l2} {A : Set l1} {P : A → Set l2} → (xs : List A) → Data.List.All.All (λ a → P a) xs → List (Σ A (λ a → P a))
  convertAll .[] Data.List.All.[] = []
  convertAll _ (px Data.List.All.∷ all) = (_ , px) ∷ convertAll _ all

  -- TODO add `prim `socket to client and `prim `io to server
  -- Takes a list of λ lifted list of functions and a term that runs on the client.
  -- Returns JS code for client and server.
  entryPoint : ∀ {w}
             → Σ (List (Id × Typeᵐ × World))
                  (λ newbindings → Data.List.All.All (λ { (_ , σ , w') → [] ⊢ᵐ ↓ σ < w' > }) newbindings
                                 × (LiftedMonomorphic.Types.toCtx newbindings) ⊢ᵐ ⋆< w >)
             → (Stm [] < client >) × (Stm [] < server >)
  entryPoint (xs , all , t) with convertλs all
  ... | (Γ' , Δ') , (cliFnStmLifted , s) , (serFnStmLifted , s')
    with convertCont {toCtx xs}{Γ' +++ []}{Δ' +++ []}{s = ++ˡ ∘ s}{s' = ++ˡ ∘ s'} _ t
  ... | (δ , cliFnStm) , (φ , serFnStm) =
        `exp ((` `λ [] ⇒ (cliFnStmLifted ； cliFnStm ；return `undefined) · Data.List.All.[]))
      , `exp ((` `λ [] ⇒ (serFnStmLifted ； serFnStm ；return `undefined) · Data.List.All.[]))
