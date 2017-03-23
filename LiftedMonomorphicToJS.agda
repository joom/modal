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
  import Data.List.Any.Membership using (_++-mono_)
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
    convertType {w} (` τ at w') = ?
    convertType {w} (`⌘ C) = convertType {w} (C w)
    convertType {w} (`∀ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    convertType {w} (`∃ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    -- convertType {w} (`⌘ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    -- convertType {w} (`∀ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    -- convertType {w} (`∃ C) = `Function [ `Object (("type" , `String) ∷ []) ] (convertType {w} (C client))
    convertType {w} (`Σt[t×[_×t]cont] τ) = `Σt[t×[_×t]cont] (convertType {w} τ)
    convertType {w} (`Env Γ) = `Object (hypsToPair {w} Γ)

  convertHyp : Hypᵐ → Hypⱼ
  convertHyp (x ⦂ τ < w >) = x ⦂ convertType {w} τ < w >

  convertCtx : Contextᵐ → Contextⱼ
  convertCtx [] = []
  convertCtx (h ∷ hs) = convertHyp h ∷ convertCtx hs

  convertCtx++ : ∀ {xs ys} → convertCtx (xs +++ ys) ≡ convertCtx xs +++ convertCtx ys
  convertCtx++ {[]} = refl
  convertCtx++ {x ∷ xs} = cong (λ l → convertHyp x ∷ l) (convertCtx++ {xs})

  convert∈ : ∀ {h Γ} → h ∈ Γ → (convertHyp h) ∈ only (hypWorld h) (convertCtx Γ)
  convert∈ {x ⦂ τ < client >} (here refl) = here refl
  convert∈ {x ⦂ τ < server >} (here refl) = here refl
  convert∈ {x ⦂ τ < client >} {(y ⦂ σ < client >) ∷ xs} (there i) = there (convert∈ i)
  convert∈ {x ⦂ τ < client >} {(y ⦂ σ < server >) ∷ xs} (there i) = convert∈ i
  convert∈ {x ⦂ τ < server >} {(y ⦂ σ < client >) ∷ xs} (there i) = convert∈ i
  convert∈ {x ⦂ τ < server >} {(y ⦂ σ < server >) ∷ xs} (there i) = there (convert∈ i)

  convertPrim : ∀ {h} → LiftedMonomorphic.Terms.Prim h → JS.Terms.Prim (convertHyp h)
  convertPrim `alert = `alert
  convertPrim `version = `version
  convertPrim `logCli = `logCli
  convertPrim `logSer = `logSer
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
    ... | (Δ''' , vCli) , (Φ''' , vSer) =
          (_ , (tCli ； (`if ⊆-exp-lemma (++ʳ Δ' ∘ s) t' `then uCli `else vCli)))
        , (_ , (tSer ； (uSer ； ⊆-fnstm-lemma (++ʳ Φ'') vSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`if t `then u `else v) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {Γ}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {Γ}{Δ' +++ Δ}{Φ' +++ Φ}{s = ++ʳ Δ' ∘ s}{s' = ++ʳ Φ' ∘ s'} server v
    ... | (Δ''' , vCli) , (Φ''' , vSer) =
          (_ , (tCli ； (uCli ； ⊆-fnstm-lemma (++ʳ Δ'') vCli)))
        , (_ , (tSer ； (`if ⊆-exp-lemma (++ʳ Φ' ∘ s') t' `then uSer `else vSer)))

    -- ∨ case
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`letcase x , y `= t `in u `or v) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`letcase_,_`=_`in_`or_ {τ = τ}{σ = σ} x y t u v) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{_ ∷ _ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (there ∘ ++ʳ Δ' ∘ s)}{s' = ++ʳ Φ' ∘ s'} client u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {_}{_ ∷ _ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (there ∘ ++ʳ Δ' ∘ s)}{s' = ++ʳ Φ' ∘ s'} client v
    ... | (Δ''' , vCli) , (Φ''' , vSer) =
            (_ , (tCli ； (`if `_===_ {eq = `StringEq} (⊆-exp-lemma (++ʳ Δ' ∘ s) (`proj t' "dir" (there (here refl)))) (`string "inl")
                           `then (`var y (default (convertType {client} σ))
                                 ； `var x (⊆-exp-lemma (there ∘ ++ʳ Δ' ∘ s) (`proj t' "inl" (there (there (here refl))))) ； uCli)
                           `else (`var x (default (convertType {client} τ))
                                 ； `var y (⊆-exp-lemma (there ∘ ++ʳ Δ' ∘ s) (`proj t' "inr" (there (there (there (here refl)))))) ； vCli) )))
          , (_ , (tSer ； (uSer ； ⊆-fnstm-lemma (++ʳ Φ'') vSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`letcase_,_`=_`in_`or_ {τ = τ}{σ = σ} x y t u v) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ _ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (there ∘ ++ʳ Φ' ∘ s')} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ _ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (there ∘ ++ʳ Φ' ∘ s')} server v
    ... | (Δ''' , vCli) , (Φ''' , vSer) =
            (_ , (tCli ； (uCli ； ⊆-fnstm-lemma (++ʳ Δ'') vCli)))
          , (_ , (tSer ； (`if `_===_ {eq = `StringEq} (⊆-exp-lemma (++ʳ Φ' ∘ s') (`proj t' "dir" (there (here refl)))) (`string "inl")
                           `then (`var y (default (convertType {server} σ)) ；
                                  `var x (⊆-exp-lemma (there ∘ ++ʳ Φ' ∘ s') (`proj t' "inl" (there (there (here refl))))) ； uSer)
                           `else (`var x (default (convertType {server} τ)) ；
                                  `var y (⊆-exp-lemma (there ∘ ++ʳ Φ' ∘ s') (`proj t' "inr" (there (there (there (here refl)))))) ； vSer) )))

    -- Elim rules
    convertCont w (`leta x `= t `in u) = ?

    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`lets u `= t `in v)
      with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`lets u `= t `in v) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_ ∷ _ ∷ Γ}{_ ∷ (Δ' +++ Δ)}{_ ∷ (Φ' +++ Φ)}{s = sub-lemma (++ʳ Δ' ∘ s)}{s' = sub-lemma (++ʳ Φ' ∘ s')} client v
    ... | (Δ'' , vCli) , (Φ'' , vSer) =
          (_ , (tCli ； (`var u (⊆-exp-lemma (++ʳ Δ' ∘ s) t') ； vCli))) , (_ , (tSer ； (`var u trustMe2 ； vSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`lets u `= t `in v) | t' , (Δ' , tCli) , (Φ' , tSer) = trustMe2

    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`put u `= t `in v)
      with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{_ ∷ (Δ' +++ Δ)}{_ ∷ (Φ' +++ Φ)}{s = sub-lemma (++ʳ Δ' ∘ s)}{s' = sub-lemma (++ʳ Φ' ∘ s')} w v
    ... | (Δ'' , vCli) , (Φ'' , vSer) with w
    ... | client = trustMe3
        --   (_ , (tCli ； `var u (⊆-exp-lemma {!!} t') ； vCli))
        -- , (_ , (`var u (⊆-exp-lemma s' {!!}) ； {!vSer!}))
    ... | server = trustMe3
        --   (_ , (`var u (⊆-exp-lemma s {!t'!}) ； {!!}))
        -- , (_ , (tSer ； (`var u (⊆-exp-lemma {!!} t') ； vSer)))
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
    ... | (Δ'' , uCli) , (Φ'' , uSer) = trustMe4
          -- (_ , (tCli ； (`var x (⊆-exp-lemma {!!} (` {!t'!} · {!!})) ； uCli))) , (_ , (tSer ； uSer))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`let x `= t ⟨ w' ⟩`in u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (++ʳ Φ' ∘ s')} server u
    ... | (Δ'' , uCli) , (Φ'' , uSer) = trustMe4

-- with convertCont {_}{Δ' +++ Δ}{Φ' +++ Φ}{s = {!!}}{s' = {!!}} w u
--     ... | (Δ'' , uCli) , (Φ'' , uSer) with w
--     ... | client = (_ , (tCli ； {!!})) , (_ , (tSer ； uSer))
--     ... | server = (_ , (tCli ； uCli)) , (_ , {!!})

    -- ∃ elim
    convertCont w (`let_=`unpack_`in_ x t u) = trustMe5
    -- `exp `undefined ；return (⊆-exp-lemma (++ʳ Δ'' ∘ ++ʳ Δ' ∘ s) t')

-- uCli ； `exp (`λ_⇒_ {_}{{!!}}{_}{_} ("a" ∷ []) (`nop ；return ⊆-exp-lemma (++ʳ Δ'' ∘ ++ʳ Δ' ∘ s) t'))

    -- Uninteresting cases of go-cc
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`go-cc[ client ] t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = (_ , (tCli ； `exp (⊆-exp-lemma (++ʳ Δ' ∘ s) t'))) , (_ , tSer)
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`go-cc[ server ] t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = (_ , tCli) , (_ , (tSer ； `exp (⊆-exp-lemma (++ʳ Φ' ∘ s') t')))

    -- Interesting cases of go-cc
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`go-cc[ server ] t) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | t' , (Δ' , tCli) , (Φ' , tSer) = trustMe6
    convertCont server (`go-cc[ client ] t) = trustMe6

    -- Function call
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`call t u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    ... | (t' , (Δ' , tCli) , (Φ' , tSer)) with convertValue {_}{Δ' +++ Δ}{Φ' +++ Φ}{s =  ++ʳ Δ' ∘ s }{s' = ++ʳ Φ' ∘ s'} u
    ... | (u' , (Δ'' , uCli) , (Φ'' , uSer)) with w
    ... | client = (_ , (tCli ； (uCli ； `exp (⊆-exp-lemma (++ʳ Δ'' ∘ ++ʳ Δ' ∘ s) (` t' · (u' Data.List.All.∷ Data.List.All.[])))))) , (_ , (tSer ； uSer))
    ... | server = (_ , (tCli ； uCli)) , (_ , (tSer ； (uSer ； `exp (⊆-exp-lemma (++ʳ Φ'' ∘ ++ʳ Φ' ∘ s') (` t' · (u' Data.List.All.∷ Data.List.All.[]))))))
    convertCont w `halt = ([] , `nop) , ([] , `nop)
    -- Primitive elim
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`prim_`in_ {x ⦂ τ < client >} p t)
      with convertCont {(x ⦂ τ < client >) ∷ Γ}{convertHyp (x ⦂ τ < client >) ∷ Δ}{Φ}{s = sub-lemma s}{s' = s'} client t
    ... | (_ , tCli) , (_ , tSer) = ((_ , (`prim (convertPrim p) ； tCli))) , (_ , tSer)
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`prim_`in_ {x ⦂ τ < server >} p t)
      with convertCont {(x ⦂ τ < server >) ∷ Γ}{Δ}{convertHyp (x ⦂ τ < server >) ∷ Φ}{s = s}{s' = sub-lemma s'} client t
    ... | (_ , tCli) , (_ , tSer) = ((_ , tCli)) , (_ , (`prim (convertPrim p) ； tSer))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`prim_`in_ {x ⦂ τ < client >} p t)
      with convertCont {(x ⦂ τ < client >) ∷ Γ}{convertHyp (x ⦂ τ < client >) ∷ Δ}{Φ}{s = sub-lemma s}{s' = s'} server t
    ... | (_ , tCli) , (_ , tSer) = ((_ , (`prim (convertPrim p) ； tCli))) , (_ , tSer)
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`prim_`in_ {x ⦂ τ < server >} p t)
      with convertCont {(x ⦂ τ < server >) ∷ Γ}{Δ}{convertHyp (x ⦂ τ < server >) ∷ Φ}{s = s}{s' = sub-lemma s'} server t
    ... | (_ , tCli) , (_ , tSer) = ((_ , tCli)) , (_ , (`prim (convertPrim p) ； tSer))

    -- Existential pair elim
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`let τ , x `=unpack v `in t)
      with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} v
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`let τ , x `=unpack v `in t) | v' , (Δ' , vCli) , (Φ' , vSer)
      with convertCont {_}{_ ∷ (Δ' +++ Δ)}{Φ' +++ Φ}{s = sub-lemma (++ʳ Δ' ∘ s)}{s' = ++ʳ Φ' ∘ s'} client t
    ... | (Δ'' , tCli) , (Φ'' , tSer) = (_ , (vCli ； (`var x o ； tCli))) , (_ , (vSer ； tSer))
      where
        v'' = ⊆-exp-lemma (++ʳ Δ' ∘ s) v'
        o = `obj (("type" , _ , `string "pair") ∷ ("fst" , _ , `proj₁Σ v'') ∷ ("snd" , _ , `proj₂Σ v'') ∷ [])
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`let τ , x `=unpack v `in t) | v' , (Δ' , vCli) , (Φ' , vSer)
      with convertCont {_}{Δ' +++ Δ}{_ ∷ (Φ' +++ Φ)}{s = ++ʳ Δ' ∘ s}{s' = sub-lemma (++ʳ Φ' ∘ s')} server t
    ... | (Δ'' , tCli) , (Φ'' , tSer) = (_ , (vCli ； tCli)) , (_ , (vSer ； (`var x o ； tSer)))
      where
        v'' = ⊆-exp-lemma (++ʳ Φ' ∘ s') v'
        o = `obj (("type" , _ , `string "pair") ∷ ("fst" , _ , `proj₁Σ v'') ∷ ("snd" , _ , `proj₂Σ v'') ∷ [])

    -- Environment elim
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} w (`open_`in_ {Δ = δ} t u) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} t
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} client (`open_`in_ {Δ = δ} t u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {δ +++ Γ}{onlyCliCtx (convertCtx δ) +++ (Δ' +++ Δ)}{onlySerCtx (convertCtx δ) +++ (Φ' +++ Φ)}
        {s = Data.List.Any.Membership._++-mono_ {xs₁ = onlyCliCtx (convertCtx δ)}{xs₂ = onlyCliCtx (convertCtx Γ)}{ys₂ = Δ' +++ Δ} id (++ʳ Δ' ∘ s)
             ∘ ⊆-≡ (onlyCliCtx++ {convertCtx δ}{convertCtx Γ})  ∘ ⊆-≡ (cong onlyCliCtx (convertCtx++ {δ}{Γ}))}
        {s' = Data.List.Any.Membership._++-mono_ {xs₁ = onlySerCtx (convertCtx δ)}{xs₂ = onlySerCtx (convertCtx Γ)}{ys₂ = Φ' +++ Φ} id (++ʳ Φ' ∘ s')
             ∘ ⊆-≡ (onlySerCtx++ {convertCtx δ}{convertCtx Γ})  ∘ ⊆-≡ (cong onlySerCtx (convertCtx++ {δ}{Γ}))}
        client u
    ... | (Δ'' , uCli) , (Φ'' , uSer) =
          (_ , (tCli ； (openEnv {Δ' +++ Δ}{δ}{δ} id (⊆-exp-lemma (++ʳ Δ' ∘ s) t') ； uCli)))
        , (_ , (tSer ； (openEnv {Φ' +++ Φ}{δ}{δ} id (eq-replace trustMe (`obj {Φ' +++ Φ}{server} [])) ； uSer)))
    convertCont {Γ}{Δ}{Φ}{s = s}{s' = s'} server (`open_`in_ {Δ = δ} t u) | t' , (Δ' , tCli) , (Φ' , tSer)
      with convertCont {δ +++ Γ}{onlyCliCtx (convertCtx δ) +++ (Δ' +++ Δ)}{onlySerCtx (convertCtx δ) +++ (Φ' +++ Φ)}
           {s = Data.List.Any.Membership._++-mono_ {xs₁ = onlyCliCtx (convertCtx δ)}{xs₂ = onlyCliCtx (convertCtx Γ)}{ys₂ = Δ' +++ Δ} id (++ʳ Δ' ∘ s)
                ∘ ⊆-≡ (onlyCliCtx++ {convertCtx δ}{convertCtx Γ})  ∘ ⊆-≡ (cong onlyCliCtx (convertCtx++ {δ}{Γ}))}
          {s' = Data.List.Any.Membership._++-mono_ {xs₁ = onlySerCtx (convertCtx δ)}{xs₂ = onlySerCtx (convertCtx Γ)}{ys₂ = Φ' +++ Φ} id (++ʳ Φ' ∘ s')
                ∘ ⊆-≡ (onlySerCtx++ {convertCtx δ}{convertCtx Γ})  ∘ ⊆-≡ (cong onlySerCtx (convertCtx++ {δ}{Γ}))}
                server u
    ... | (Δ'' , uCli) , (Φ'' , uSer) =
          (_ , (tCli ； (openEnv {Δ' +++ Δ}{δ}{δ} id (eq-replace trustMe (`obj {Δ' +++ Δ}{client} [])) ； uCli)))
        , (_ , (tSer ； (openEnv {Φ' +++ Φ}{δ}{δ} id (⊆-exp-lemma (++ʳ Φ' ∘ s') t') ； uSer)))

    -- hypsToPairWrongWorld : ∀ {Γ δ w w'} → ¬ (w ≡ w') → Γ ⊢ⱼ `Object (hypsToPair {w} δ) < w' > ≡ Γ ⊢ⱼ `Object [] < w' >
    -- hypsToPairWrongWorld {w = client} {client} neq = ⊥-elim (neq refl)
    -- hypsToPairWrongWorld {w = server} {server} neq = ⊥-elim (neq refl)
    -- hypsToPairWrongWorld {δ = []} {client} {server} neq = refl
    -- hypsToPairWrongWorld {δ = (x ⦂ τ < client >) ∷ δ} {client} {server} neq = {!!}
    -- hypsToPairWrongWorld {δ = (x ⦂ τ < server >) ∷ δ} {client} {server} neq = hypsToPairWrongWorld {δ = δ} neq
    -- hypsToPairWrongWorld {δ = xs} {w = server} {client} neq = {!!}

    hypsToPair∈ : ∀ {Δ x τ w} → (x ⦂ τ < w >) ∈ Δ → (x , convertType {w} τ) ∈ hypsToPair {w} Δ
    hypsToPair∈ {w = w} (here refl) with w decW w
    hypsToPair∈ (here refl) | yes refl = here refl
    ... | no q = ⊥-elim (q refl)
    hypsToPair∈ {(x ⦂ τ < w >) ∷ xs}{w = w'} (there i) with w' decW w
    hypsToPair∈ {(x ⦂ τ < w >) ∷ xs} (there i) | yes refl = there (hypsToPair∈ i)
    ... | no q = hypsToPair∈ i

    openEnv : ∀ {Γ δ Δ mσ w} → δ ⊆ Δ
                              → Γ ⊢ⱼ (`Object (hypsToPair {w} Δ) < w >)
                              → FnStm Γ ⇓ only w (convertCtx δ) ⦂ mσ < w >
    openEnv {δ = []} {w = client} s t = `nop
    openEnv {δ = []} {w = server} s t = `nop
    openEnv {Γ}{δ = (x ⦂ τ < client >) ∷ δ}{Δ} {w = client} s t =
         openEnv {Γ}{δ}{Δ} (sub-lemma' s) t
      ； `var x (`proj (⊆-exp-lemma (++ʳ (onlyCliCtx (convertCtx δ))) t) x (hypsToPair∈ (s (here refl))))
    openEnv {Γ}{δ = (x ⦂ τ < server >) ∷ δ}{Δ} {w = server} s t =
         openEnv {Γ}{δ}{Δ} (sub-lemma' s) t
      ； `var x (`proj (⊆-exp-lemma (++ʳ (onlySerCtx (convertCtx δ))) t) x (hypsToPair∈ (s (here refl))))
    openEnv {Γ}{δ = (x ⦂ τ < server >) ∷ δ}{Δ} {w = client} s t = openEnv {Γ}{δ}{Δ} (sub-lemma' s) t
    openEnv {Γ}{δ = (x ⦂ τ < client >) ∷ δ}{Δ} {w = server} s t = openEnv {Γ}{δ}{Δ} (sub-lemma' s) t


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
    ... | (t' , tCliPair , tSerPair) = trustMe7 , tCliPair , tSerPair
    convertValue {Γ}{Δ}{Φ}{w = w}{s = s}{s' = s'}  (`sham C) with convertValue {Γ}{Δ}{Φ}{s = s}{s' = s'} (C w) -- TODO revise
    ... | (t' , tCliPair , tSerPair) = t' , tCliPair , tSerPair -- (`λ "a" ∷ [] ⇒ `exp (⊆-exp-lemma there t')) , tCliPair , tSerPair
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
