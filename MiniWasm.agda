module MiniWasm (Var : Set) where

open import Function hiding (const)
open import Data.Integer as IntM hiding (_+_ ; suc ; _≤_ ; _≤?_ ; +_)
open import Data.Nat as Nat
open import Data.Bool as BoolM hiding (not ; _≤_ ; _≤?_)
open import Data.Unit hiding (_≤_ ;  _≤?_)
open import Data.Product
open import Data.List as ListM hiding (and)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Product
open import Data.Empty
open import Data.Maybe as MaybeM

Dec-≡ : Set → Set
Dec-≡ A = Decidable (_≡_ {A = A})

data Wildcard (A : Set) : Set where
  just : A → Wildcard A
  anything : Wildcard A

module Syntax where
  data InsnGroup : Set where
    arith : InsnGroup
    logic : InsnGroup
    store : InsnGroup
    control : InsnGroup

  data Insn : Set where
    const : ℤ → Insn
    load : Var → Insn
    store : Var → Insn
    add : Insn
    mul : Insn
    and : Insn
    not : Insn
    nop : Insn
    br : (l : ℕ) → Insn
    brif : (l : ℕ) → Insn
    block : (a r : ℕ) → (is : List Insn) → Insn
    loop : (a r : ℕ) → (is : List Insn) → Insn

  Code = List Insn

module Typing where
  open Syntax
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat.Properties


  private
    variable
      es es' : List ℕ -- type for block context
      l : ℕ -- block height
      v : Var -- varibale name
      z : ℤ -- integer value
      a r a' r' d m : ℕ -- operand type argument and result
      i : Insn -- an instruction
      is : Code -- sequence of instructions

  infixl 1 _hasTypeC_
  infixr 1 _hasMinType_

  _comparableWith_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r) comparableWith (a' , r') = a + r' ≡ r + a'

  _comparableWith?_ : Decidable _comparableWith_
  (a , r) comparableWith? (a' , r') = a + r' Nat.≟ r + a'

  _subtypeOf_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r) subtypeOf (a' , r') = ∃ λ d → a + d ≡ a' × r + d ≡ r'

  _subtypeOfW_ : ℕ × Wildcard ℕ → ℕ × ℕ → Set
  (a , just r) subtypeOfW (a' , r') = (a , r) subtypeOf (a' , r')
  (a , anything) subtypeOfW (a' , r') = a ≤ a'

  ≤×cmp→sub : (a Nat.≤ a') × (a , r) comparableWith (a' , r') → (a , r) subtypeOf (a' , r')
  ≤×cmp→sub  {a} {a'} {r} {r'} (a≤a' , a+r'≡r+a') = let
    a+d≡a' = begin-equality
      a + (a' ∸ a) ≡⟨ m+[n∸m]≡n a≤a' ⟩
      a' ∎
    r+d≡r' = begin-equality
      r + (a' ∸ a) ≡⟨ sym (+-∸-assoc r a≤a') ⟩
      r + a' ∸ a ≡⟨ sym (cong (_∸ a) a+r'≡r+a') ⟩
      a + r' ∸ a ≡⟨ m+n∸m≡n a r' ⟩
      r' ∎
    in (a' ∸ a , a+d≡a' , r+d≡r')
    where open ≤-Reasoning
  sub→≤×cmp : (a , r) subtypeOf (a' , r') → a ≤ a' × (a , r) comparableWith (a' , r')
  sub→≤×cmp {a} {r} {a'} {r'} (d , a+d≡a' , r+d≡r') = let
    a≤a' = begin
      a ≤⟨ m≤m+n a d ⟩
      a + d ≡⟨ a+d≡a' ⟩
      a' ∎
    a+r'≡r+a' = begin-equality
      a + r' ≡⟨ cong (a +_) (sym (r+d≡r')) ⟩
      a + (r + d) ≡⟨ cong (a +_) (+-comm r d)⟩
      a + (d + r) ≡⟨ sym (+-assoc a d r) ⟩
      (a + d) + r ≡⟨ cong (_+ r) (a+d≡a') ⟩
      a' + r ≡⟨ +-comm a' r ⟩
      r + a' ∎
    in  (a≤a' , a+r'≡r+a')
    where open ≤-Reasoning
    
  ≤×cmp⇔sub : (a ≤ a' × (a , r) comparableWith (a' , r')) ⇔ (a , r) subtypeOf (a' , r')
  Equivalence.f ≤×cmp⇔sub = ≤×cmp→sub
  Equivalence.g ≤×cmp⇔sub  = sub→≤×cmp
  Equivalence.cong₁ ≤×cmp⇔sub refl = refl
  Equivalence.cong₂ ≤×cmp⇔sub refl = refl

  _subtypeOf?_ : Decidable _subtypeOf_
  (a , r) subtypeOf? (a' , r') with a ≤? a' ×-dec (a , r) comparableWith? (a' , r')
  ... | yes p = yes (≤×cmp→sub p)
  ... | no np =  no λ p → np (sub→≤×cmp p)

  _subtypeOfE_ : List ℕ × ℕ × ℕ → List ℕ × ℕ × ℕ  → Set
  (es , t) subtypeOfE (es' , t') =  ∃ λ de → es ++ de ≡ es' × t subtypeOf t' 


  data _hasTypeC_ : Code → List ℕ × ℕ × ℕ → Set
  data _hasMinTypeI_ : Insn → List ℕ × ℕ × ℕ → Set where
    tconst : const z hasMinTypeI ([] , 0 , 1)
    tload  :  load v hasMinTypeI ([] , 0 , 1)
    tstore : store v hasMinTypeI ([] , 1 , 0)
    tnop   :     nop hasMinTypeI ([] , 0 , 0)
    tnot   :     not hasMinTypeI ([] , 1 , 1)
    tand   :     and hasMinTypeI ([] , 2 , 1)
    tmul   :     mul hasMinTypeI ([] , 2 , 1)
    tadd   :     add hasMinTypeI ([] , 2 , 1)
    tbr    :
      (l ≡ length es) →
      br l hasMinTypeI (es ++ (a ∷ []) , a , r)
    tbrif  : 
      (l ≡ length es) →
      brif l hasMinTypeI (es ++ (a ∷ []), (suc a) , a)
    tblock :
      is hasTypeC (r ∷ es , a , r) →
      block a r is hasMinTypeI (es , a , r)
    tloop  :
      is hasTypeC (a ∷ es , a , r) →
      loop a r is hasMinTypeI (es , a , r)

  _hasTypeI_ : Insn → List ℕ × ℕ × ℕ → Set
  i hasTypeI t = ∃ λ t0 → (i hasMinTypeI t0) × ( t0 subtypeOfE t)

  data _hasTypeC_ where
    [] : [] hasTypeC (es , r , r)
    _∷_ : i hasTypeI (es , a , m) → is hasTypeC (es , m , r) → (i ∷ is) hasTypeC (es , a , r)

  _hasTypeCW_ : Code → List ℕ × ℕ × Wildcard ℕ → Set
  is hasTypeCW (es , a , just r) = is hasTypeC (es , a , r)
  is hasTypeCW (es , a , anything) = ∃ λ r → is hasTypeC (es , a , r)

module TypeInference where
  open Syntax
  open Typing
  open import Data.Maybe as MaybeM
  open import Data.Fin as FinM hiding (_+_ ; suc ; _≤?_)
  open import Data.Nat.Properties

  _!!_ : List ℕ → ℕ → Maybe ℕ
  [] !! _  = nothing
  (x ∷ xs) !! zero = just x
  (_ ∷ xs) !! (suc n) = xs !! n

  guard : {P : Set} → Dec P → Maybe ⊤
  guard (yes _) = just _
  guard (no _) = nothing

  netStackEffect : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
  netStackEffect (a , r) (a' , r') = (a + (a' ∸ r) , r' + (r ∸ a'))

  inferI : List ℕ → Insn → Maybe (ℕ × Wildcard ℕ)
  inferC : List ℕ → Code → Maybe (ℕ × Wildcard ℕ)

  inferI es (const z) = just (0 , just 1)
  inferI es (load x) = just (0 , just 1)
  inferI es (store x) = just (1 , just 0)
  inferI es add = just (2 , just 1)
  inferI es mul = just (2 , just 1)
  inferI es and = just (2 , just 1)
  inferI es not = just (1 , just 1)
  inferI es nop = just (0 , just 0)
  inferI es (br l) = do
    e ← es !! l
    just (e , anything)
  inferI es (brif l) = do
    e ← es !! l
    just (suc e , just e)
  inferI es (block a r is) = do
    (a' , mr') ← inferC (r ∷ es) is
    _ ← decToMaybe (a' ≤? a)
    just r' ← just mr'
      where anything → just (a , just r)
    _ ← guard ((a' , r') subtypeOf? (a , r))
    just (a , just r)

  inferI es (loop a r is) = do
    (a' , mr') ← inferC (a ∷ es) is
    _ ← decToMaybe (a' ≤? a)
    just r' ← just mr'
      where anything → just (a , just r)
    _ ← guard ((a' , r') subtypeOf? (a , r))
    just (a , just r)

  inferC es [] = just (0 , just 0)
  inferC es (i ∷ is) = do
    (a , mr) ← inferI es i
    (a' , mr') ← inferC es is
    just r ← just mr
      where anything → just (a , anything)
    just r' ← just mr'
      where anything → just (a + (r ∸ a') , anything)
    just (a + (r ∸ a') , just ((a' ∸ r) + r'))

  example0' = (1 , 1) subtypeOf? (2 , 2)
  example0 = inferI [] (block 1 1 (br 0 ∷ []))
  example1 = inferI (1 ∷ []) (br 0)
  example2 = inferC (1 ∷ []) (br 0 ∷ [])

  soundness : ∀{a mr} → (es : List ℕ) → (is : Code) → inferC es is ≡ just (a , mr) → is hasTypeCW (es , a , mr)
  soundness es [] refl = []
  soundness es (i ∷ is) inferOk with inferI es i | inspect (inferI es) i
  ... | just (a0 , anything) | [ eq ] = {!!}
  ... | just (a0 , just r0) | [ eq ] with inferC es is
  ... | just (a0' , anything) = {!!}
  ... | just (a0' , just r0') = {!!}

  principality : ∀{a r} → (es : List ℕ) → (is : Code) → is hasTypeC (es , a , r) → ∃ λ ((a0 , mr0) : ℕ × Wildcard ℕ) → inferC es is ≡ just (a0 , mr0) × (a0 , mr0) subtypeOfW (a , r)
  principality es [] [] with inferC es [] | inspect (inferC es) []
  principality {a} es [] [] | just (.0 , .(just 0)) | [ refl ] = ((0 , just 0) , refl , a , refl , refl)
  principality es (i ∷ is) (ti ∷ tis) with inferI es i | inspect (inferI es) i | principality es is tis
  ... | nothing | [ eq ] | good = {!!}
  ... | just x | [ eq ] | good = {!!}

module Semantics (_≟_ : Dec-≡ Var)  where
  open Syntax
  open Typing
  open import Data.Vec as VecM
  open import Data.Empty
  open import Data.Sum
  open import Data.List.Properties using (++-identityʳ)

  cast : ℤ → Bool
  cast +0 = false
  cast _ = true

  cast' : Bool → ℤ
  cast' false = +0
  cast' true = 1ℤ

  Store = Var → ℤ

  updateS : Var → ℤ → Store → Store -- store update
  updateS v z sto v' = if isYes (v ≟ v') then z else sto v'
  lookupS : Var → Store → ℤ -- store lookup
  lookupS v sto = sto v

  OpeStk = Vec ℤ

  
  data _Maybe-≤_ {X : Set} : Maybe X → Maybe X → Set where
    just≤just : ∀{x y} → (just x) Maybe-≤ (just y)
    nothing≤ : ∀{y} → nothing Maybe-≤ y

  Mono : Set → Set
  Mono X = ∃ λ (f : ℕ → Maybe X) → ∀{n m} → n ≤ m → f n Maybe-≤ f m

  Cfg : ℕ → Set
  Cfg n = Store × OpeStk n

  module DirectStyle where
    Lbls : List ℕ → Set
    Lbls [] = ⊥
    Lbls (e ∷ es) = Cfg e ⊎ Lbls es
  
    injLast : {a : ℕ} → (es : List ℕ) → Cfg a → Lbls (es ListM.++ a ∷ [])
    injLast [] cfg = inj₁ cfg
    injLast (e ∷ es) cfg = inj₂ (injLast es cfg)
  
    injN : {es : List ℕ} → (es' : List ℕ) → Lbls es → Lbls (es ListM.++ es')
    injN {es} [] = subst Lbls (sym (++-identityʳ es))
    injN {e ∷ es} es' (inj₁ cfg) = inj₁ cfg
    injN {e ∷ es} es' (inj₂ outer) = inj₂ (injN es' (outer))

    ⟦_⟧i : (i : Insn) → {a r : ℕ} → {es : List ℕ} → (i hasMinTypeI (es , a , r)) → Cfg a → Cfg r ⊎ Lbls es
    ⟦_⟧ : (is : Code) → {a r : ℕ} → {es : List ℕ} → (is hasTypeC (es , a , r)) → Cfg a → Cfg r ⊎ Lbls es

    ⟦ .(const z) ⟧i (tconst {z}) (sto , []) =  inj₁ (sto , z ∷ [])
    ⟦ .(load v) ⟧i (tload {v}) (sto , []) = inj₁ (sto , lookupS v sto ∷ [])
    ⟦ .(store v) ⟧i (tstore {v}) (sto , z ∷ []) = inj₁ (updateS v z sto , [])
    ⟦ .nop ⟧i tnop (sto , []) = inj₁ (sto , [])
    ⟦ .not ⟧i tnot (sto , z ∷ []) = inj₁ (sto , cast' (BoolM.not (cast z)) ∷ [])
    ⟦ .and ⟧i tand (sto , z ∷ z' ∷ []) = inj₁ (sto , cast' (cast z ∧ cast z') ∷ [])
    ⟦ .mul ⟧i tmul (sto , z ∷ z' ∷ []) =  inj₁ (sto , z IntM.* z' ∷ []) 
    ⟦ .add ⟧i tadd (sto , z ∷ z' ∷ []) = inj₁ (sto , z IntM.+ z' ∷ [])
    ⟦ .(br (ListM.length es)) ⟧i (tbr {es = es} refl) cfg = inj₂ (injLast es cfg)
    ⟦ .(brif (ListM.length es)) ⟧i {suc a} {r} {.(es ListM.++ a ∷ [])} (tbrif {es = es} refl) (sto , z ∷ ostk) =
      if cast z
      then inj₁ (sto , ostk)
      else inj₂ (injLast es (sto , ostk))
    ⟦ block a r is ⟧i (tblock {is} is-hasType) cfg with ⟦ is ⟧ is-hasType cfg
    ... | inj₁ cfg' = inj₁ cfg'
    ... | inj₂ (inj₁ cfg') = inj₁ cfg'
    ... | inj₂ (inj₂ outer) = inj₂ outer
    ⟦ loop a r is ⟧i (tloop {is} is-hasType) cfg with ⟦ is ⟧ is-hasType cfg
    ... | inj₁ cfg' = inj₁ cfg'
    ... | inj₂ (inj₁ cfg') = ⟦ loop a r is ⟧i (tloop {is} is-hasType) cfg'
    ... | inj₂ (inj₂ outer) = inj₂ outer

    ⟦ .[] ⟧ [] cfg = inj₁ cfg
    ⟦ i ∷ is ⟧ (((es0 , a0 , r0) , ti-min , de , es0++d≡es@refl , d , a0+d≡a@refl , r0+d≡r@refl) ∷ tis) (sto , ostk) with ⟦ i ⟧i ti-min (sto , VecM.take a0 ostk)
    ... | inj₁ (sto' , ostk') = ⟦ is ⟧ tis (sto' , ostk' VecM.++ VecM.drop a0 ostk)
    ... | inj₂ A =  inj₂ (injN de A)

  module ContinuationStyle where
    Cont : ℕ → ℕ → Set
    Cont r a = Cfg a → Cfg r

    Env : ℕ → List ℕ → Set
    Env R [] = ⊤
    Env R (e ∷ es) = Cont R e × Env R es
    ⟦_⟧i : (i : Insn) → {a r : ℕ} → {es : List ℕ} → (i hasMinTypeI (es , a , r)) → {R : ℕ} → Env R es → Cont R r → Cont R a
    ⟦_⟧ : (is : Code) → {a r : ℕ} → {es : List ℕ} → (is hasTypeC (es , a , r)) → {R : ℕ} → Env R es → Cont R r → Cont R a

    lastE : {e : ℕ} → {es : List ℕ} → {R : ℕ} → Env R (es ListM.++ (e ∷ [])) → Cont R e
    lastE {es = []} (c , cs) = c
    lastE {es = e ∷ es} (c , cs) = lastE cs

    takeE : {e es : List ℕ} → {R : ℕ} → Env R (e ListM.++ es) → Env R e
    takeE {e} {[]} {R} = subst (Env R) (++-identityʳ e)
    takeE {[]} {e' ∷ es'} _ = tt
    takeE {e ∷ es} {e' ∷ es'} (c , env) = (c , (takeE {es} {e' ∷ es'} env))

    ⟦ .(const z) ⟧i (tconst {z}) _ c (sto , []) =  c (sto , z ∷ [])
    ⟦ .(load v) ⟧i (tload {v}) _ c (sto , [])  = c (sto , lookupS v sto ∷ [])
    ⟦ .(store v) ⟧i (tstore {v}) _ c (sto , z ∷ []) = c (updateS v z sto , [])
    ⟦ .nop ⟧i tnop  _ c = c
    ⟦ .not ⟧i tnot _ c (sto , z ∷ []) = c (sto , cast' (BoolM.not (cast z)) ∷ [])
    ⟦ .and ⟧i tand _ c (sto , z ∷ z' ∷ []) = c (sto , cast' (cast z ∧ cast z') ∷ [])
    ⟦ .mul ⟧i tmul _ c (sto , z ∷ z' ∷ []) = c (sto , z IntM.* z' ∷ []) 
    ⟦ .add ⟧i tadd _ c (sto , z ∷ z' ∷ []) = c (sto , z IntM.+ z' ∷ [])
    ⟦ .(br (ListM.length es)) ⟧i (tbr {es = es} refl) env c = lastE env
    ⟦ .(brif (ListM.length es)) ⟧i {suc a} {r} {.(es ListM.++ a ∷ [])} (tbrif {es = es} refl) env c (sto , z ∷ ostk) =
      if cast z
      then c (sto , ostk)
      else lastE env (sto , ostk)
    ⟦ block a r is ⟧i (tblock {is} is-hasType) env c = ⟦ is ⟧ is-hasType (c , env) c
    ⟦ loop a r is ⟧i (tloop {is} is-hasType) env c = ⟦ is ⟧ is-hasType ((⟦ loop a r is ⟧i (tloop {is} is-hasType) env c) , env) c

    ⟦ .[] ⟧ [] env = id
