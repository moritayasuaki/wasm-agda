module MiniWasm4 (Var : Set) where

open import Data.Maybe as MaybeM
open import Function hiding (const)
open import Data.Integer as IntM hiding (_+_ ; suc ; _≤_ ; _≤?_ ; +_ ; _⊔_)
open import Data.Nat as Nat
open import Data.Bool as BoolM hiding (not ; _≤_ ; _≤?_)
open import Data.Unit hiding (_≤_ ;  _≤?_)
open import Data.Product
open import Data.Fin hiding (_+_ ; _≤_ ; _≤?_)
open import Data.Vec as VecM hiding (_++_ ; length ; _>>=_)
open import Data.List as ListM hiding (and)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Product
open import Data.Empty

Dec-≡ : Set → Set
Dec-≡ A = Decidable (_≡_ {A = A})

data Wildcard (A : Set) : Set where
  exactly : A → Wildcard A
  atleast : A → Wildcard A

private
  variable
    n : ℕ

module Syntax where
  data InsnGroup : Set where
    arith : InsnGroup
    logic : InsnGroup
    store : InsnGroup
    control : InsnGroup

  data Insn : ℕ → Set where
    const : ℤ → Insn n
    load : Var → Insn n
    store : Var → Insn n
    add : Insn n
    mul : Insn n
    and : Insn n
    not : Insn n
    nop : Insn n
    br : (l : Fin n) → Insn n
    brif : (l : Fin n) → Insn n
    block : (a r : ℕ) → (is : List (Insn (suc n))) → Insn n
    loop : (a r : ℕ) → (is : List (Insn (suc n))) → Insn n

  Code : ℕ → Set
  Code n = List (Insn n)

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
      -- i : Insn -- an instruction
      -- is : Code -- sequence of instructions

  _subtypeOf_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r) subtypeOf (a' , r') = ∃ λ ((da , dr) : ℕ × ℕ) → da ≡ dr × a + da ≡ a' × r + dr ≡ r'

  _subtypeOfW_ : ℕ × Wildcard ℕ → ℕ × ℕ → Set
  (a , exactly r) subtypeOfW (a' , r') = (a , r) subtypeOf (a' , r')
  (a , atleast r0) subtypeOfW (a' , r') = ∃ λ d → (a , r0 + d) subtypeOf (a' , r')

  _subtypeOfWM_ : Maybe (ℕ × Wildcard ℕ) → ℕ × ℕ → Set
  nothing subtypeOfWM _ = ⊥
  just q subtypeOfWM t = q subtypeOfW t

  _subtypeOf?_ : Decidable _subtypeOf_
  (a , r) subtypeOf? (a' , r') with a ≤? a' | r ≤? r'
  ... | no a≰a' | _ = no λ (_ , _ , a+d≡a' , _) → a≰a' (m+n≤o⇒m≤o _ (≤-reflexive a+d≡a')) 
  ... | _ | no r≰r' = no λ (_ , _ , _ , r+d≡r') → r≰r' (m+n≤o⇒m≤o _ (≤-reflexive r+d≡r'))
  ... | yes a≤a' | yes r≤r' with r' ∸ r Nat.≟ a' ∸ a
  ... | no np =  no λ (da , dr , a+d≡a' , r+d≡r') → {! !}  
  ... | yes p = {! !}

  _subtypeOfW?_ : Decidable _subtypeOfW_
  (a , exactly r) subtypeOfW? (a' , r') = (a , r) subtypeOf? (a' , r')

  {-
  (a , atleast r0) subtypeOfW? (a' , r') with a ≤? a' 
  ... | no a≰a' = no λ (d , sub) → a≰a' (sub→a≤a' sub)
  ... | yes a≤a' with r0 + a' ≤? a + r'
  ... | no r0+a'≰a+r' = no λ (d , sub) → let
    open ≤-Reasoning
    (_ , a+r'≡r+a') = sub→≤×cmp sub
    r0+a'≤a+r' = begin
      r0 + a' ≤⟨ +-monoˡ-≤ a' (m≤m+n r0 d) ⟩ 
      r0 + d + a' ≡⟨ sym a+r'≡r+a' ⟩
      a + r' ∎
    in r0+a'≰a+r' r0+a'≤a+r'
  ... | yes r0+a'≤a+r' = let
    open ≤-Reasoning
    d = a' ∸ a
    r = a + r' ∸ a'
    d' = r ∸ r0
    a'≤a+r' = begin
      a' ≤⟨ m≤n+m a' r0 ⟩
      r0 + a' ≤⟨ r0+a'≤a+r' ⟩
      a + r' ∎
    {-
    d≤r' = begin
      d  ≤⟨  ∸-monoˡ-≤ a a'≤a+r' ⟩
      a + r' ∸ a ≡⟨ m+n∸m≡n a r' ⟩
      r' ∎
    -}
    r0≤r = begin
      r0 ≡⟨ sym (+-identityʳ r0) ⟩
      r0 + 0 ≡⟨ cong (r0 +_) (sym (n∸n≡0 a')) ⟩
      r0 + (a' ∸ a') ≡⟨ sym (+-∸-assoc r0 (≤-refl {a'})) ⟩
      r0 + a' ∸ a' ≤⟨ ∸-monoˡ-≤ a' r0+a'≤a+r' ⟩
      r ∎
    r+a'≡a+r' = begin-equality
      r + a' ≡⟨ m∸n+n≡m {m = a + r'} {n = a'}  a'≤a+r' ⟩
      a + r' ∎
    in yes (d' ,  d , {!!} , {!!})
    -}

  _subtypeOfWM?_ : Decidable _subtypeOfWM_
  nothing subtypeOfWM? t' = no λ()
  just t subtypeOfWM? t' = t subtypeOfW? t' 

  _supertypeOfE_ : List ℕ × ℕ × ℕ → List ℕ × ℕ × ℕ  → Set
  (es , t) supertypeOfE (es' , t') =  ∃ λ de → es ++ de ≡ es' × t' subtypeOf t

  hasTypeC : {n : ℕ} → (es : Vec ℕ n) → Code n → ℕ × ℕ → Set
  hasTypeI : {n : ℕ} → (es : Vec ℕ n) → Insn n → ℕ × ℕ → Set

  hasTypeC es [] (a , r) = a ≡ r
  hasTypeC es (i ∷ is) (a , r) = ∃ λ m → hasTypeI es i (a , m) × hasTypeC es is (m , r)

  hasTypeI es (const x) (a , suc r) = a ≡ r
  hasTypeI es (load x) (a , suc r) = a ≡ r
  hasTypeI es (store x) (suc a , r) = a ≡ r
  hasTypeI es add (suc (suc a) , suc r) = a ≡ r
  hasTypeI es mul (suc (suc a) , suc r) = a ≡ r
  hasTypeI es and (suc (suc a) , suc r) = a ≡ r 
  hasTypeI es not (suc a , suc r) = a ≡ r
  hasTypeI es nop (a , r) =  a ≡ r
  hasTypeI es (br l) (a , r) = ∃ λ d → VecM.lookup es l + d ≡ a
  hasTypeI es (brif l) (suc a , r) = (a ≡ r) × ∃ λ d → (VecM.lookup es l + d ≡ a)
  hasTypeI es (block a' r' is) (a , r) = hasTypeC (r' ∷ es) is (a' , r') × (a' , r') subtypeOf (a , r)
  hasTypeI es (loop a' r' is) (a , r) = hasTypeC (a' ∷ es) is (a' , r') × (a' , r') subtypeOf (a , r)
  hasTypeI es _ _ = ⊥

  hasTypeCW : {n : ℕ} → (es : Vec ℕ n) → Code n → ℕ × Wildcard ℕ → Set
  hasTypeCW es is (a , exactly r) = hasTypeC es is (a , r)
  hasTypeCW es is (a , atleast r0) = (r : ℕ) → r0 ≤ r → hasTypeC es is (a , r)

  data _⊢_hasTypeC_ (es : Vec ℕ n) : Code n → ℕ × ℕ → Set
  data _⊢_hasMinTypeI_ (es : Vec ℕ n) : Insn n → ℕ × ℕ → Set where
    tconst : es ⊢ const z hasMinTypeI (0 , 1)
    tload  : es ⊢ load v hasMinTypeI (0 , 1)
    tstore : es ⊢ store v hasMinTypeI (1 , 0)
    tnop   : es ⊢ nop hasMinTypeI (0 , 0)
    tnot   : es ⊢ not hasMinTypeI (1 , 1)
    tand   : es ⊢ and hasMinTypeI (2 , 1)
    tmul   : es ⊢ mul hasMinTypeI (2 , 1)
    tadd   : es ⊢ add hasMinTypeI (2 , 1)
    tbr    : ∀{l : Fin n} → es ⊢ br l hasMinTypeI (VecM.lookup es l , r)
    tbrif  : ∀{l : Fin n} → es ⊢ brif l hasMinTypeI ((suc (VecM.lookup es l)) , VecM.lookup es l)
    tblock :
      {is : Code (suc n)} →
      (r ∷ es) ⊢ is hasTypeC (a , r) →
      es ⊢ block a r is hasMinTypeI ( a , r)
    tloop  :
      {is : Code (suc n)} →
      (a ∷ es) ⊢ is hasTypeC (a , r) →
      es ⊢ loop a r is hasMinTypeI (a , r)

  _⊢_hasTypeI_ : (es : Vec ℕ n) → Insn n → ℕ × ℕ → Set
  es ⊢ i hasTypeI t = ∃ λ t0 → (es ⊢ i hasMinTypeI t0) × (t0 subtypeOf t)

  data _⊢_hasTypeC_ {n} es where
    [] : es ⊢ [] hasTypeC (r , r)
    _∷_ : {i : Insn n} → {is : Code n} → es ⊢ i hasTypeI (a , m) → es ⊢ is hasTypeC (m , r) → es ⊢ (i ∷ is) hasTypeC (a , r)

  _⊢_hasTypeCW_ : (es : Vec ℕ n) → Code n → ℕ × Wildcard ℕ → Set
  es ⊢ is hasTypeCW (a , exactly r) = es ⊢ is hasTypeC (a , r)
  es ⊢ is hasTypeCW (a , atleast r0) = ∃ λ d → es ⊢ is hasTypeC (a , r0 + d)

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

  comp : ℕ × Wildcard ℕ → ℕ × Wildcard ℕ → ℕ × Wildcard ℕ
  comp (a , exactly r) (a' , exactly r') = (a + (a' ∸ r) , exactly ((r ∸ a') + r'))
  comp (a , exactly r) (a' , atleast r') = (a + (a' ∸ r) , atleast ((r ∸ a') + r'))
  comp (a , atleast r) (a' , exactly r') = (a , atleast (r' + (r ∸ a')))
  comp (a , atleast r) (a' , atleast r') = (a , atleast (r' + (r ∸ a')))

  inferI : Vec ℕ n → Insn n → Maybe (ℕ × Wildcard ℕ)
  inferC : Vec ℕ n → Code n → Maybe (ℕ × Wildcard ℕ)

  inferI es (const z) = just (0 , exactly 1)
  inferI es (load x) = just (0 , exactly 1)
  inferI es (store x) = just (1 , exactly 0)
  inferI es add = just (2 , exactly 1)
  inferI es mul = just (2 , exactly 1)
  inferI es and = just (2 , exactly 1)
  inferI es not = just (1 , exactly 1)
  inferI es nop = just (0 , exactly 0)
  inferI es (br l) = let
    e = VecM.lookup es l
    in just (e , atleast 0)
  inferI es (brif l) = let
    e = VecM.lookup es l
    in just (suc e , exactly e)
  inferI es (block a r is) = do
    t ← inferC (r ∷ es) is
    _ ← decToMaybe (t subtypeOfW? (a , r))
    just (a , exactly r)

  inferI es (loop a r is) = do
    t ← inferC (a ∷ es) is
    _ ← decToMaybe (t subtypeOfW? (a , r))
    just (a , exactly r)


  inferC es [] = just (0 , exactly 0)
  
  inferC es (i ∷ is) = do
    ti ← inferI es i
    tis ← inferC es is
    just (comp ti tis)

  example0' = (1 , 1) subtypeOf? (2 , 2)
  example0 = inferI [] (block 1 1 (br FinM.zero ∷ []))
  example1 = inferI (1 ∷ []) (br FinM.zero)
  example2 = inferC (1 ∷ []) (br FinM.zero ∷ [])

  lemma' : (m n : ℕ) → m + (n ∸ m) ≡ m ⊔ n
  lemma' zero zero = refl
  lemma' zero (suc n) = refl
  lemma' (suc m) zero = cong suc (+-identityʳ m)
  lemma' (suc m) (suc n) = cong suc (lemma' m n)

  lemma : (m n : ℕ) → n + (m ∸ n) ≡ m + (n ∸ m)
  lemma zero zero = refl
  lemma zero (suc n) = cong suc (+-comm n 0)
  lemma (suc m) zero = cong suc (+-comm 0 m)
  lemma (suc m) (suc n) = cong suc (lemma m n)

  soundnessC : ∀{a r} → (es : Vec ℕ n) → (is : Code n) → inferC es is subtypeOfWM (a , r) → hasTypeC es is (a , r)
  soundnessI : ∀{a r} → (es : Vec ℕ n) → (i : Insn n) → inferI es i subtypeOfWM (a , r) → hasTypeI es i (a , r)
  soundnessC es [] (_ , refl , refl , refl) = refl
  soundnessC es (i ∷ is) proof with inferI es i | inspect (inferI es) i
  ... | just (a , mr) | [ infer-i≡ ] with inferC es is | inspect (inferC es) is
  soundnessC es (i ∷ is) ((d , .d) , refl , refl , refl) | just (a , exactly r) | [ infer-i≡ ] | just (a' , exactly r') | [ infer-is≡ ] = let
    open ≤-Reasoning
    in (r + (a' ∸ r) + d
       , soundnessI es i (subst (_subtypeOfWM _) (sym infer-i≡) ( (a' ∸ r + d , a' ∸ r + d) , refl , sym (+-assoc a _ _) , sym (+-assoc r _ _))) 
       , soundnessC es is (subst (_subtypeOfWM _) (sym infer-is≡) ( (r ∸ a' + d , r ∸ a' + d) , refl , trans (sym (+-assoc a' _ _)) (cong (_+ d) (lemma r a')) ,  trans (sym (+-assoc r' _ _)) (cong (_+ d) (+-comm r' _))))
       )
  soundnessC es (i ∷ is) (d' , r∸a+r0'≤r' , (d , refl , refl)) | just (a , exactly r) | [ infer-i≡ ] | just (a' , atleast r0') | [ infer-is≡ ] = let
    open ≤-Reasoning
    in {!!}
  soundnessC es (i ∷ is) (d , q , p) | just (a , atleast r0) | [ infer-i≡ ] | just (a' , exactly r') | [ infer-is≡ ] = {!!}
  soundnessC es (i ∷ is) (d , q , p) | just (a , atleast r0) | [ infer-i≡ ] | just (a' , atleast r0') | [ infer-is≡ ] = {!!}
-- ( subst (λ X → (a + (a' ∸ r) + d , r + (a' ∸ r) + d) instanceOfWM X) 

  soundnessI es (const x) (_ , refl , refl , refl) = refl
  soundnessI es (load x) (_ , refl , refl , refl) = refl
  soundnessI es (store x) (_ , refl , refl , refl) = refl
  soundnessI es add (_ , refl , refl , refl) = refl
  soundnessI es mul (_ , refl , refl , refl) = refl
  soundnessI es and (_ , refl , refl , refl) = refl
  soundnessI es not (_ , refl , refl , refl) = refl
  soundnessI es nop (_ , refl , refl , refl) = refl
  soundnessI es (br l) (_ , (d , .d) , refl , refl , refl) = (d , refl)
  soundnessI es (brif l) (d , refl , refl , refl) = (refl , {!!})

  soundnessI es (block a' r' is) proof with inferC (r' ∷ es) is | inspect (inferC (r' ∷ es)) is
  ... | just (a'' , mr'') | [ eq ] with (a'' , mr'') subtypeOfW? (a' , r')
  soundnessI es (block a' r' is) a'r'⊑ar | just (a'' , exactly r'') | [ eq ] | yes a''r''⊑a'r' =
    (soundnessC (r' ∷ es) is (subst (_subtypeOfWM _) (sym eq) a''r''⊑a'r') , a'r'⊑ar)
  soundnessI es (block a' r' is) a'r'⊑ar | just (a'' , atleast r0'') | [ eq ] | yes (∃r''≥r0'',a''r''⊑a'r') =
    (soundnessC (r' ∷ es) is (subst (_subtypeOfWM _) (sym eq) (∃r''≥r0'',a''r''⊑a'r')) , a'r'⊑ar)

  soundnessI es (loop a' r' is) proof with inferC (a' ∷ es) is | inspect (inferC (a' ∷ es)) is
  ... | just (a'' , mr'') | [ eq ] with (a'' , mr'') subtypeOfW? (a' , r')
  soundnessI es (loop a' r' is) a'r'⊑ar | just (a'' , exactly r'') | [ eq ] | yes a''r''⊑a'r' =
    (soundnessC (a' ∷ es) is (subst (_subtypeOfWM _) (sym eq) a''r''⊑a'r') , a'r'⊑ar)
  soundnessI es (loop a' r' is) a'r'⊑ar | just (a'' , atleast x) | [ eq ] | yes ∃r''≥r0'',a''r''⊑a'r' =
    (soundnessC (a' ∷ es) is (subst (_subtypeOfWM _) (sym eq) ∃r''≥r0'',a''r''⊑a'r') , a'r'⊑ar)

{-
  soundness es (i ∷ is) inferOk with inferI es i | inspect (inferI es) i
  ... | just (a0 , anything) | [ eq ] = {!!}
  ... | just (a0 , just r0) | [ eq ] with inferC es is
  ... | just (a0' , anything) = {!!}
  ... | just (a0' , just r0') = {!!}

  principality : ∀{a r} → (es : Vec ℕ n) → (is : Code n) → hasTypeC es is (a , r) → ∃ λ ((a0 , mr0) : ℕ × Wildcard ℕ) → inferC es is ≡ just (a0 , mr0) × (a0 , mr0) instanceOfW (a , r)
  principality es [] [] with inferC es [] | inspect (inferC es) []
  principality {a} es [] [] | just (.0 , .(just 0)) | [ refl ] = ((0 , just 0) , refl , a , refl , refl)
  principality es (i ∷ is) (ti ∷ tis) with inferI es i | inspect (inferI es) i | principality es is tis
  ... | nothing | [ eq ] | good = {!!}
  ... | just x | [ eq ] | good = {!!}
-}

module Semantics (_≟_ : Dec-≡ Var)  where
  open Syntax
  open Typing
  open import Data.Vec as VecM
  open import Data.Empty
  open import Data.Sum
  open import Data.List.Properties using (++-identityʳ)

  castB : ℤ → Bool
  castB +0 = false
  castB _ = true

  castB' : Bool → ℤ
  castB' false = +0
  castB' true = 1ℤ

  Store = Var → ℤ

  updateS : Var → ℤ → Store → Store -- store update
  updateS v z sto v' = if isYes (v ≟ v') then z else sto v'
  lookupS : Var → Store → ℤ -- store lookup
  lookupS v sto = sto v

  OpeStk = Vec ℤ

  Cfg : ℕ → Set
  Cfg n = Store × OpeStk n

  module DirectStyle where
    Lbls : Vec ℕ n → Set
    Lbls [] = ⊥
    Lbls (e ∷ es) = Cfg e ⊎ Lbls es
  

    injL : {es : Vec ℕ n} → {l : Fin n} → Cfg (VecM.lookup es l) → Lbls es
    injL {es = e ∷ es} {l = zero} cfg = inj₁ cfg
    injL {es = e ∷ es} {l = suc l} cfg = inj₂ (injL cfg)
  
    injN : {es : Vec ℕ n} → {es' : Vec ℕ n} → Lbls es → Lbls (es VecM.++ es')
    injN {es = es} {es' = []} = subst Lbls {!!}
    injN {es = e ∷ es} {es' = es'} (inj₁ cfg) = inj₁ cfg
    injN {es = e ∷ es} {es' = es'} (inj₂ outer) = inj₂ {!!}

    ⟦_⟧i : (i : Insn n) → {a r : ℕ} → {es : Vec ℕ n} → es ⊢ i hasMinTypeI (a , r) → Cfg a → Cfg r ⊎ Lbls es
    ⟦_⟧ : (is : Code n) → {a r : ℕ} → {es : Vec ℕ n} → es ⊢ is hasTypeC (a , r) → Cfg a → Cfg r ⊎ Lbls es

    ⟦ .(const z) ⟧i (tconst {z}) (sto , []) =  inj₁ (sto , z ∷ [])
    ⟦ .(load v) ⟧i (tload {v}) (sto , []) = inj₁ (sto , lookupS v sto ∷ [])
    ⟦ .(store v) ⟧i (tstore {v}) (sto , z ∷ []) = inj₁ (updateS v z sto , [])
    ⟦ .nop ⟧i tnop (sto , []) = inj₁ (sto , [])
    ⟦ .not ⟧i tnot (sto , z ∷ []) = inj₁ (sto , castB' (BoolM.not (castB z)) ∷ [])
    ⟦ .and ⟧i tand (sto , z ∷ z' ∷ []) = inj₁ (sto , castB' (castB z ∧ castB z') ∷ [])
    ⟦ .mul ⟧i tmul (sto , z ∷ z' ∷ []) =  inj₁ (sto , z IntM.* z' ∷ []) 
    ⟦ .add ⟧i tadd (sto , z ∷ z' ∷ []) = inj₁ (sto , z IntM.+ z' ∷ [])
    -- stack in cfg contains as much as `br` needs.
    ⟦ br l ⟧i tbr cfg = inj₂ (injL cfg)
    ⟦ brif l ⟧i tbrif (sto , z ∷ ostk) =
      if castB z
      then inj₁ (sto , ostk)
      else inj₂ (injL (sto , ostk))
    ⟦ block a r is ⟧i (tblock is-hasTypeC) cfg with ⟦ is ⟧ is-hasTypeC cfg
    ... | inj₁ cfg' = inj₁ cfg'
    ... | inj₂ (inj₁ cfg') = inj₁ cfg'
    ... | inj₂ (inj₂ outer) = inj₂ outer
    ⟦ loop a r is ⟧i (tloop is-hasTypeC) cfg with ⟦ is ⟧ is-hasTypeC cfg
    ... | inj₁ cfg' = inj₁ cfg'
    ... | inj₂ (inj₁ cfg') = ⟦ loop a r is ⟧i (tloop is-hasTypeC) cfg'
    ... | inj₂ (inj₂ outer) = inj₂ outer

    ⟦ .[] ⟧ [] cfg = inj₁ cfg
    -- Sequential composition ⟦ i ∷ is ⟧ provides only minimum footprint for ⟦ i ⟧i, i.e. it provides (VecM.take a0 ostk) for `i` and keeps (VecM.drop a0 ostk) for subsequent instructions `is` 
    -- This can be done because we know the minimum footprint `a0` for `i` by `hasMinTypeI` predicate.
    -- If the evaluation of `i` normally goes in current frame, then we take back `VecM.drop a0 ostk` under `ostk'` which is production of `i`.
    -- If the evaluation of `i` jump outside, then `VecM.drop a0 ostk` will be lost.
    -- Sequencial composition only give minimum footprint for `br l` instruction too.
    -- Here, `es !! l` corresponds to the minumum footprint for `br l`.
    -- So `br` instruction itself does not need to do something like spliting local stack or discarding stack elements.
    ⟦ i ∷ is ⟧ (((a0 , r0) , i-hasMinTypeI , (d , .d) , refl , refl , refl) ∷ tis) (sto , ostk) with ⟦ i ⟧i i-hasMinTypeI (sto , VecM.take a0 ostk)
    ... | inj₁ (sto' , ostk') = ⟦ is ⟧ tis (sto' , ostk' VecM.++ (VecM.drop a0 ostk))
    ... | inj₂ lbls = inj₂ lbls

