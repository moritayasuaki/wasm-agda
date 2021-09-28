module MiniWasm4 (Var : Set) where

open import Data.Maybe as MaybeM
open import Function hiding (const)
open import Data.Integer as IntM hiding (_+_ ; suc ; _≤_ ; _≤?_ ; +_ ; _⊔_)
open import Data.Nat as Nat
open import Data.Bool as BoolM hiding (not ; _≤_ ; _≤?_)
open import Data.Unit hiding (_≤_ ;  _≤?_)
open import Data.Product
open import Data.Fin as FinM hiding (_+_ ; _≤_ ; _≤?_)
open import Data.Vec as VecM hiding (_++_ ; length ; _>>=_)
open import Data.List as ListM hiding (and)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Product
open import Data.Empty
open import Data.Sum

Dec-≡ : Set → Set
Dec-≡ A = Decidable (_≡_ {A = A})

∃!⇒∃ : ∀{a ℓ} {A : Set a} {P : A → Set ℓ} → ∃! _≡_ P → ∃ P
∃!⇒∃ (x , Px , _) = x , Px

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
    block : (t : ℕ × ℕ) → (is : List (Insn (suc n))) → Insn n
    loop : (t : ℕ × ℕ) → (is : List (Insn (suc n))) → Insn n

  Code : ℕ → Set
  Code n = List (Insn n)

module Typing where
  open Syntax
  open import Data.Nat.Properties

  private
    variable
      es es' : List ℕ -- type for block context
      l : ℕ -- block height
      v : Var -- varibale name
      z : ℤ -- integer value
      a r a' r' d m r0 : ℕ -- operand type argument and result
      -- i : Insn -- an instruction
      -- is : Code -- sequence of instructions

  m≤n⇒∃!d[m+d≡n] : ∀{m n} → m ≤ n → ∃! _≡_ λ d → m + d ≡ n
  m≤n⇒∃!d[m+d≡n] {n = n} z≤n = (n , refl , sym)
  m≤n⇒∃!d[m+d≡n] {n = suc n} (s≤s m≤n) = let (d , m+d≡n , ∀d'[m+d'≡n⇒d'≡d]) = m≤n⇒∃!d[m+d≡n] m≤n in (d , cong suc m+d≡n , λ m+d'≡n → ∀d'[m+d'≡n⇒d'≡d] (suc-injective m+d'≡n)) 


  m≤n⇒∃d[m+d≡n] : ∀{m n} → m ≤ n → ∃ λ d → m + d ≡ n
  m≤n⇒∃d[m+d≡n] m≤n = ∃!⇒∃ (m≤n⇒∃!d[m+d≡n] m≤n)

  ∃d[m+d≡n]⇒m≤n : ∀{m n} → (∃ λ d → m + d ≡ n) → m ≤ n
  ∃d[m+d≡n]⇒m≤n {m} (d , m+d≡n@refl) = m≤m+n m d

  ∃!d[m+d≡n]? : Decidable λ m n → ∃! _≡_ λ d → m + d ≡ n
  ∃!d[m+d≡n]? m n with m ≤? n
  ... | yes m≤n = yes (m≤n⇒∃!d[m+d≡n] m≤n)
  ... | no m≰n = no λ (d , m+d≡n , _) → m≰n (∃d[m+d≡n]⇒m≤n (d ,  m+d≡n))

  _-?_ : Decidable λ n m → ∃! _≡_ λ d → m + d ≡ n
  m -? n = ∃!d[m+d≡n]? n m

  m+n≡o⇒m≤o : ∀ {m n o : ℕ} → m + n ≡ o → m ≤ o
  m+n≡o⇒m≤o m+n≡o = m+n≤o⇒m≤o _ (≤-reflexive m+n≡o)

  m+d≡n⇒m∸n≡d : m + d ≡ n → n ∸ m ≡ d
  m+d≡n⇒m∸n≡d {m} refl = m+n∸m≡n m _

  _subtypeOf_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r) subtypeOf (a' , r') = ∃ λ d → a + d ≡ a' × r + d ≡ r'

  _subtypeOf-≡_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r) subtypeOf-≡ (a' , r') = ∃ λ a'-a → a + a'-a ≡ a' × ∃ λ r'-r → r + r'-r ≡ r' × a'-a ≡ r'-r

  _subtypeOf-∸_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r) subtypeOf-∸ (a' , r') = a ≤ a' × r ≤ r' × a' ∸ a ≡ r' ∸ r

  sub-≡⇒sub-∸ : (a , r) subtypeOf-≡ (a' , r') → (a , r) subtypeOf-∸ (a' ,  r')
  sub-≡⇒sub-∸ {a = a} {r = r} (a'-a , a+a'-a≡a' , r'-r , r+r'-r≡r' , a'-a≡r'-r) = let
    a'-a≡a'∸a = m+d≡n⇒m∸n≡d {m = a} a+a'-a≡a'
    r'-r≡r'∸r = m+d≡n⇒m∸n≡d {m = r} r+r'-r≡r'
    in m+n≡o⇒m≤o a+a'-a≡a' , m+n≡o⇒m≤o r+r'-r≡r' , subst₂ _≡_ (sym a'-a≡a'∸a) (sym r'-r≡r'∸r) a'-a≡r'-r

  sub-∸⇒sub-≡ : (a , r) subtypeOf-∸ (a' , r') → (a , r) subtypeOf-≡ (a' , r')
  sub-∸⇒sub-≡ {a} {r} {a'} {r'} (a≤a' , r≤r' , a'∸a≡r'∸r) = (a' ∸ a , m+[n∸m]≡n a≤a' , r' ∸ r , m+[n∸m]≡n r≤r' , a'∸a≡r'∸r)

  sub-≡⇒sub : (a , r) subtypeOf-≡ (a' , r') → (a , r) subtypeOf (a' , r')
  sub-≡⇒sub (d , a+d≡a' , .d , r+d≡r' , refl) = d , a+d≡a' , r+d≡r'

  sub⇒sub-≡ : (a , r) subtypeOf (a' , r') → (a , r) subtypeOf-≡ (a' , r')
  sub⇒sub-≡ (d , a+d≡a' , r+d≡r') = d , a+d≡a' , d , r+d≡r' , refl

  sub⇒sub-∸ : (a , r) subtypeOf (a' , r') → (a , r) subtypeOf-∸ (a' , r')
  sub⇒sub-∸ = sub-≡⇒sub-∸ ∘ sub⇒sub-≡ 
  sub-∸⇒sub : (a , r) subtypeOf-∸ (a' , r') → (a , r) subtypeOf (a' , r')
  sub-∸⇒sub = sub-≡⇒sub ∘ sub-∸⇒sub-≡ 

  r-uniq-∸ : a ≤ a' → a' ∸ a ≤ r' → ∃! _≡_ λ r → (a , r) subtypeOf-∸ (a' , r')
  r-uniq-∸ {a} {a'} {r'} a≤a' a'∸a≤r' =
    r' ∸ (a' ∸ a) , (a≤a' , m∸n≤m r' (a' ∸ a) , sym (m∸[m∸n]≡n a'∸a≤r')) , λ {r} (_ , r≤r' , a'∸a≡r'∸r) →  trans (cong (r' ∸_) a'∸a≡r'∸r) (m∸[m∸n]≡n r≤r') 

  r-uniq : a ≤ a' → a' ∸ a ≤ r' → ∃! _≡_ λ r → (a , r) subtypeOf (a' , r')
  r-uniq a≤a' a'∸a≤r' with r-uniq-∸ a≤a' a'∸a≤r'
  ... | r , sub-∸[r] , sub-∸[x]⇒x≡r = r , sub-∸⇒sub sub-∸[r] , λ sub[x] → sub-∸[x]⇒x≡r (sub⇒sub-∸ sub[x])

  _subtypeOf-∸?_ : Decidable _subtypeOf-∸_
  (a , r) subtypeOf-∸? (a' , r') = a ≤? a' ×-dec r ≤? r' ×-dec a' ∸ a Nat.≟ r' ∸ r

  _subtypeOf-≡?_ : Decidable _subtypeOf-≡_
  t subtypeOf-≡? t' with t subtypeOf-∸? t'
  ... | yes sub' = yes (sub-∸⇒sub-≡ sub')
  ... | no ¬sub' = no (λ sub-≡ → ¬sub' (sub-≡⇒sub-∸ sub-≡))

  _subtypeOf?_ : Decidable _subtypeOf_
  t subtypeOf? t' with t subtypeOf-≡? t'
  ... | yes sub-≡ = yes (sub-≡⇒sub sub-≡)
  ... | no ¬sub-≡ = no (λ sub-0 → ¬sub-≡ (sub⇒sub-≡ sub-0))

  _subtypeOf≤-+_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r0) subtypeOf≤-+ (a' , r') = ∃ λ d → (a , r0 + d) subtypeOf (a' , r')
  
  _subtypeOf≤_ : ℕ × ℕ → ℕ × ℕ → Set
  (a , r0) subtypeOf≤ (a' , r') = ∃ λ r → r0 ≤ r × (a , r) subtypeOf (a' , r')

  _subtypeOf≤?_ : Decidable _subtypeOf≤_
  (a , r0) subtypeOf≤? (a' , r') with a ≤? a' | a' ∸ a ≤? r'
  ... | no a≰a' | _ = no λ (r , r0≤r , sub) → case sub⇒sub-∸ sub of λ (a≤a' , _) → a≰a' a≤a'
  ... | _ | no a'∸a≰r' = no λ (r , r0≤r , sub) → case sub⇒sub-∸ sub of λ (a≤a' , r≤r' , a'∸a≡r'∸r) → a'∸a≰r' (≤-trans (≤-reflexive a'∸a≡r'∸r) (m∸n≤m r' r))
  ... | yes a≤a' | yes a'∸a≤r' with r-uniq a≤a' a'∸a≤r'
  ... | (r , sub-r , ∀sub-x⇒x≡r) with r0 ≤? r
  ... | no r0≰r = no λ (x , r0≤x , sub-x) → r0≰r (≤-trans r0≤x (≤-reflexive (sym (∀sub-x⇒x≡r sub-x))))
  ... | yes r0≤r = yes (r , r0≤r , sub-r)

  sub≤-+⇒sub≤ : (a , r0) subtypeOf≤-+ (a' , r') → (a , r0) subtypeOf≤ (a' , r')
  sub≤-+⇒sub≤ {r0 = r0} (rd , sub) = r0 + rd , m≤m+n r0 rd , sub

  sub≤⇒sub≤-+ : (a , r0) subtypeOf≤ (a' , r') → (a , r0) subtypeOf≤-+ (a' , r')
  sub≤⇒sub≤-+ {r0 = r0} (r , r0≤r , d , a+d≡a' , r+d≡r') = (r ∸ r0 , d , a+d≡a' , trans (cong (_+ d) ((m+[n∸m]≡n r0≤r))) r+d≡r')

  _subtypeOfW_ : ℕ × Wildcard ℕ → ℕ × Wildcard ℕ → Set
  (a , exactly r) subtypeOfW (a' , exactly r') = (a , r) subtypeOf (a' , r')
  (a , exactly r) subtypeOfW (a' , atleast r0') = ⊥
  (a , atleast r0) subtypeOfW (a' , exactly r') = (a , r0) subtypeOf≤ (a' , r')
  (a , atleast r0) subtypeOfW (a' , atleast r0') = (a , r0) subtypeOf≤ (a' , r0')

  _subtypeOfW?_ : Decidable _subtypeOfW_
  (a , exactly r) subtypeOfW? (a' , exactly r') = (a , r) subtypeOf? (a' , r')
  (a , exactly r) subtypeOfW? (a' , atleast r0') = no λ()
  (a , atleast r0) subtypeOfW? (a' , exactly r') = (a , r0) subtypeOf≤? (a' , r')
  (a , atleast r0) subtypeOfW? (a' , atleast r0') = (a , r0) subtypeOf≤? (a' , r0')

  _subtypeOfWM_ : Maybe (ℕ × Wildcard ℕ) → Maybe (ℕ × Wildcard ℕ) → Set
  _ subtypeOfWM nothing = ⊤
  just t subtypeOfWM just t' = t subtypeOfW t'
  _ subtypeOfWM _ = ⊥

  _subtypeOfWM?_ : Decidable _subtypeOfWM_
  _ subtypeOfWM? nothing = yes tt
  nothing subtypeOfWM? just _ = no id
  just t subtypeOfWM? just t' = t subtypeOfW? t' 

  subPo : IsPartialOrder _≡_ _subtypeOf_
  subPo = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ { refl →  0 , +-identityʳ _ , +-identityʳ _}
      ; trans = λ { (d , refl , refl) (d' , refl , refl) →  d + d' , sym (+-assoc _ d d') , sym (+-assoc _ d d')}
      }
    ; antisym = λ {i} {j} → λ { (d , eqa , eqr) (d' , eqa' , eqr') → let
        open ≡-Reasoning
        i₁+[d+d']≡i₁ = begin proj₁ i + (d + d') ≡⟨ sym (+-assoc _ d d') ⟩
          proj₁ i + d + d' ≡⟨ cong (_+ d') eqa ⟩
          proj₁ j + d' ≡⟨ eqa' ⟩
          proj₁ i ∎
        i₁+[d+d']≡i₁+0 = begin proj₁ i + (d + d') ≡⟨ i₁+[d+d']≡i₁ ⟩
          proj₁ i ≡⟨ sym (+-identityʳ (proj₁ i)) ⟩
          proj₁ i + 0 ∎
        d+d'≡0 = +-cancelˡ-≡ (proj₁ i) i₁+[d+d']≡i₁+0
        d≡0 = m+n≡0⇒m≡0 d d+d'≡0
        i₁≡j₁ = begin proj₁ i ≡⟨ sym (+-identityʳ (proj₁ i)) ⟩
          proj₁ i + 0 ≡⟨ cong (proj₁ i +_) (sym d≡0) ⟩
          proj₁ i + d ≡⟨ eqa ⟩
          proj₁ j ∎
        i₂≡j₂ = begin proj₂ i ≡⟨ sym (+-identityʳ (proj₂ i)) ⟩
          proj₂ i + 0 ≡⟨ cong (proj₂ i +_) (sym d≡0) ⟩
          proj₂ i + d ≡⟨ eqr ⟩
          proj₂ j ∎
        in cong₂ _,_ i₁≡j₁ i₂≡j₂
      }
    }

  _⊢_hasTypeC_ : (es : Vec ℕ n) → Code n → ℕ × ℕ → Set

  _⊢_hasTypeI_ : (es : Vec ℕ n) → Insn n → ℕ × ℕ → Set
  es ⊢ const z hasTypeI (a , suc r) = a ≡ r
  es ⊢ load v hasTypeI (a , suc r) = a ≡ r
  es ⊢ store v hasTypeI (suc a , r) = a ≡ r
  es ⊢ nop hasTypeI  (a , r) = a ≡ r
  es ⊢ not hasTypeI (suc a , suc r) = a ≡ r
  es ⊢ and hasTypeI (suc (suc a) , suc r) = a ≡ r
  es ⊢ mul hasTypeI (suc (suc a) , suc r) = a ≡ r
  es ⊢ add hasTypeI (suc (suc a) , suc r) = a ≡ r
  es ⊢ br l hasTypeI (a , r) = ∃ λ d → VecM.lookup es l + d ≡ a
  es ⊢ brif l hasTypeI (suc a , r) = a ≡ r × ∃ λ d → VecM.lookup es l + d ≡ a
  es ⊢ block (a' , r') is hasTypeI (a , r) = (a' , r') subtypeOf (a , r) × (r' ∷ es) ⊢ is hasTypeC (a' , r')
  es ⊢ loop (a' , r') is hasTypeI (a , r) = (a' , r') subtypeOf (a , r) × (a' ∷ es) ⊢ is hasTypeC (a' , r')
  es ⊢ i hasTypeI t = ⊥


  es ⊢ [] hasTypeC (a , r) = a ≡ r
  es ⊢ (i ∷ is) hasTypeC (a , r) = ∃ λ m → es ⊢ i hasTypeI (a , m) × es ⊢ is hasTypeC (m , r)

  _⊢_hasTypeCW_ : (es : Vec ℕ n) → Code n → ℕ × Wildcard ℕ → Set
  es ⊢ is hasTypeCW (a , exactly r) = es ⊢ is hasTypeC (a , r)
  es ⊢ is hasTypeCW (a , atleast r0) = ∃ λ d → es ⊢ is hasTypeC (a , r0 + d)

  _⊢_hasMinTypeI_ : (es : Vec ℕ n) → Insn n → ℕ × ℕ → Set
  es ⊢ const z hasMinTypeI (0 , 1) = ⊤
  es ⊢ load v hasMinTypeI (0 , 1) = ⊤
  es ⊢ store v hasMinTypeI (1 , 0) = ⊤
  es ⊢ nop hasMinTypeI (0 , 0) = ⊤
  es ⊢ not hasMinTypeI (1 , 1) = ⊤
  es ⊢ and hasMinTypeI (2 , 1) = ⊤
  es ⊢ mul hasMinTypeI (2 , 1) = ⊤
  es ⊢ add hasMinTypeI (2 , 1) = ⊤
  es ⊢ br l hasMinTypeI (a , r) = a ≡ VecM.lookup es l
  es ⊢ brif l hasMinTypeI (a , r) = a ≡ suc (VecM.lookup es l) × r ≡ VecM.lookup es l
  es ⊢ block (a , r) is hasMinTypeI (a' , r') = a ≡ a' × r ≡ r' × (r ∷ es) ⊢ is hasTypeC (a , r)
  es ⊢ loop (a , r) is hasMinTypeI (a' , r') = a ≡ a' × r ≡ r' × (a ∷ es) ⊢ is hasTypeC (a , r)
  es ⊢ i hasMinTypeI t = ⊥

  _⊢_hasTypeIMin_ : (es : Vec ℕ n) → Insn n → ℕ × ℕ → Set
  es ⊢ i hasTypeIMin t = ∃ λ t0 → (es ⊢ i hasMinTypeI t0) × (t0 subtypeOf t)

  hasTypeIMin⇒hasTypeI : {es : Vec ℕ n} {i : Insn n} {a : ℕ} {r : ℕ} → es ⊢ i hasTypeIMin (a , r) → es ⊢ i hasTypeI (a , r)
  hasTypeIMin⇒hasTypeI {i = const z} ((0 , 1) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = load x} ((0 , 1) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = store x} ((1 , 0) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = add} ((2 , 1) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = mul} ((2 , 1) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = and} ((2 , 1) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = not} ((1 , 1) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {i = nop} ((0 , 0) , min , _ , refl , refl) = refl
  hasTypeIMin⇒hasTypeI {es = es} {i = br l} ((.(VecM.lookup es l) , r) , refl , d , refl , refl) = d , refl
  hasTypeIMin⇒hasTypeI {es = es} {i = brif l} ((.(suc (VecM.lookup es l)) , .(VecM.lookup es l)) , (refl , refl) , d , refl , refl) = refl , d , refl 
  hasTypeIMin⇒hasTypeI {i = block (a' , r') is} ((.a' , .r') , (refl , refl , hasTypeC) , d , refl , refl) = (d , refl , refl) , hasTypeC
  hasTypeIMin⇒hasTypeI {i = loop (a' , r') is} ((.a' , .r') , (refl , refl , hasTypeC) , d , refl , refl) = (d , refl , refl) , hasTypeC
  -- converse does not hold for br

module TypeInference where
  open Syntax
  open Typing
  open import Data.Nat.Properties


  compM : ℕ × Wildcard ℕ → ℕ × Wildcard ℕ → Maybe (ℕ × Wildcard ℕ)
  compM (a , exactly r) (a' , exactly r') with a' ≤? r | r ≤? a'
  ... | no ¬a'r | no ¬ra'  = ⊥-elim (¬a'r (≰⇒≥ ¬ra'))
  ... | yes _ | _ = just (a , exactly (r' + (r ∸ a')))
  ... | _ | yes _ = just (a + (a' ∸ r) , exactly r')
  compM (a , exactly r) (a' , atleast r0') with a' ≤? r | r ≤? a'
  ... | no ¬a'r | no ¬ra'  = ⊥-elim (¬a'r (≰⇒≥ ¬ra'))
  ... | yes _ | _ = just (a , atleast (r0' + (r ∸ a')))
  ... | _ | yes _ = just (a + (a' ∸ r) , atleast r0')
  compM (a , atleast r0) (a' , exactly r') with a' ≤? r0 | r0 ≤? a'
  ... | no ¬a'r | no ¬ra'  = ⊥-elim (¬a'r (≰⇒≥ ¬ra'))
  ... | yes _ | _ = just (a , atleast (r' + (r0 ∸ a')))
  ... | _ | yes _ = just (a , atleast r')
  compM (a , atleast r0) (a' , atleast r0') with a' ≤? r0 | r0 ≤? a'
  ... | no ¬a'r | no ¬ra'  = ⊥-elim (¬a'r (≰⇒≥ ¬ra'))
  ... | yes _ | _ = just (a , atleast (r0' + (r0 ∸ a')))
  ... | _ | yes _ = just (a , atleast r0')

  liftW : ℕ × ℕ → ℕ × Wildcard ℕ
  liftW (a , r) = (a , exactly r)

  liftM : ℕ × Wildcard ℕ → Maybe (ℕ × Wildcard ℕ)
  liftM t = just t

  liftWM = liftM ∘ liftW

  castW : ℕ × Wildcard ℕ → ℕ × Wildcard ℕ → Maybe (ℕ × Wildcard ℕ)
  castW t t' = do
    _ ← decToMaybe (t subtypeOfW? t')
    just t'

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
  inferI es (block (a , r) is) = do
    t ← inferC (r ∷ es) is
    _ ← decToMaybe (t subtypeOfW? liftW (a , r))
    just (a , exactly r)

  inferI es (loop (a , r) is) = do
    t ← inferC (a ∷ es) is
    _ ← decToMaybe (t subtypeOfW? liftW (a , r))
    just (a , exactly r)

  inferC es [] = just (0 , exactly 0)

  inferC es (i ∷ is) = do
    ti ← inferI es i
    tis ← inferC es is
    compM ti tis

  example0' = (1 , 1) subtypeOf-≡? (2 , 2)
  example0 = inferI [] (block (1 , 1) (br FinM.zero ∷ []))
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

  soundnessC : ∀{a r} → (es : Vec ℕ n) → (is : Code n) → inferC es is subtypeOfWM (just (a , exactly r)) → es ⊢ is hasTypeC (a , r)
  soundnessI : ∀{a r} → (es : Vec ℕ n) → (i : Insn n) → inferI es i subtypeOfWM (just (a , exactly r)) → es ⊢ i hasTypeI (a , r)
  soundnessC es [] (_ , refl , refl) = refl
  soundnessC es (i ∷ is) inferCSub with inferI es i | inspect (inferI es) i
  ... | just (a'' , mr'') | [ eqI ] with inferC es is | inspect (inferC es) is
  soundnessC es (i ∷ is) inferCSub | just (aᵢ , exactly rᵢ) | [ eqI ] | just (aᵢ' , exactly rᵢ') | [ eqC ] with aᵢ' ≤? rᵢ | rᵢ ≤? aᵢ'
  ... | no ¬ar | no ¬ra = ⊥-elim (¬ar (≰⇒≥ ¬ra))
  soundnessC es (i ∷ is) (d , refl , refl) | just (aᵢ , exactly rᵢ) | [ eqI ] | just (aᵢ' , exactly rᵢ') | [ eqC ] | yes aᵢ'≤rᵢ | _ with m≤n⇒∃d[m+d≡n] aᵢ'≤rᵢ
  ... | dᵢ , refl = let
    subI = subst (_subtypeOfWM just (_ , exactly _)) (sym eqI) (d , refl , refl)
    subC = subst (_subtypeOfWM just (_ , exactly _)) (sym eqC) (dᵢ + d , sym (+-assoc aᵢ' _ _) , trans (sym (+-assoc rᵢ' _ _)) (cong (λ M → rᵢ' + M + d) (sym (m+n∸m≡n aᵢ' dᵢ))))
    in rᵢ + d , soundnessI es i subI , soundnessC es is subC
  soundnessC es (i ∷ is) (d , refl , refl) | just (aᵢ , exactly rᵢ) | [ eqI ] | just (aᵢ' , exactly rᵢ') | [ eqC ] | no _ | yes rᵢ≤aᵢ' with m≤n⇒∃d[m+d≡n] rᵢ≤aᵢ'
  ... | dᵢ , refl = let
    subI = subst (_subtypeOfWM just (_ , exactly _)) (sym eqI) (dᵢ + d , trans (sym (+-assoc aᵢ _ _)) (cong (λ M → aᵢ + M + d) (sym (m+n∸m≡n rᵢ dᵢ))) , sym (+-assoc rᵢ _ _))
    subC = subst (_subtypeOfWM just (_ , exactly _)) (sym eqC) (d , refl , refl)
    in  aᵢ' + d , soundnessI es i subI , soundnessC es is subC
  soundnessC es (i ∷ is) inferCSub | just (aᵢ , exactly rᵢ) | [ eqI ] | just (aᵢ' , atleast rᵢ') | [ eqC ] with aᵢ' ≤? rᵢ | rᵢ ≤? aᵢ'
  ... | no ¬ar | no ¬ra = ⊥-elim (¬ar (≰⇒≥ ¬ra))
  soundnessC es (i ∷ is) (r , r0≤ , d , refl , refl) | just (aᵢ , exactly rᵢ) | [ eqI ] | just (aᵢ' , atleast r0ᵢ') | [ eqC ] | yes aᵢ'≤rᵢ | _ with m≤n⇒∃d[m+d≡n] aᵢ'≤rᵢ | m≤n⇒∃!d[m+d≡n] r0≤
  ... | dᵢ , refl | rd , refl , _ = let
    subI = subst (_subtypeOfWM just (_ , exactly _)) (sym eqI) (d , refl , refl)
    subC = subst (_subtypeOfWM just (_ , exactly _)) (sym eqC) (sub≤-+⇒sub≤ (rd , dᵢ + d , {!!} , {!!}  ))
    in rᵢ + d , soundnessI es i subI , soundnessC es is subC
  soundnessC es (i ∷ is) (r , r≤ , d , refl , refl) | just (aᵢ , exactly rᵢ) | [ eqI ] | just (aᵢ' , atleast rᵢ') | [ eqC ] | no _ | yes rᵢ≤aᵢ' = {!!}
  soundnessC es (i ∷ is) inferCSub | just (a , atleast r) | [ eqI ] | just (a' , exactly r') | [ eqC ] = {!!}
  soundnessC es (i ∷ is) inferCSub | just (a , atleast r) | [ eqI ] | just (a' , atleast r') | [ eqC ] = {!!}

  soundnessI es (const z) (_ , refl , refl) = refl
  soundnessI es (load x) (_ , refl , refl) = refl
  soundnessI es (store x) (_ , refl , refl) = refl
  soundnessI es add (_ , refl , refl) = refl
  soundnessI es mul (_ , refl , refl) = refl
  soundnessI es and (_ , refl , refl) = refl
  soundnessI es not (_ , refl , refl) = refl
  soundnessI es nop (_ , refl , refl) = refl
  soundnessI es (br l) (_ , _ , d , es!!l+d≡a , _) = d , es!!l+d≡a
  soundnessI {a = suc a} es (brif l) (d , s[es!!l+d]≡sa , refl) with suc-injective s[es!!l+d]≡sa
  ... | refl = refl , d , refl
  soundnessI es (block (a' , r') is) inferISub with inferC (r' ∷ es) is | inspect (inferC  (r' ∷ es)) is
  ... | just (a'' , mr'') | [ eq ] with (a'' , mr'') subtypeOfW? (a' , exactly r')
  soundnessI es (block (a' , r') is) sub | just (a , exactly r) | [ eq ] | yes sub' =
    sub , soundnessC (r' ∷ es) is (subst (_subtypeOfWM liftWM (a' , r')) (sym eq) sub')
  soundnessI es (block (a' , r') is) sub | just (a , atleast r0) | [ eq ] | yes sub≤' =
    sub , soundnessC (r' ∷ es) is (subst (_subtypeOfWM liftWM (a' , r')) (sym eq) sub≤')
  soundnessI es (loop (a' , r') is) inferISub with inferC (a' ∷ es) is | inspect (inferC  (a' ∷ es)) is
  ... | just (a'' , mr'') | [ eq ] with (a'' , mr'') subtypeOfW? (a' , exactly r')
  soundnessI es (loop (a' , r') is) sub | just (a , exactly r) | [ eq ] | yes sub' =
    sub , soundnessC (a' ∷ es) is (subst (_subtypeOfWM liftWM (a' , r')) (sym eq) sub')
  soundnessI es (loop (a' , r') is) sub | just (a , atleast r0) | [ eq ] | yes sub≤' =
    sub , soundnessC (a' ∷ es) is (subst (_subtypeOfWM liftWM (a' , r')) (sym eq) sub≤')

{-
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
{-
    ⟦_⟧I : (i : Insn n) → {a r : ℕ} → {es : Vec ℕ n} → es ⊢ i hasTypeI (a , r) → Cfg a → Cfg r ⊎ Lbls es
    ⟦_⟧C : (is : Code n) → {a r : ℕ} → {es : Vec ℕ n} → es ⊢ is hasTypeC (a , r) → Cfg a → Cfg r ⊎ Lbls es

    ⟦ .(const z) ⟧I (tconst {z}) (sto , []) =  inj₁ (sto , z ∷ [])
    ⟦ .(load v) ⟧I (tload {v}) (sto , []) = inj₁ (sto , lookupS v sto ∷ [])
    ⟦ .(store v) ⟧I (tstore {v}) (sto , z ∷ []) = inj₁ (updateS v z sto , [])
    ⟦ .nop ⟧I tnop (sto , []) = inj₁ (sto , [])
    ⟦ .not ⟧I tnot (sto , z ∷ []) = inj₁ (sto , castB' (BoolM.not (castB z)) ∷ [])
    ⟦ .and ⟧I tand (sto , z ∷ z' ∷ []) = inj₁ (sto , castB' (castB z ∧ castB z') ∷ [])
    ⟦ .mul ⟧I tmul (sto , z ∷ z' ∷ []) =  inj₁ (sto , z IntM.* z' ∷ []) 
    ⟦ .add ⟧I tadd (sto , z ∷ z' ∷ []) = inj₁ (sto , z IntM.+ z' ∷ [])
    -- stack in cfg contains as much as `br` needs.
    ⟦ br l ⟧I tbr cfg = inj₂ (injL cfg)
    ⟦ brif l ⟧I tbrif (sto , z ∷ ostk) =
      if castB z
      then inj₁ (sto , ostk)
      else inj₂ (injL (sto , ostk))
    ⟦ block a r is ⟧I (tblock is-hasTypeC) cfg with ⟦ is ⟧ is-hasTypeC cfg
    ... | inj₁ cfg' = inj₁ cfg'
    ... | inj₂ (inj₁ cfg') = inj₁ cfg'
    ... | inj₂ (inj₂ outer) = inj₂ outer
    ⟦ loop a r is ⟧I (tloop is-hasTypeC) cfg with ⟦ is ⟧ is-hasTypeC cfg
    ... | inj₁ cfg' = inj₁ cfg'
    ... | inj₂ (inj₁ cfg') = ⟦ loop a r is ⟧i (tloop is-hasTypeC) cfg'
    ... | inj₂ (inj₂ outer) = inj₂ outer

    ⟦ .[] ⟧C [] cfg = inj₁ cfg
    -- Sequential composition ⟦ i ∷ is ⟧ provides only minimum footprint for ⟦ i ⟧i, i.e. it provides (VecM.take a0 ostk) for `i` and keeps (VecM.drop a0 ostk) for subsequent instructions `is` 
    -- This can be done because we know the minimum footprint `a0` for `i` by `hasMinTypeI` predicate.
    -- If the evaluation of `i` normally goes in current frame, then we take back `VecM.drop a0 ostk` under `ostk'` which is production of `i`.
    -- If the evaluation of `i` jump outside, then `VecM.drop a0 ostk` will be lost.
    -- Sequencial composition only give minimum footprint for `br l` instruction too.
    -- Here, `es !! l` corresponds to the minumum footprint for `br l`.
    -- So `br` instruction itself does not need to do something like spliting local stack or discarding stack elements.
    ⟦ i ∷ is ⟧C (((a0 , r0) , i-hasMinTypeI , (d , .d) , refl , refl , refl) ∷ tis) (sto , ostk) with ⟦ i ⟧i i-hasMinTypeI (sto , VecM.take a0 ostk)
    ... | inj₁ (sto' , ostk') = ⟦ is ⟧ tis (sto' , ostk' VecM.++ (VecM.drop a0 ostk))
    ... | inj₂ lbls = inj₂ lbls

-}

  ⟦_⟧vt : Wildcard ℕ → Set
  ⟦ exactly r ⟧vt = Cfg r
  ⟦ atleast r0 ⟧vt = ∀ r → r0 ≤ r → Cfg r

  ⟦_⟧ft : Wildcard ℕ × Wildcard ℕ → Set
  ⟦ a , r ⟧ft = ∀ d → ⟦ up d a ⟧vt → ⟦ up d r ⟧vt where
    up : ℕ → Wildcard ℕ → Wildcard ℕ
    up n (exactly r) = exactly (r + n)
    up n (atleast r0) = atleast (r0 + n)
