module MiniWasm6 (Var : Set) where

open import Data.Maybe as MaybeM
open import Function hiding (const)
open import Data.Integer as IntM hiding (_+_ ; suc ; _≤_ ; _≤?_ ; +_ ; _⊔_ ; _≰_)
open import Data.Nat as Nat
open import Data.Bool as BoolM hiding (not ; _≤_ ; _≤?_)
open import Data.Unit hiding (_≤_ ;  _≤?_)
open import Data.Product
open import Data.Fin as FinM hiding (_+_ ; _≤_ ; _≤?_)
open import Data.Vec as VecM hiding (_++_ ; length ; _>>=_) renaming (lookup to _!!_)
open import Data.List as ListM hiding (and)
open import Relation.Binary.PropositionalEquality as ≡M
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

  +0-id : ∀ {m} → m + 0 ≡ m
  +0-id {m} = +-identityʳ m

  +0-id' : ∀{m} → m ≡ m + 0
  +0-id' {m} = sym (+-identityʳ m)

  +-assoc' : ∀{m} n o → m + (n + o) ≡ m + n + o
  +-assoc' {m} n o = sym (+-assoc m n o)

  +-assoc'-pair : ∀{a r} d d' e e' → (a + (d + d') , r + (e + e')) ≡ (a + d + d' , r + e + e') 
  +-assoc'-pair d d' e e' = cong₂ _,_ (sym (+-assoc _ d d')) (sym (+-assoc _ e e'))

  m+n≡o⇒m≤o : ∀ {m n o : ℕ} → m + n ≡ o → m ≤ o
  m+n≡o⇒m≤o m+n≡o = m+n≤o⇒m≤o _ (≤-reflexive m+n≡o)

  m+d≡n⇒m∸n≡d : m + d ≡ n → n ∸ m ≡ d
  m+d≡n⇒m∸n≡d {m} refl = m+n∸m≡n m _

  m+n+o≡m⇒n≡0 : ∀{m n o} → m + n + o ≡ m → n ≡ 0
  m+n+o≡m⇒n≡0 {m} {n} {o} m+n+o≡m =  let
    open ≡-Reasoning
    m+[n+o]≡m+0 = begin
      m + (n + o) ≡⟨ +-assoc' n o ⟩
      m + n + o ≡⟨ m+n+o≡m ⟩
      m ≡⟨ +0-id' ⟩
      m + 0 ∎
    n+o≡0 = +-cancelˡ-≡ m m+[n+o]≡m+0
    n≡0 = m+n≡0⇒m≡0 n n+o≡0
    in n≡0

  m+n+o≡m+p⇒n+o≡p : ∀ m {n o p} → m + n + o ≡ m + p → n + o ≡ p
  m+n+o≡m+p⇒n+o≡p m m+n+o≡m+p = +-cancelˡ-≡ m (trans (sym (+-assoc m _ _)) m+n+o≡m+p)

  n+o≡p⇒m+n+o≡m+p : ∀ m {n o p} → n + o ≡ p → m + n + o ≡ m + p
  n+o≡p⇒m+n+o≡m+p m n+o≡p = trans (+-assoc m _ _) (cong (m +_) n+o≡p)

  ≤-diff : ∀{m n} → m ≤ n → m + (n ∸ m) ≡ n
  ≤-diff m≤n = m+[n∸m]≡n m≤n

  ≤-diff' : ∀{m n} → m ≤ n → n ≡ m + (n ∸ m)
  ≤-diff' m≤n = sym (m+[n∸m]≡n m≤n)

  -- type for stack height extension
  data Q : Set where
    uni : Q -- in/out stack height maintains balance sub performs
    bi : Q -- unbalanced growing

  conj : Q → Q → Q
  conj uni uni = uni
  conj _ _ = bi

  uniExt uniExt≤ : ℕ × ℕ → ℕ × ℕ → Set
  uniExt (a , r) (a' , r') = ∃ λ d → a + d ≡ a' × r + d ≡ r'
  uniExt≤ (a , r) (a' , r') = a ≤ a' × r ≤ r' × a' ∸ a ≡ r' ∸ r

  biExt biExt≤ : ℕ × ℕ → ℕ × ℕ → Set
  biExt (a , r) (a' , r') = ∃₂ λ d e → a + d ≡ a' × r + e ≡ r'
  biExt≤ (a , r) (a' , r') = a ≤ a' × r ≤ r'

  ext : Q → ℕ × ℕ → ℕ × ℕ → Set
  ext uni = uniExt
  ext bi = biExt

  uniExt⇒uniExt≤ : ∀{t t'} → uniExt t t' → uniExt≤ t t'
  uniExt⇒uniExt≤ {t = (a , r)} (d , a+d≡a' , r+d≡r') =
    (m+n≡o⇒m≤o a+d≡a') , (m+n≡o⇒m≤o r+d≡r') , trans (m+d≡n⇒m∸n≡d {m = a} a+d≡a') (sym (m+d≡n⇒m∸n≡d {m = r} r+d≡r')) 

  uniExt≤⇒uniExt : ∀{t t'} → uniExt≤ t t' → uniExt t t'
  uniExt≤⇒uniExt {t = (a , r)} {t' = (a' , r')} (a≤a' , r≤r' , a'∸a≡r'∸r) = a' ∸ a , m+[n∸m]≡n a≤a' , trans (cong (r +_ ) (a'∸a≡r'∸r)) (m+[n∸m]≡n r≤r')

  uniExt? : Decidable uniExt
  uniExt? (a , r) (a' , r') with a ≤? a' ×-dec r ≤? r' ×-dec a' ∸ a Nat.≟ r' ∸ r
  ... | no np = no λ p → np (uniExt⇒uniExt≤ p)
  ... | yes p = yes (uniExt≤⇒uniExt p)

  biExt⇒biExt≤ : ∀{t t'} → biExt t t' → biExt≤ t t'
  biExt⇒biExt≤ (d , e , a+d≡a' , r+e≡r') = (m+n≡o⇒m≤o a+d≡a' , m+n≡o⇒m≤o r+e≡r')

  biExt≤⇒biExt : ∀{t t'} → biExt≤ t t' → biExt t t'
  biExt≤⇒biExt (a≤a' , r≤r') = let
    (d , a+d≡a') = m≤n⇒∃d[m+d≡n] a≤a'
    (e , r+e≡r') = m≤n⇒∃d[m+d≡n] r≤r'
    in (d , e , a+d≡a' , r+e≡r')

  biExt? : Decidable biExt
  biExt? (a , r) (a' , r') with  a ≤? a' ×-dec r ≤? r'
  ... | no np = no λ p → np (biExt⇒biExt≤ p)
  ... | yes p = yes (biExt≤⇒biExt p)

  uniExt⇒biExt : ∀{t t'} → uniExt t t' → biExt t t'
  uniExt⇒biExt (d , refl , refl) = d ,  d  , refl , refl

  data _≤Q_ : Q → Q → Set where
    uni≤uni : uni ≤Q uni
    bi≤q : ∀ {q} → bi ≤Q q

  _≤Q?_ : Decidable _≤Q_
  uni ≤Q? uni = yes uni≤uni
  bi ≤Q? q = yes bi≤q 
  uni ≤Q? bi = no λ()
  
  data _<:_ : Q × ℕ × ℕ → Q × ℕ × ℕ → Set where
    <:-intro : ∀ {q t t' q'} → ext q t t' → q ≤Q q' → (q , t) <: (q' , t')

  _<:?_ : Decidable _<:_
  (uni , t) <:? (uni , t') with uniExt? t t'
  ... | yes p = yes (<:-intro p uni≤uni)
  ... | no ¬p = no λ{(<:-intro p uni≤uni) → ¬p p}
  (bi , t) <:? (q , t') with biExt? t t'
  ... | yes p = yes (<:-intro p bi≤q)
  ... | no ¬p = no λ{(<:-intro p bi≤q) → ¬p p}
  (uni , t) <:? (bi , t') = no λ{(<:-intro p ())}

  data _<:M_ : Maybe (Q × ℕ × ℕ) → Maybe (Q × ℕ × ℕ) → Set where
    top : ∀{qt} → qt <:M nothing
    sub : ∀{qt qt'} → qt <: qt' → just qt <:M just qt'

  _<:M?_ : Decidable _<:M_
  _ <:M? nothing = yes top
  just qt <:M? just qt' with qt <:? qt'
  ... | yes p = yes (sub p)
  ... | no ¬p = no λ{(sub p) → ¬p p}
  nothing <:M? just _ = no λ()

  data _∈_ : ℕ × ℕ → Q × ℕ × ℕ → Set where
     ∈-intro : ∀{t t0} → (q : Q) → ext q t0 t → t ∈ (q , t0) 
  {-
    uni : ∀{t t0} → uniExt t0 t → t ∈ (uni , t0)
    bi : ∀{t t0} → biExt t0 t → t ∈ (bi , t0)
  -}

  data _∈M_ : ℕ × ℕ → Maybe (Q × ℕ × ℕ) → Set where
    sub : ∀{t qt} → t ∈ qt → t ∈M just qt

  ∈⇒<:uni : ∀{t qt} → t ∈ qt → qt <: (uni , t)
  ∈⇒<:uni (∈-intro uni p) = <:-intro p uni≤uni
  ∈⇒<:uni (∈-intro bi p) = <:-intro p bi≤q

  <:uni⇒∈ : ∀{t qt} → qt <: (uni , t) → t ∈ qt 
  <:uni⇒∈ (<:-intro p uni≤uni) = ∈-intro _ p
  <:uni⇒∈ (<:-intro p bi≤q) = ∈-intro _ p

  min∈ : (qt : Q × ℕ × ℕ) → let (_ , t) = qt in t ∈ qt
  min∈ (uni , a , r) = ∈-intro uni (0 , +0-id , +0-id)
  min∈ (bi , a , r) = ∈-intro bi (0 , 0 , +0-id , +0-id)

  +d+d∈ : (d : ℕ) → (qt : Q × ℕ × ℕ) → let (_ , a , r) = qt in (a + d , r + d) ∈ qt
  +d+d∈ d (uni , a , r) = ∈-intro uni (d , refl , refl)
  +d+d∈ d (bi , a , r) = ∈-intro bi (d , d , refl , refl)

  +d+e∈ : (d e : ℕ) → (t : ℕ × ℕ) → let (a , r) = t in (a + d , r + e) ∈ (bi , a , r)
  +d+e∈ d e (a , r) = ∈-intro bi (d , e , refl , refl)

  qt<:uni : (qt : Q × ℕ × ℕ) → qt <: (uni , proj₂ qt)
  qt<:uni (uni , a , r) = <:-intro (0 , +0-id , +0-id) _
  qt<:uni (bi , a , r) = <:-intro (0 , 0 , +0-id , +0-id) _

  preGap : ∀{a r q a' r'} → ((a' , r') ∈ (q , a , r)) → ∃ λ d → (a + d ≡ a')
  preGap (∈-intro uni (d , a+d≡a' , _)) = d , a+d≡a'
  preGap (∈-intro bi (d , _ , a+d≡a' , _)) = d , a+d≡a'

  postGap : ∀{a r q a' r'} → ((a' , r') ∈ (q , a , r)) → ∃ λ e → (r + e ≡ r')
  postGap (∈-intro uni (e , _ , r+e≡r')) = e , r+e≡r'
  postGap (∈-intro bi (_ , e , _ , r+e≡r')) = e , r+e≡r'

  +d+d∈' : {t' : ℕ × ℕ} → (qt : Q × ℕ × ℕ) → (d : ℕ) → let (a' , r') = t' in let (_ , a , r) = qt in a + d ≡ a' → r + d ≡ r' → (a' , r') ∈ qt
  +d+d∈' (uni , t) d a+d≡a' r+d≡r' = ∈-intro uni (d , a+d≡a' , r+d≡r')
  +d+d∈' (bi , t) d a+d≡a' r+d≡r' = ∈-intro bi (d , d , a+d≡a' , r+d≡r')

  uniExt-isPreorder : IsPreorder _≡_ uniExt
  uniExt-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ { refl → 0 , +0-id , +0-id}
    ; trans = λ { (d , refl , refl) (d' , refl , refl) → d + d' , +-assoc' d d' , +-assoc' d d' }
    }
  biExt-isPreorder : IsPreorder _≡_ biExt
  biExt-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ {refl → (0 , 0 , +0-id , +0-id )}
    ; trans = λ { (d , e , refl , refl) (d' , e' , refl , refl) → d + d' , e + e' , +-assoc' d d' , +-assoc' e e'}
    }
 
  <:-isPreorder : IsPreorder _≡_ _<:_
  <:-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ
      { {uni , _} refl → <:-intro (uniM.reflexive refl) uni≤uni
      ; {bi , _} {q , _} refl → <:-intro (biM.reflexive refl) bi≤q
      }
    ; trans = λ
      { (<:-intro  ij uni≤uni) (<:-intro jk uni≤uni) → <:-intro (IsPreorder.trans uniExt-isPreorder ij jk) uni≤uni
      ; (<:-intro ij bi≤q) (<:-intro {uni} jk uni≤uni) → <:-intro (IsPreorder.trans biExt-isPreorder ij (uniExt⇒biExt jk)) bi≤q
      ; (<:-intro ij bi≤q) (<:-intro jk bi≤q) → <:-intro (IsPreorder.trans biExt-isPreorder ij jk) bi≤q
      }
    } where
    module uniM = IsPreorder uniExt-isPreorder
    module biM = IsPreorder biExt-isPreorder

  <:M-isPreorder : IsPreorder _≡_ _<:M_
  <:M-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ
      { {nothing} refl → top
      ; {just _} refl → sub (IsPreorder.reflexive <:-isPreorder refl)
      }
    ; trans = λ
      { {_} {_} {nothing} _ _ → top
      ; {just _} {just _} {just _} (sub ij) (sub jk) → sub (IsPreorder.trans <:-isPreorder ij jk)
      }
    }

  -- _:Cm_ _:Im_ 
  -- Wasm specification style definition 
  -- Every single nstruction (except stack polymorhic e.g. br l) has only minimum type
  -- The typing rule for the empty instructions extends its type along with stack
  -- The typing rule for composition adjusts the type for single instruction
  data _⊢_:Cm_ (es : Vec ℕ n) : Code n → ℕ × ℕ → Set

  data _⊢_:Im_ (es : Vec ℕ n) : Insn n → ℕ × ℕ → Set where
    const : es ⊢ const z :Im (0 , 1)
    load : es ⊢ load v :Im (0 , 1)
    store : es ⊢ store v :Im (1 , 0)
    nop : es ⊢ nop :Im  (0 , 0)
    not : es ⊢ not :Im (1 , 1)
    and : es ⊢ and :Im (2 , 1)
    mul : es ⊢ mul :Im (2 , 1)
    add : es ⊢ add :Im (2 , 1)
    br : (l : Fin n) → (d e : ℕ ) → es ⊢ br l :Im (es !! l + d , e)
    brif : (l : Fin n) → es ⊢ brif l :Im (suc (es !! l) , es !! l)
    block : {is : Code (suc n)} → (t : ℕ × ℕ) → let (a , r) = t in (r ∷ es) ⊢ is :Cm (a , r) → es ⊢ block (a , r) is :Im (a , r)
    loop : {is : Code (suc n)} → (t : ℕ × ℕ) → let (a , r) = t in (a ∷ es) ⊢ is :Cm (a , r) → es ⊢ loop (a , r) is :Im (a , r)

  data _⊢_:Cm_ es where
    [] : es ⊢ [] :Cm (a , a)
    comp : ∀{i is a1 r1 a2 r2 a1+d d}
      → a2 ≡ r1 + d 
      → a1+d ≡ a1 + d
      → es ⊢ i :Im (a1 , r1)
      → es ⊢ is :Cm (a2 , r2)
      → es ⊢ (i ∷ is) :Cm (a1+d , r2)

  -- Direct definition _:Cd_ _:Id_ 
  -- Every instruction is polymorphic
  -- compositions are degined by direct mediating stack type
  data _⊢_:Cd_ (es : Vec ℕ n) : Code n → ℕ × ℕ → Set
  data _⊢_:Id_ (es : Vec ℕ n) : Insn n → ℕ × ℕ → Set where -- direct typing
    const : (d : ℕ) → es ⊢ const z :Id (d , suc d)
    load : (d : ℕ) →  es ⊢ load v :Id (d , suc d)
    store : (d : ℕ) → es ⊢ store v :Id (suc d , d)
    nop : (d : ℕ) → es ⊢ nop :Id (d , d)
    not : (d : ℕ) → es ⊢ not :Id (suc d , suc d)
    and : (d : ℕ) → es ⊢ and :Id (suc (suc d) , suc d)
    mul : (d : ℕ) → es ⊢ mul :Id (suc (suc d) , suc d)
    add : (d : ℕ) → es ⊢ add :Id (suc (suc d) , suc d)
    br : (l : Fin n) → (d e : ℕ) → es ⊢ br l :Id (es !! l + d , e)
    brif : (l : Fin n) → (d : ℕ) →  es ⊢ brif l :Id (suc (es !! l) + d , es !! l + d)
    block : {is : Code (suc n)} → (t : ℕ × ℕ) → let (a , r) = t in (r ∷ es) ⊢ is :Cd (a , r) → (d : ℕ) → es ⊢ block (a , r) is :Id (a + d , r + d)
    loop :  {is : Code (suc n)} → (t : ℕ × ℕ) → let (a , r) = t in (a ∷ es) ⊢ is :Cd (a , r) → (d : ℕ) → es ⊢ loop (a , r) is :Id (a + d , r + d)

  data _⊢_:Cd_ es where -- direct typing
    [] : (d : ℕ) →  es ⊢ [] :Cd (d , d)
    _∷[_]_ : ∀{i is a1 r1 a2 r2} → es ⊢ i :Id (a1 , r1) → r1 ≡ a2 → es ⊢ is :Cd (a2 , r2) → es ⊢ (i ∷ is) :Cd (a1 , r2)

  data _⊢_:Cs_ (es : Vec ℕ n) : Code n → Q × ℕ × ℕ → Set
  data _⊢_:Is_ (es : Vec ℕ n) : Insn n → Q × ℕ × ℕ → Set where -- direct typing with extention
    const : es ⊢ const z :Is (uni , 0 , 1)
    load : es ⊢ load v :Is (uni , 0 , 1)
    store : es ⊢ store v :Is (uni , 1 , 0)
    nop : es ⊢ nop :Is (uni , 0 , 0)
    not : es ⊢ not :Is (uni , 1 , 1)
    and : es ⊢ and :Is (uni , 2 , 1)
    mul : es ⊢ mul :Is (uni , 2 , 1)
    add : es ⊢ add :Is (uni , 2 , 1)
    br : (l : Fin n) → es ⊢ br l :Is (bi , es !! l , 0)
    brif : (l : Fin n) →  es ⊢ brif l :Is (uni , suc (es !! l) , es !! l)
    block : {is : Code (suc n)} → (qt : Q × ℕ × ℕ) → let (q , a , r) = qt
      in (r ∷ es) ⊢ is :Cs (q , a , r) → es ⊢ block (a , r) is :Is (uni , a , r)
    loop :  {is : Code (suc n)} → (qt : Q × ℕ × ℕ) → let (q , a , r) = qt
      in (a ∷ es) ⊢ is :Cs (q , a , r) → es ⊢ loop (a , r) is :Is (uni , a , r)

    sub : ∀{i qt qt'} →
      es ⊢ i :Is qt → qt <: qt' → es ⊢ i :Is qt'


  data _⊢_:Cs_ es where -- direct typing
    [] : es ⊢ [] :Cs (uni , 0 , 0)
    comp :  ∀{i is q1 q2 a1 r1 a2 r2}
      → es ⊢ i :Is (q1 , a1 , r1)
      → r1 ≡ a2
      → es ⊢ is :Cs (q2 , a2 , r2)
      → es ⊢ (i ∷ is) :Cs (conj q1 q2 , a1 , r2)
  {-
    comp-uni : ∀{i is a1 r1 a2 r2}
      → es ⊢ i :Is (uni , a1 , r1)
      → r1 ≡ a2
      → es ⊢ is :Cs (uni , a2 , r2)
      → es ⊢ (i ∷ is) :Cs (uni , a1 , r2)
    comp-bir : ∀{g1 i is a1 r1 a2 r2}
      → es ⊢ i :Is (g1 , a1 , r1)
      → r1 ≡ a2
      → es ⊢ is :Cs (bi , a2 , r2)
      → es ⊢ (i ∷ is) :Cs (bi , a1 , r2)
    comp-bil : ∀{g2 i is a1 r1 a2 r2}
      → es ⊢ i :Is (bi , a1 , r1)
      → r1 ≡ a2
      → es ⊢ is :Cs (g2 , a2 , r2)
      → es ⊢ (i ∷ is) :Cs (bi , a1 , r2)
    -}
    sub : ∀{is qt qt'} → es ⊢ is :Cs qt → qt <: qt' → es ⊢ is :Cs qt'


module TypeInference where
  open Syntax
  open Typing
  open import Data.Nat.Properties

  f1 : Q → ℕ → ℕ → ℕ
  f1 uni r1 a2 = a2 ∸ r1
  f1 bi r1 a2 = 0
  f2 : Q → ℕ → ℕ → ℕ
  f2 uni r1 a2 = r1 ∸ a2
  f2 bi r1 a2 = 0

  compM' : Q × ℕ × ℕ → Q × ℕ × ℕ → Q × ℕ × ℕ
  compM' (q1 , a1 , r1) (q2 , a2 , r2) = (conj q1 q2 , a1 + f1 q1 r1 a2 , r2 + f2 q2 r1 a2) where

 {-
  compM' (bi , a1 , r1) (bi , a2 , r2) = (bi , a1 + 0 , r2 + 0) 
  compM' (bi , a1 , r1) (uni , a2 , r2) = (bi , a1 + 0 , r2 + (r1 ∸ a2))
  compM' (uni , a1 , r1) (bi , a2 , r2) = (bi , a1 + (a2 ∸ r1) , r2 + 0)
  compM' (uni , a1 , r1) (uni , a2 , r2) = (uni , a1 + (a2 ∸ r1) , r2 + (r1 ∸ a2))
-}

  compM : Q × ℕ × ℕ → Q × ℕ × ℕ → Maybe (Q × ℕ × ℕ)
  compM (g1 , a1 , r1) (g2 , a2 , r2) with a2 ≤? r1 | r1 ≤? a2
  ... | no ¬a2≤r1 | no ¬r1≤a2 = ⊥-elim (¬a2≤r1 (≰⇒≥ ¬r1≤a2))
  compM (g1 , a1 , r1) (uni , a2 , r2) | yes a2≤r1 | _ = just (g1 , a1 ,  r2 + (r1 ∸ a2))
  compM (_ , a1 , r1) (bi , a2 , r2) | yes a2≤r1 | _ = just (bi , a1 , r2)
  compM (uni , a1 , r1) (g2 , a2 , r2) | no _ | yes r1≤a2 = just (g2 , a1 + (a2 ∸ r1) , r2)
  compM (bi , a1 , r1) (_ , a2 , r2) | no _ | yes r1≤a2 = just (bi , a1 , r2)

  inferI : Vec ℕ n → Insn n → Maybe (Q × ℕ × ℕ)
  inferC : Vec ℕ n → Code n → Maybe (Q × ℕ × ℕ)

  inferI es (const z) = just (uni , 0 , 1)
  inferI es (load x) = just (uni , 0 , 1)
  inferI es (store x) = just (uni , 1 , 0)
  inferI es add = just (uni , 2 , 1)
  inferI es mul = just (uni , 2 , 1)
  inferI es and = just (uni , 2 , 1)
  inferI es not = just (uni , 1 , 1)
  inferI es nop = just (uni , 0 , 0)
  inferI es (br l) = let
    e = VecM.lookup es l
    in just (bi , e , 0)
  inferI es (brif l) = let
    e = VecM.lookup es l
    in just (uni , suc e , e)
  inferI es (block (a , r) is) = do
    t ← inferC (r ∷ es) is
    _ ← decToMaybe (t <:? (uni , a , r))
    just (uni , a , r)
  inferI es (loop (a , r) is) = do
    t ← inferC (a ∷ es) is
    _ ← decToMaybe (t <:? (uni , a , r))
    just (uni , a , r)
  inferC es [] = just (uni , 0 , 0)
  inferC es (i ∷ is) = do
    ti ← inferI es i
    tis ← inferC es is
    just (compM' ti tis)

  example0' = (uni , 1 , 1) <:? (uni , 2 , 2)
  example0 = inferI [] (block (1 , 1) (br FinM.zero ∷ []))
  example1 = inferI (1 ∷ []) (br FinM.zero)
  example2 = inferC (1 ∷ []) (br FinM.zero ∷ [])

  Cd⇒Cm : {es : Vec ℕ n} → {t : ℕ × ℕ} → {is : Code n} → es ⊢ is :Cd t → es ⊢ is :Cm t
  Cd⇒Cm ([] _) = []
  Cd⇒Cm (ti ∷[ refl ] tis) with Cd⇒Cm tis
  Cd⇒Cm (const _ ∷[ refl ] _) | tis' = comp refl refl const tis'
  Cd⇒Cm (load _ ∷[ refl ] _) | tis' = comp refl refl load tis'
  Cd⇒Cm (store _ ∷[ refl ] _) | tis' = comp refl refl store tis'
  Cd⇒Cm (nop _ ∷[ refl ] _) | tis' = comp refl refl nop tis'
  Cd⇒Cm (not d ∷[ refl ] _) | tis' = comp refl refl not tis'
  Cd⇒Cm (and d ∷[ refl ] _) | tis' = comp refl refl and tis'
  Cd⇒Cm (mul d ∷[ refl ] _) | tis' = comp refl refl mul tis'
  Cd⇒Cm (add d ∷[ refl ] _) | tis' = comp refl refl add tis'
  Cd⇒Cm (br l d e ∷[ refl ] _) | tis' = comp {d = 0} +0-id' +0-id' (br l d e) tis'
  Cd⇒Cm (brif l d ∷[ refl ] _) | tis' = comp refl refl (brif l) tis'
  Cd⇒Cm (block (a' , r') tis d ∷[ refl ] _) | tis' = comp refl refl (block _ (Cd⇒Cm tis)) tis' 
  Cd⇒Cm (loop (a' , r') tis d ∷[ refl ] _) | tis' = comp refl refl (loop _ (Cd⇒Cm tis)) tis'

  Cm⇒Cd : {es : Vec ℕ n} → {t : ℕ × ℕ} → {is : Code n} → es ⊢ is :Cm t → es ⊢ is :Cd t
  Cm⇒Cd [] = [] _
  Cm⇒Cd (comp refl refl ti tis) with Cm⇒Cd tis
  Cm⇒Cd (comp refl refl const _) | tis' = const _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl load _) | tis' = load _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl store _) | tis' = store _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl nop _) | tis' = nop _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl not _) | tis' = not _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl and _) | tis' = and _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl mul _) | tis' = mul _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl add _) | tis' = add _ ∷[ refl ] tis'
  Cm⇒Cd {es = es} {t = .((es !! l) + d + d' , _)} (comp {d = d'} refl refl (br l d e) _) | tis' rewrite +-assoc (es !! l) d d' =
    br l _ _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl (brif l) _) | tis' = brif l _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl (block (a' , r') tis) _) | tis' = block _ (Cm⇒Cd tis) _ ∷[ refl ] tis'
  Cm⇒Cd (comp refl refl (loop (a' , r') tis) _) | tis' = loop _ (Cm⇒Cd tis) _ ∷[ refl ] tis'

  soundsubC : ∀{qt t} → {es : Vec ℕ n} → {is : Code n} → es ⊢ is :Cs qt → t ∈ qt → es ⊢ is :Cd t
  soundsubI : ∀{qt t} → {es : Vec ℕ n} → {i : Insn n} → es ⊢ i :Is qt → t ∈ qt → es ⊢ i :Id t
  soundsubI const (∈-intro uni (d , refl , refl)) = const d
  soundsubI load (∈-intro uni (d , refl , refl)) = load d
  soundsubI store (∈-intro uni (d , refl , refl)) = store d
  soundsubI nop (∈-intro uni (d , refl , refl)) = nop d
  soundsubI not (∈-intro uni (d , refl , refl)) = not d
  soundsubI and (∈-intro uni (d , refl , refl)) = and d
  soundsubI mul (∈-intro uni (d , refl , refl)) = mul d
  soundsubI add (∈-intro uni (d , refl , refl)) = add d
  soundsubI (br l) (∈-intro bi (d , e , refl , refl)) = br l d e
  soundsubI (brif l) (∈-intro uni (d , refl , refl)) = brif l d
  soundsubI (block (q , a , r) tis) (∈-intro uni (d , refl , refl)) = block (a , r) (soundsubC tis (min∈ (q , a , r))) d
  soundsubI (loop (q , a , r) tis) (∈-intro uni (d , refl , refl)) = loop (a , r) (soundsubC tis (min∈ (q , a , r))) d 
  soundsubI (sub {qt = uni , a , r} ti (<:-intro {uni} (d' , refl , refl) _)) (∈-intro uni (d , refl , refl)) rewrite +-assoc a d' d | +-assoc r d' d =
    soundsubI ti (+d+d∈ (d' + d) (uni , a , r))
  soundsubI (sub {qt = bi , a , r} ti (<:-intro {bi} (d' , e' , refl , refl) _)) (∈-intro uni (d , refl , refl)) rewrite +-assoc a d' d | +-assoc r e' d =
    soundsubI ti (+d+e∈ (d' + d) (e' + d) (a , r))
  soundsubI (sub {qt = .bi , a , r} ti (<:-intro {bi} (d' , e' , refl , refl) _)) (∈-intro bi (d , e , refl , refl)) rewrite +-assoc a d' d | +-assoc r e' e =
    soundsubI ti (+d+e∈ (d' + d) (e' + e) (a , r))

{-
  soundsubC [] (uni (d , refl , refl)) = [] d
  soundsubC (comp-uni ti refl tis) (uni (d , refl , refl)) =
    soundsubI ti (uni (d , refl , refl)) ∷[ refl ] soundsubC tis (uni (d , refl , refl))
  soundsubC (comp-bil {g2} {r1 = r1} {r2 = r2} ti refl tis) (bi (d , e , refl , refl)) =
    soundsubI ti (bi (d , e , refl , refl)) ∷[ refl ] soundsubC tis (+d+d∈ e (g2 , r1 , r2))
  soundsubC (comp-bir {g1 = g1} {a1 = a1} {r1 = r1} ti refl tis) (bi (d , e , refl , refl)) =
    soundsubI ti (+d+d∈ d (g1 , a1 , r1)) ∷[ refl ] soundsubC tis (bi (d , e , refl , refl))
  soundsubC (sub {qt = .uni , a , r} .{uni , _} tis (uni (d' , refl , refl))) (uni (d , refl , refl)) rewrite +-assoc a d' d | +-assoc r d' d =
    soundsubC tis (+d+d∈ (d' + d) (uni , a , r))
  soundsubC (sub {qt = .bi , a , r} .{uni , _} tis (bi (d' , e' , refl , refl))) (uni (d , refl , refl)) rewrite +-assoc a d' d | +-assoc r e' d =
    soundsubC tis (+d+e∈ (d' + d) (e' + d) (a , r))
  soundsubC (sub {qt = .bi , a , r} .{bi , _} tis (bi (d' , e' , refl , refl))) (bi (d , e , refl , refl)) rewrite +-assoc a d' d | +-assoc r e' e =
    soundsubC tis (+d+e∈ (d' + d) (e' + e) (a , r))
-}
  <:-trans = IsPreorder.trans <:-isPreorder

  soundnessC : ∀{qt} → {es : Vec ℕ n} → (is : Code n) → inferC es is ≡ just qt → es ⊢ is :Cs qt
  soundnessI : ∀{qt} → {es : Vec ℕ n} → (i : Insn n) → inferI es i ≡ just qt → es ⊢ i :Is qt
  soundnessI (const x) refl = const
  soundnessI (load x) refl = load
  soundnessI (store x) refl = store
  soundnessI add refl = add
  soundnessI mul refl = mul
  soundnessI and refl = and
  soundnessI not refl = not
  soundnessI nop refl = nop
  soundnessI (br l) refl = br l 
  soundnessI (brif l) refl = brif l
  soundnessI {es = es} (block (a' , r') is) inf with inferC (r' ∷ es) is | inspect (inferC (r' ∷ es)) is
  ... | just (q , a , r) | [ eq ] with (q , a , r) <:? (uni , a' , r')
  soundnessI {es = es} (block (a' , r') is) refl | just (q , a , r) | [ eq ] | yes t<: = block (uni , a' , r') (sub (soundnessC is eq) t<:)
  soundnessI {es = es} (loop (a' , r') is) inf with inferC (a' ∷ es) is | inspect (inferC (a' ∷ es)) is
  ... | just (q , a , r) | [ eq ] with (q , a , r) <:? (uni , a' , r')
  soundnessI {es = es} (loop (a' , r') is) refl | just (q , a , r) | [ eq ] | yes t<: = loop (uni , a' , r') (sub (soundnessC is eq) t<:)

{-
  soundnessC [] refl = []
  soundnessC {es = es} (i ∷ is) inf with inferI es i | inspect (inferI es) i
  ... | just (q1 , a1 , r1) | [ eqI ] with inferC es is | inspect (inferC es) is
  ... | just (q2 , a2 , r2) | [ eqC ] with soundnessI i eqI | soundnessC is eqC | a2 ≤? r1 | r1 ≤? a2
  ... | ti | tis | no ¬a2≤r1 | no ¬r1≤a2 = ⊥-elim (¬a2≤r1 (≰⇒≥ ¬r1≤a2))
  soundnessC (i ∷ is) refl | just (uni , a1 , r1) | _ | just (uni , a2 , r2) | _ | ti | tis | yes a2≤r1 | _ =
    comp-uni ti (≤-diff' a2≤r1) (sub tis (uni (r1 ∸ a2 , refl , refl)))
  soundnessC (i ∷ is) refl | just (_ , a1 , r1) | _ | just (bi , a2 , r2) | _ | ti | tis | yes a2≤r1 | _ =
    comp-bir ti (≤-diff' a2≤r1) (sub tis (bi (r1 ∸ a2 , 0 , refl , +0-id)))
  soundnessC (i ∷ is) refl | just (bi , a1 , r1) | _ | just (uni , a2 , r2) | _ | ti | tis | yes a2≤r1 | _ =
    comp-bil ti (≤-diff' a2≤r1) (sub tis (uni (r1 ∸ a2 , refl , refl)))
  soundnessC {es = es} (i ∷ is) refl | just (uni , a1 , r1) | _ | just (uni , a2 , r2) | _ | ti | tis | no _ | yes r1≤a2 =
    comp-uni (sub ti (uni (a2 ∸ r1 , refl , refl))) (≤-diff r1≤a2) tis
  soundnessC {es = es} (i ∷ is) refl | just (uni , a1 , r1) | _ | just (bi , a2 , r2) | _ | ti | tis | no _ | yes r1≤a2 =
    comp-bir (sub ti (uni (a2 ∸ r1 , refl , refl))) (≤-diff r1≤a2) tis
  soundnessC {es = es} (i ∷ is) refl | just (bi , a1 , r1) | _ | just (_ , a2 , r2) | _ | ti | tis | no _ | yes r1≤a2 =
    comp-bil (sub ti (bi (0 , a2 ∸ r1 , +0-id , refl))) (≤-diff r1≤a2) tis
-}

  principalityC : ∀{t} → {es : Vec ℕ n} → (is : Code n) → es ⊢ is :Cd t → ∃ λ qt → inferC es is ≡ just qt × (t ∈ qt)
  principalityI : ∀{t} → {es : Vec ℕ n} → (i : Insn n) → es ⊢ i :Id t → ∃ λ qt → inferI es i ≡ just qt × (t ∈ qt)
  principalityI .(const _) (const d) = (uni , 0 , 1) , refl , ∈-intro uni (d , refl , refl) 
  principalityI .(load _) (load d) =  (uni , 0 , 1) , refl , ∈-intro uni (d , refl , refl) 
  principalityI .(store _) (store d) =  (uni , 1 , 0) , refl , ∈-intro uni (d , refl , refl) 
  principalityI .nop (nop d) =  (uni , 0 , 0) , refl , ∈-intro uni (d , refl , refl) 
  principalityI .not (not d) =  (uni , 1 , 1) , refl , ∈-intro uni (d , refl , refl)
  principalityI .and (and d) =  (uni , 2 , 1) , refl , ∈-intro uni (d , refl , refl)
  principalityI .mul (mul d) =  (uni , 2 , 1) , refl , ∈-intro uni (d , refl , refl)
  principalityI .add (add d) =  (uni , 2 , 1) , refl , ∈-intro uni (d , refl , refl)
  principalityI {es = es} .(br l) (br l d d') = (bi , es !! l , 0) , refl , ∈-intro bi (d , d' , refl , refl)
  principalityI {es = es} .(brif l) (brif l d) = (uni , suc (es !! l) , es !! l) , refl , ∈-intro uni (d , refl , refl)
  principalityI {es = es} (block .(a' , r') is) (block (a' , r') tis d) with inferC (r' ∷ es) is | principalityC is tis
  ... | just qtis | .qtis , refl , ∈  with qtis <:? (uni , a' , r') | dec-yes (qtis <:? (uni , a' , r')) (∈⇒<:uni ∈)
  ... | yes <: | _ =  (uni , a' , r') , refl , ∈-intro uni (d , refl , refl)
  principalityI {es = es} (loop .(a' , r') is) (loop (a' , r') tis d) with inferC (a' ∷ es) is | principalityC is tis
  ... | just qtis | .qtis , refl , ∈  with qtis <:? (uni , a' , r') | dec-yes (qtis <:? (uni , a' , r')) (∈⇒<:uni ∈)
  ... | yes <: | _ =  (uni , a' , r') , refl , ∈-intro uni (d , refl , refl)

  lemma : ∀ m p {n o k} → n + o ≡ p + k → p ≤ n → m + (n ∸ p) + o ≡ m + k
  lemma m p n+o≡p+k p≤n with m≤n⇒∃d[m+d≡n] p≤n
  ...  | d , refl = trans (cong (λ d → m + d + _) (m+n∸m≡n p d)) (n+o≡p⇒m+n+o≡m+p m (m+n+o≡m+p⇒n+o≡p p n+o≡p+k))
{-
  principalityC .[] ([] d) = (uni , 0 , 0) , refl , uni (d , refl , refl)
  principalityC {es = es} (i ∷ is) (ti ∷[ refl ] tis) with inferI es i | principalityI i ti
  ... | just (q1 , a1 , r1) | (.q1 , .a1 , .r1) , refl , ∈1 with inferC es is | principalityC is tis
  ... | just (q2 , a2 , r2) | (.q2 , .a2 , .r2) , refl , ∈2 with a2 ≤? r1 | r1 ≤? a2
  ... | no ¬a2≤r1 | no ¬r1≤a2 = ⊥-elim (¬a2≤r1 (≰⇒≥ ¬r1≤a2))

  principalityC _ (ti ∷[ refl ] tis) | just (uni , a1 , r1) | ._ , refl , uni (d1 , refl , r1+e1≡a2+d2) | just (uni , a2 , r2) | ._ , refl , uni (d2 , refl , refl) | yes a2≤r1 | _ =
    (uni , a1 , r2 + (r1 ∸ a2)) , refl , uni (d1 , refl , lemma r2 a2 r1+e1≡a2+d2 a2≤r1)
  principalityC _ (ti ∷[ refl ] tis) | just (bi , a1 , r1) | ._ , refl , bi (d1 , e1 , refl , r1+e1≡a2+d2) | just (uni , a2 , r2) | ._ , refl , uni (d2 , refl , refl) | yes a2≤r1 | _ =
    (bi , a1 , r2 + (r1 ∸ a2)) , refl , bi (d1 , e1 , refl , lemma r2 a2 r1+e1≡a2+d2 a2≤r1)
  principalityC _ (ti ∷[ refl ] tis) | just (q1 , a1 , r1) | ._ , refl , ∈1 | just (bi , a2 , r2) | ._ , refl , bi (d2 , e2 , refl , refl) | yes a2≤r1 | _ with preGap ∈1
  ... | (d1 , refl) = (bi ,  a1 , r2) , refl , bi (d1 , e2 , refl , refl) 
  principalityC _ (ti ∷[ refl ] tis) | just (uni , a1 , r1) | ._ , refl , uni (d1 , refl , refl) | just (uni , a2 , r2) | ._ , refl , uni (d2 , a2+d2≡r1+d1 , refl) | no _ | yes r1≤a2 =
    (uni , a1 + (a2 ∸ r1) , r2) , refl , uni (d2 , lemma a1 r1 a2+d2≡r1+d1 r1≤a2 , refl)
  principalityC _ (ti ∷[ refl ] tis) | just (uni , a1 , r1) | ._ , refl , uni (d1 , refl , refl) | just (bi , a2 , r2) | ._ , refl , bi (d2 , e2 , a2+d2≡r1+d1 , refl) | no _ | yes r1≤a2 =
    (bi , a1 + (a2 ∸ r1) , r2) , refl , bi (d2 , e2 , lemma a1 r1 a2+d2≡r1+d1 r1≤a2 , refl)
  principalityC _ (ti ∷[ refl ] tis) | just (bi , a1 , r1) | ._ , refl , bi (d1 , e1 , refl , refl) | just (q2 , a2 , r2) | ._ , refl , ∈2 | no _ | yes r1≤a2 with postGap ∈2
  ... | (e2 , refl) = (bi , a1 , r2) , refl , bi (d1 , e2 , refl , refl)
-}
  principalityC' : ∀{qt'} → {es : Vec ℕ n} → (is : Code n) → es ⊢ is :Cs qt' → ∃ λ qt → inferC es is ≡ just qt × (qt <: qt')
  principalityI' : ∀{qt'} → {es : Vec ℕ n} → (i : Insn n) → es ⊢ i :Is qt' → ∃ λ qt → inferI es i ≡ just qt × (qt <: qt')

  principalityI' .(const _) const = (uni , 0 , 1) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .(load _) load = (uni , 0 , 1) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .(store _) store = (uni , 1 , 0) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .nop nop = (uni , 0 , 0) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .not not = (uni , 1 , 1) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .and and = (uni , 2 , 1) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .mul mul = (uni , 2 , 1) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' .add add = (uni , 2 , 1) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityI' {es = es} .(br l) (br l) = (bi , es !! l , 0) , refl , <:-intro (_ , _ , +0-id , +0-id) bi≤q
  principalityI' {es = es} .(brif l) (brif l) = (uni , suc (es !! l) , es !! l) , refl , <:-intro (_ , +0-id , +0-id) uni≤uni
  principalityI' {es = es} (block .(a' , r') is) (block (q' , a' , r') tis) with inferC (r' ∷ es) is | principalityC' is tis
  ... | just qtis | .qtis , refl , qt<:qt'  with qtis <:? (uni , a' , r') | dec-yes (qtis <:? (uni , a' , r')) (<:-trans (qt<:qt') (qt<:uni (q' , a' , r')))
  ... | yes <: | _ =  (uni , a' , r') , refl , <:-intro (0 , +0-id , +0-id) uni≤uni
  principalityI' {es = es} (loop .(a' , r') is) (loop (q' , a' , r') tis) with inferC (a' ∷ es) is | principalityC' is tis
  ... | just qtis | .qtis , refl , qt<:qt'  with qtis <:? (uni , a' , r') | dec-yes (qtis <:? (uni , a' , r')) (<:-trans (qt<:qt') (qt<:uni (q' , a' , r')))
  ... | yes <: | _ =  (uni , a' , r') , refl , <:-intro (0 , +0-id , +0-id) uni≤uni
  principalityI' i (sub qti qt<:qt') = let primqt , inf≡primqt , primqt<:qt = principalityI' i qti in primqt , inf≡primqt , <:-trans (primqt<:qt) (qt<:qt')

  
  lemma-1 :  ∀{q1 a1 r1 q1' a q2 a2 r2 q2' r m} → (q1 , a1 , r1) <: (q1' , a , m) → (q2 , a2 , r2) <: (q2' , m , r)  →  (conj q1 q2 , a1 + f1 q1 r1 a2 , r2 + f2 q2 r1 a2) <: (conj q1' q2' , a , r)
  lemma-1  {q1 = q1} {r1 = r1} {q2 = q2} {a2 = a2} {m = m} (<:-intro (d1 , refl , eq1) uni≤uni) (<:-intro (d2 , eq2 , refl) uni≤uni) = <:-intro ({!!}) uni≤uni where
    lemma-2 : r1 + d1 ≡ m → a2 + d2 ≡ m → ∃ λ d' → a2 ∸ r1 + d' ≡ d1 × r1 ∸ a2 + d' ≡ d2
    lemma-2 eq1 eq2 with r1 ≤? a2
    ... | p = {!!}

  lemma-1 {q1 = uni} {r1 = r1} {q2 = uni} {a2 = a2}   (<:-intro {.uni} (d1 , refl , refl) _) (<:-intro {.uni} (d2 , eq , refl) _) with r1 ≤? a2
  ... | yes r1≤a2 = <:-intro ({!!} , ({!!} , {!!})) {!!}
  ... | no _ = {!!}
  lemma-1 (<:-intro {bi} x x₁) (<:-intro {uni} x₂ x₃) = <:-intro {!!} {!!}
  lemma-1 (<:-intro {uni} x x₁) (<:-intro {bi} x₂ x₃) = <:-intro {!!} {!!}
  lemma-1 (<:-intro {bi} x x₁) (<:-intro {bi} x₂ x₃) = <:-intro {!!} {!!}

  principalityC' .[] [] = (uni , 0 , 0) , refl , <:-intro (_ , refl , refl) uni≤uni
  principalityC' {es = es} (i ∷ is) (comp ti refl tis) with inferI es i | principalityI' i ti
  ... | just _ | prin-i with inferC es is | principalityC' is tis
  principalityC' {es = es} (i ∷ is) (comp ti refl tis) | just (q1 , a1 , r1) | .(q1 , a1 , r1) , refl , qti<:qti' | just (q2 , a2 , r2) | .(q2 , a2 , r2) , refl , qtis<:qtis' = ( conj q1 q2 , a1 + f1 q1 r1 a2 , r2 + f2 q2 r1 a2) , refl , lemma-1  qti<:qti'  qtis<:qtis'
  principalityC' is (sub qti qt<:qt') = let primqt , inf≡primqt , primqt<:qt = principalityC' is qti in primqt , inf≡primqt , <:-trans (primqt<:qt) (qt<:qt')
{-
  principalityC' {es = es} (i ∷ is) T with inferI es i | principalityI' i qti
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) with inferI es i | principalityI' i qti
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) | just pq1@(uni , pa1 , pr1) | .(uni , pa1 , pr1) , refl , uni (d1 , refl , refl) with inferC es is | principalityC' is qtis
  ... | nothing | ()
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) | just pq1@(uni , pa1 , pr1) | .(uni , pa1 , pr1) , refl , uni (d1 , refl , refl) | just (uni , pa2 , pr2) | .(uni , pa2 , pr2) , refl , pqt2<:qt2 with pr1 ≤? pa2 | pa2 ≤? pr1
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) | just pq1@(uni , pa1 , pr1) | .(uni , pa1 , pr1) , refl , uni (d1 , refl , refl) | just (uni , pa2 , pr2) | .(uni , pa2 , pr2) , refl , pqt2<:qt2  | no ¬pr1≤pa2 | no ¬pa2≤pr1 = {!!}
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) | just pq1@(uni , pa1 , pr1) | .(uni , pa1 , pr1) , refl , uni (d1 , refl , refl) | just (uni , pa2 , pr2) | .(uni , pa2 , pr2) , refl , pqt2<:qt2  | yes pr1≤pa2 | _ = {!!}
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) | just pq1@(uni , pa1 , pr1) | .(uni , pa1 , pr1) , refl , uni (d1 , refl , refl) | just (uni , pa2 , pr2) | .(uni , pa2 , pr2) , refl , pqt2<:qt2  | no _ | yes pa2≤pr1 = {!!}
  principalityC' {es = es} (i ∷ is) (comp-uni qti refl qtis) | just pq1@(bi , pa1 , pr1) | .(bi , pa1 , pr1) , refl , bi (d1 , e1 , refl , refl) with inferC es is | principalityC' is qtis
  ... | nothing | ()
  ... | just (uni , pa2 , pr2) | .(uni , pa2 , pr2) , refl , pqt2<:qt2 = {!!}
  ... | just (bi , pqt1) | .(bi , pqt1) , refl , pqt2<:qt2 = {!!}
  -}
  {-
  with inferC es is | principalityC' is qtis
  ... | just qtis' | .qtis' , refl , qtis'<:qtis with a2 ≤? r1 | r1 ≤? a2
  ... | no ¬a2≤r1 | no ¬r1≤a2 = ⊥-elim (¬a2≤r1 (≰⇒≥ ¬r1≤a2))
  ... | no _ | yes r1≤a2 = {!!}
  
  principalityC' .(_ ∷ _) (comp-bir x y qtis) = {!!}
  principalityC' .(_ ∷ _) (comp-bil x y qtis) = {!!}
  principalityC' is (sub qti qt<:qt') = let primqt , inf≡primqt , primqt<:qt = principalityC' is qti in primqt , inf≡primqt , <:-trans (primqt<:qt) (qt<:qt')
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
{-
  module DirectStyle where
    Lbls : Vec ℕ n → Set
    Lbls [] = ⊥
    Lbls (e ∷ es) = Cfg e ⊎ Lbls es

    injL : {es : Vec ℕ n} → (l : Fin n) → Cfg (VecM.lookup es l) → Lbls es
    injL {es = e ∷ es} zero cfg = inj₁ cfg
    injL {es = e ∷ es} (suc l) cfg = inj₂ (injL l cfg)

    ⟦_⟧Q :  Q × ℕ × ℕ → Vec ℕ n → Set
    ⟦ qt ⟧Q es = ∀ t → t ∈ qt → let (a , r) = t in Cfg a → Cfg r ⊎ Lbls es

    ⟦_⟧<: :  {qt qt' : Q × ℕ × ℕ} → qt <: qt' → (es : Vec ℕ n) → ⟦ qt ⟧Q es → ⟦ qt' ⟧Q es
    ⟦ uni {a , r} (d , refl , refl) ⟧<: es f (a' , r') (uni (d' , refl , refl)) cfg' = f (a' , r') p cfg' where
      p : (a + d + d' , r + d + d') ∈ (uni , a , r)
      p = subst (_∈ (uni , a , r)) (+-assoc'-pair d d' d d') (+d+d∈ (d + d') (uni , a , r))
    ⟦ bi {a , r} (d , e , refl , refl) ⟧<: es f (a' , r') (uni (d' , refl , refl)) cfg' = f (a' , r') p cfg' where
      p : (a + d + d' , r + e + d') ∈ (bi , a , r)
      p = subst (_∈ (bi , a , r)) (+-assoc'-pair d d' e d') (+d+e∈ (d + d') (e + d') (a , r))
    ⟦ bi {a , r} (d , e , refl , refl) ⟧<: es f (a' , r') (bi (d' , e' , refl , refl)) cfg' = f (a' , r') p cfg' where
      p : (a + d + d' , r + e + e') ∈ (bi , a , r)
      p = subst (_∈ (bi , a , r)) (+-assoc'-pair d d' e e') (+d+e∈ (d + d') (e + e') (a , r))

    {-# NON_TERMINATING #-}
    ⟦_⟧I : (i : Insn n) → (es : Vec ℕ n) → ∀{q a r} → es ⊢ i :Is (q , a , r) → ⟦ q , a , r ⟧Q es
    {-# NON_TERMINATING #-}
    ⟦_⟧C : (is : Code n) → (es : Vec ℕ n) → ∀{q a r} → es ⊢ is :Cs (q , a , r) → ⟦ q , a , r ⟧Q es

    ⟦ .const z ⟧I es const _ (uni (_ , refl , refl)) (s , zs) = inj₁ (s , z ∷ zs)
    ⟦ .load v ⟧I es load _ (uni (_ , refl , refl)) (s , zs) = inj₁ (s , lookupS v s ∷ zs)
    ⟦ .store v ⟧I es store _ (uni (_ , refl , refl)) (s , z ∷ zs) = inj₁ (updateS v z s , zs)
    ⟦ .nop ⟧I es nop _ (uni (_ , refl , refl)) cfg = inj₁ cfg
    ⟦ .not ⟧I es not _ (uni (_ , refl , refl)) (s , z ∷ zs) = inj₁ (s , castB' (BoolM.not (castB z)) ∷ zs)
    ⟦ .and ⟧I es and _ (uni (_ , refl , refl)) (s , z ∷ z' ∷ zs) = inj₁ (s , castB' (castB z ∧ castB z') ∷ zs)
    ⟦ .mul ⟧I es mul _ (uni (_ , refl , refl)) (s , z ∷ z' ∷ zs) = inj₁ (s , z IntM.* z' ∷ zs)
    ⟦ .add ⟧I es add _ (uni (_ , refl , refl)) (s , z ∷ z' ∷ zs) = inj₁ (s , z IntM.+ z' ∷ zs)
    ⟦ .(br l) ⟧I es (br l) (a , r) (bi (d , e , refl , refl)) (s , zs) = inj₂ (injL l (s , VecM.take (es !! l) zs))
    ⟦ .(brif l) ⟧I es (brif l) _ (uni (_ , refl , refl)) (s , z ∷ zs) =
      if castB z
      then inj₁ (s , zs)
      else inj₂ (injL l (s , VecM.take (es !! l) zs))
    ⟦ block (a , r) is ⟧I es (block (q , (a , r)) tis) (.(a + d) , .(r + d)) (uni (d , refl , refl)) (s , zs) with ⟦ is ⟧C (r ∷ es) tis (a , r) (min∈ (q , a , r)) (s , VecM.take a zs)
    ... | inj₁ (s' , zs') = inj₁ (s' , zs' VecM.++ VecM.drop a zs)
    ... | inj₂ (inj₁ (s' , zs')) = inj₁ (s' , zs' VecM.++ VecM.drop a zs)
    ... | inj₂ (inj₂ outer) = inj₂ outer
    ⟦ .loop (a , r) is ⟧I es (loop (q , .(a , r)) tis) (.(a + d) , .(r + d)) (uni (d , refl , refl)) (s , zs) with ⟦ is ⟧C (a ∷ es) tis (a , r) (min∈ (q , a , r)) (s , VecM.take a zs)
    ... | inj₁ (s' , zs') = inj₁ (s' , zs' VecM.++ (VecM.drop a zs))
    ... | inj₂ (inj₁ (s' , zs')) = (⟦ loop (a , r) is ⟧I es) (loop (q , a , r) tis) (a + d , r + d) (uni (d , refl , refl)) (s' , zs' VecM.++ VecM.drop a zs)
    ... | inj₂ (inj₂ outer) = inj₂ outer
    ⟦ i ⟧I es (sub {qt = qt} ti <:) t t∈qt cfg = (⟦ <: ⟧<: es) ((⟦ i ⟧I es) ti) t t∈qt cfg

    ⟦ .[] ⟧C es [] (a' , .a') (uni (.a' , refl , refl)) cfg = inj₁ cfg
    ⟦ i ∷ is ⟧C es {a = a} {r = r} (comp {r1 = r1} ti refl tis) instanceOf = {!!}
{-
    ⟦ i ∷ is ⟧C es {a = a} {r = r} (comp-uni {r1 = r1} ti refl tis) (.(a + d) , .(r + d)) (uni (d , refl , refl)) cfg with ⟦ i ⟧I es ti (a + d , r1 + d) (+d+d∈ d (uni , a , r1)) cfg
    ... | inj₂ out = inj₂ out
    ... | inj₁ cfg' = ⟦ is ⟧C es tis (r1 + d , r + d) (+d+d∈ d (uni , r1 , r)) cfg'
    ⟦ i ∷ is ⟧C es {a = a} {r = r} (comp-bir {g1} {r1 = r1} ti refl tis) (.(a + d) , .(r + e)) (bi (d , e , refl , refl)) cfg with ⟦ i ⟧I es ti (a + d , r1 + d) (+d+d∈ d (g1 , a , r1)) cfg
    ... | inj₂ out = inj₂ out
    ... | inj₁ cfg' = ⟦ is ⟧C es tis (r1 + d , r + e) (+d+e∈ d e (r1 , r)) cfg'
    ⟦ i ∷ is ⟧C es {a = a} {r = r} (comp-bil {g2} {r1 = r1} ti refl tis) (.(a + d) , .(r + e)) (bi (d , e , refl , refl)) cfg with ⟦ i ⟧I es ti (a + d , r1 + e ) (+d+e∈ d e (a , r1) ) cfg
    ... | inj₂ out = inj₂ out
    ... | inj₁ cfg' = ⟦ is ⟧C es tis (r1 + e , r + e) (+d+d∈ e (g2 , r1 , r)) cfg'
-}
    ⟦ is ⟧C es (sub {qt = qt} tis <:) t t∈qt cfg = (⟦ <: ⟧<: es) (⟦ is ⟧C es tis) t t∈qt cfg
-}
