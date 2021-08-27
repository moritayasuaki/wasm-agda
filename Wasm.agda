module Wasm where

import Category.Monad.Indexed
import Category.Monad
import Category.Applicative.Indexed
import Function
import Level
import Data.Fin as Fin

import Data.Unit as Unit
import Data.Product as Product
import Data.Sum as Sum


import Data.Nat as Nat
import Data.Vec as Vec
import Data.List as List
import Data.Bool as Bool
import Data.Empty as Empty
import Data.String as String
import Data.Maybe as Maybe
import Monad
import Category.Monad.State using (IStateT ; StateTIMonad)
import Category.Monad.Continuation using (DContT ; DContIMonad)

import Relation.Binary
import Relation.Binary.PropositionalEquality as PropositionalEquality
import Relation.Nullary.Decidable as Decidable

infix 4.5 _⇒_
record arrow (I : Set) (O : Set) : Set where
  constructor _⇒_
  field
    dom : I
    cod : O

_<b_ : Nat.ℕ → Nat.ℕ → Bool.Bool
n <b 0 = Bool.false
0 <b Nat.suc m = Bool.true
Nat.suc n <b Nat.suc m = n <b m

module Show where
  open String
  open List hiding (_++_)
  open import Data.Nat.Show as NS
  open import Data.Bool.Show as BS

  show-list-with-sep : ∀{X : Set} → (X → String) → String → List X → String
  show-list-with-sep show _ [] = ""
  show-list-with-sep show _ (x ∷ []) = show x
  show-list-with-sep show sep (x ∷ x' ∷ xs) = show x ++ sep ++ show-list-with-sep show sep (x' ∷ xs)

  concat-with : String → List String → String
  concat-with s ss = show-list-with-sep (Function.id) s ss

  concat-with-space : List String → String
  concat-with-space = concat-with " "

  concat-with-colon : List String → String
  concat-with-colon = concat-with ": "

  concat-with-comma : List String → String
  concat-with-comma = concat-with ", "


module _ where
  open Relation.Binary
  open import Data.Product
  open import Data.Maybe

  record Lens (S A : Set) : Set where
    field
      view : S → A
      update : S → A → S

  record LensProp (S A : Set) (l : Lens S A) (_~S_ : Rel S Level.zero) (_~A_ : Rel A Level.zero) : Set where
    open Lens l
    field
      view-update : ∀ s → ∀ a → view (update s a) ~A a
      update-view : ∀ s → update s (view s) ~S s
      update-update : ∀ s → ∀ a a' → update (update s a) a' ~S update s a'

  prod-fst : ∀{A B} → Lens (A × B) A
  Lens.view prod-fst = proj₁
  Lens.update prod-fst (fst , snd) = λ new → (new , snd)

  idlens : ∀{S : Set} → Lens S S
  Lens.view idlens = Function.id
  Lens.update idlens = Function.const Function.id

  record Prism (S A : Set) : Set where
    field
      preview : S → Maybe A
      review : A → S

  idprism : ∀{S : Set} → Prism S S
  Prism.preview idprism = just
  Prism.review idprism = Function.id

module Syntax where
  open Product
  open import Function.Identity.Categorical as Id using (Identity)
  
  module _ where
    open Bool hiding (not)
    open Nat
    open Unit
    open List hiding (and ; drop)
    open Monad.IList hiding (drop)
    open Monad.IExc

    data valtype : Set where
      bool : valtype
      nat : valtype
      unit : valtype

    resulttype : Set
    resulttype = List valtype

    functype = arrow resulttype resulttype

    data val : Set where
      bool : Bool → val
      nat : ℕ → val
      unit : ⊤ → val

    data insn : Set
    data n-insn : Set where
        n-const : val → n-insn
        n-nop : n-insn
        n-not : n-insn
        n-and : n-insn
        n-add : n-insn
        n-sub : n-insn
        n-eqz : n-insn
        n-dup : n-insn
        n-drop : n-insn

    data m-insn : Set where
        m-store : m-insn
        m-load : m-insn
        m-grow : m-insn

    data c-insn : Set where
        c-block : functype → List insn → c-insn
        c-if-else : functype → List insn → List insn → c-insn
        c-loop : functype → List insn → c-insn
        c-br : ℕ → c-insn
        c-br-if : ℕ → c-insn

    data insn where
        numeric : n-insn → insn
        control : c-insn → insn
        memory : m-insn → insn

    pattern const x = numeric (n-const x)
    pattern nop = numeric n-nop
    pattern not = numeric n-not
    pattern and = numeric n-and
    pattern add = numeric n-add
    pattern sub = numeric n-sub
    pattern eqz = numeric n-eqz
    pattern dup = numeric n-dup
    pattern drop = numeric n-drop
    pattern block t is = control (c-block t is)
    pattern if-else t is is' = control (c-if-else t is is')
    pattern loop t is = control (c-loop t is)
    pattern br n = control (c-br n)
    pattern br-if n = control (c-br-if n)
    pattern store = memory m-store
    pattern load = memory m-load
    pattern grow = memory m-grow


    vals : Set
    vals = List val

    insns : Set
    insns = List insn

    -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
    frame : Set
    frame = vals × Nat.ℕ × insns × insns

    frames = List frame

    record mem : Set where
      field
        limit : ℕ
        assign : ℕ → ℕ

    initmem : mem
    initmem = record {limit = 0; assign = λ _ → 0}

    count = ℕ

    config = mem × frames × vals × insns

    memarg = ℕ -- offset

  module _ where
    open String
    open List hiding (_++_)
    open import Data.Nat.Show as NS
    open import Data.Bool.Show as BS
    open Show

    show-valtype : valtype → String
    show-valtype unit = "unit"
    show-valtype nat  = "nat"
    show-valtype bool = "bool"

    show-val : val → String
    show-val (unit tt) = "tt"
    show-val (nat n) = NS.show n
    show-val (bool b) = BS.show b

    show-resulttype : resulttype → String
    show-resulttype xs = "[" ++ (show-list-with-sep show-valtype " " xs) ++ "]"

    show-vals : vals → String
    show-vals vs = "[" ++ (show-list-with-sep show-val " " vs) ++ "]"

    show-functype : functype → String
    show-functype (a ⇒ b) = show-resulttype a ++ "⇒" ++ show-resulttype b

    show-insn : insn → String
    show-insns : insns → String
    show-insns is = "[" ++ go is ++ "]" where
      go : insns → String
      go [] = ""
      go (i ∷ []) = show-insn i
      go (i ∷ is) = show-insn i ++ " " ++ go is

    show-insn (const v) = concat-with-space ("const" ∷ show-val v ∷ [])
    show-insn nop = "nop"
    show-insn not = "not"
    show-insn and = "and"
    show-insn add = "add"
    show-insn sub = "sub"
    show-insn eqz = "eqz"
    show-insn dup = "dup"
    show-insn drop = "drop"
    show-insn store = "store"
    show-insn load = "load"
    show-insn (block ft is) = concat-with-space ("block" ∷ show-functype ft ∷ show-insns is ∷ [])
    show-insn (if-else ft ist isf) = concat-with-space ("if" ∷ show-functype ft ∷ show-insns ist ∷ show-insns isf ∷ [])
    show-insn (loop ft is) = concat-with-space ("loop" ∷ show-functype ft ∷ show-insns is ∷ [])
    show-insn (br n) = concat-with-space ("br" ∷ NS.show n ∷ [])
    show-insn (br-if n) = concat-with-space ("br-if" ∷ NS.show n ∷ [])
    show-insn grow = "grow"

    show-frame : frame → String
    show-frame (vs , a , l , is) = show-vals vs ++ "ℓ" ++ NS.show a ++ "{" ++ show-insns l ++ "}" ++ "*" ++ show-insns is

    show-frames : frames → String
    show-frames fs = "[" ++ show-list-with-sep show-frame " " fs ++ "]"

    show-mem : mem → String
    show-mem m = "{" ++ concat-with-comma (go (mem.limit m) (mem.assign m) Nat.zero) ++ "}"where
      open Nat
      go : ℕ → (ℕ → ℕ) → ℕ → List String
      go zero ass i = []
      go (suc n) ass i = (NS.show i ++ " ↦ " ++ NS.show (ass i)) ∷ go n ass (suc i)

    show-config : config → String
    show-config (m , fs , vs , is) = "(" ++ concat-with-comma (show-mem m ∷ show-frames fs ∷ show-vals vs ∷ show-insns is ∷ []) ++ ")"

module Equality where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Function.Injection
  open import Data.Nat as N
  open import Data.Nat.Properties as P
  open Syntax
  to : valtype → ℕ
  to unit = 0
  to bool = 1
  to nat = 2
 
  injective : ∀ {x y : valtype} → to x ≡ to y → x ≡ y
  injective {unit} {unit} p = refl
  injective {bool} {bool} p = refl
  injective {nat} {nat} p = refl

  infix 4 _==_
  _==_ : Decidable _≡_
  _==_ = via-injection (injection to injective) P._≟_

module InterpreterCore where
  open String using (String)
  open Category.Monad
  open Category.Monad.State
  open Product
  open Unit
  open Function
  data Eval (R S : Set) : Set where
    run : S → Eval R S
    stop : R → Eval R S

  bind : ∀{A B R} → Eval R A → (A → Eval R B) → Eval R B
  bind (run s) f = f s
  bind (stop r) _ = stop r

  EvalMonad : (R : Set) → RawMonad (Eval R)
  EvalMonad R = record
    { return = run
    ; _>>=_ = bind
    }

  open Category.Monad.State

  StEval : Set → Set → Set → Set
  StEval R S = IStateT (λ _ → S) (Eval R) tt tt

  StEvalMonad : ∀ (R S : Set) → RawMonad (StEval R S)
  StEvalMonad R S = StateTIMonad (λ _ → S) (EvalMonad R)

  pattern ok a = run a
  pattern ok' a = run (tt , a)

  zoomE : {R' R S' S X : Set} → (Lens S S') → (Prism R R') → S → Eval R' (X × S') → Eval R (X × S)
  zoomE lens prism s (stop r') = stop (review r')
    where open Prism prism
  zoomE lens prism s (run (x , s')) = run (x , (update s s'))
    where open Lens lens

  zoom : {R' R S' S X : Set} → (Lens S S') → (Prism R R') → StEval R' S' X → StEval R S X
  zoom lens prism st' s0 = let
    s0' = view s0
    rs1' = st' s0'
    in zoomE lens prism s0 rs1' where
      open Lens lens
      open Prism prism

feqz : Nat.ℕ → Bool.Bool
feqz 0 = Bool.true
feqz _ = Bool.false

module Interpreter where
  open Function 
  open String using (String)
  open Syntax 
  open Category.Monad
  open Sum
  open Product
  open Unit
  open List hiding (and)
  open Nat
  open Bool hiding (not)
  open Category.Monad.State
  open InterpreterCore public
  open Show

  interp-valtype : valtype → Set
  interp-valtype bool = Bool
  interp-valtype nat = ℕ
  interp-valtype unit = ⊤

  {-
  data reskind : Set where
    error : String → reskind
    value : vals → reskind
    trap : config → reskind
  -}

  -- StE = StEval reskind

  module Numeric where
    res = String
    cfg = vals
    M = StEval res cfg

    pattern error' s = stop s
    open RawMonad (StEvalMonad res cfg)

    push : val → M ⊤
    push v vs = ok' (v ∷ vs)

    pop : M val
    pop (v ∷ vs) = ok (v , vs)
    pop _ = error' "value stack underflow"

    chkval : (t : valtype) → val → M (interp-valtype t)
    chkval bool (bool b) = return b
    chkval nat (nat n) = return n
    chkval unit (unit tt) = return tt
    chkval expected v _ = error' (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (actual v) ∷ "instead of" ∷ show-valtype expected ∷ [])
      where actual : val → valtype
            actual (bool _) = bool
            actual (nat _) = nat
            actual (unit _) = unit
  
    popchk : (t : valtype) → M (interp-valtype t)
    popchk t = pop >>= chkval t
    
    einsn : n-insn → M ⊤
    einsn n-nop = ok'
    einsn (n-const v) = do push v
    einsn n-and = do
      x ← popchk bool
      y ← popchk bool
      push $ bool $ x ∧ y
    einsn n-not = do
      x ← popchk bool
      push $ bool $ Bool.not x
    einsn n-add = do
      x ← popchk nat
      y ← popchk nat
      push $ nat ( x + y )
    einsn n-sub = do
      x ← popchk nat
      y ← popchk nat
      push $ nat ( x ∸ y )
    einsn n-eqz = do
      n ← popchk nat
      push $ bool (feqz n)
    einsn n-dup = do
      v ← pop
      push v
      push v
    einsn n-drop = do
      pop
      return tt
  
  module Control where
    res = String
    cfg = frames × vals × insns
    M = StEval res cfg
    pattern error' s = stop s

    open RawMonad (StEvalMonad res cfg)

    zoom' : {X : Set} → Numeric.M X → M X
    zoom' m = zoom lens idprism m where
      lens : Lens cfg Numeric.cfg
      Lens.view lens (fs , vs , is) = vs
      Lens.update lens (fs , vs , is) vs' = (fs , vs' , is)

    append : vals → M ⊤
    append vs' (fs , vs , is) = ok' (fs , vs' ++ vs , is)

    split : ℕ → M vals
    split n (fs , vs , is) = ok (take n vs , fs , List.drop n vs , is)
  
    swap-insns : insns → M insns
    swap-insns is (fs , vs , is') = ok (is' , fs , vs , is)

    enter : frame → M ⊤
    enter (vs' , a , l , is') (fs , vs , is) = ok' ((vs , a , l , is) ∷ fs , vs' , is')
    
    leave : M frame
    leave ((vs , a , l , is) ∷ fs , vs' , is') = ok ((vs' , a , l , is') , fs , vs , is)
    leave _ = error' "control stack underflow"
  
    br-helper : ℕ → M ⊤
    br-helper n (fs , vs , _) with List.drop n fs
    ... | [] = error' "branch to outside" 
    ... | (vs' , m , lis , cis) ∷ fs' = ok' (fs' , (take m vs) ++ vs' , lis ++ cis)

    popchk : (t : valtype) → M (interp-valtype t)
    popchk x = zoom' (Numeric.popchk x)

    einsn : c-insn → M ⊤
    einsn (c-block (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length b , [] , is)
    einsn (c-if-else (a ⇒ b) ist isf) = do
      p ← popchk bool
      vs ← split (length a)
      if p then enter (vs , length b , [] , ist)
           else enter (vs , length b , [] , isf)
    einsn (c-loop (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length a , loop (a ⇒ b) is ∷ [] , is)
  
    einsn (c-br n) = do
      br-helper n
  
    einsn (c-br-if n) = popchk bool >>= λ where
        false → return tt
        true → br-helper n

    eend : frame → M ⊤
    eend (vs , _ , _ , is) (fs , vs' , _) = ok' (fs , vs' ++ vs , is)

  module Memory where
    data res : Set where
      error : String → res
      trap : res

    cfg = mem × vals
    M = StEval res cfg

    open Decidable

    pattern error' s = stop (error s)
    pattern trap' = stop trap

    open RawMonad (StEvalMonad res cfg)

    zoom' : {X : Set} → StEval Numeric.res Numeric.cfg X → StEval res cfg X
    zoom' m = zoom lens prism m where
      lens : Lens cfg Numeric.cfg
      Lens.view lens (m , vs) = vs
      Lens.update lens (m , vs) vs' = (m , vs')
      prism : Prism res Numeric.res
      Prism.preview prism (error s) = Maybe.just s
      Prism.preview prism trap = Maybe.nothing
      Prism.review prism s = error s

    getmem : M mem
    getmem (m , vs) = ok (m , m , vs)

    setmem : mem → M ⊤
    setmem new (old , vs') = ok' (new , vs')



    chklimit : ℕ → M Bool
    chklimit i (m , vs) = ok ((i <ᵇ mem.limit m) , m , vs)

    reassign : ℕ → ℕ → mem → mem
    reassign i v m = record
      { limit = limit
      ; assign = λ i' → if isYes (i' Nat.≟ i) then v else assign i
      } where open mem m

    growmem : ℕ → mem → ℕ × mem
    growmem i m = limit , record
      { limit = limit + i
      ; assign = assign -- Maybe we need an explicit zero clear
      } where open mem m

    write : ℕ → ℕ → M ⊤
    write i v = do
      m ← getmem
      setmem (reassign i v m)

    read : ℕ → M ℕ
    read i = do
      m ← getmem
      return (mem.assign m i)

    open Relation.Binary
    open import Relation.Binary.PropositionalEquality
    _~_ : Rel mem Level.zero
    m ~ m' = (i : ℕ) → (i Nat.< mem.limit m) → mem.assign m i ≡ mem.assign m' i  


    popchk : (t : valtype) → M (interp-valtype t)
    popchk t = zoom' (Numeric.popchk t)

    push : val → M ⊤
    push v = zoom' (Numeric.push v)

    einsn : m-insn → M ⊤
    einsn m-load = do
      ea ← popchk nat
      true ← chklimit ea where
        false → λ _ → stop trap
      v ← read ea
      push (nat v)
    einsn m-store = do
      v ← popchk nat
      ea ← popchk nat
      true ← chklimit ea where
        false → λ _ → stop trap
      write ea v

    einsn m-grow = do
      n ← popchk nat
      m ← getmem
      let (n' , m') = growmem n m
      setmem m'
      push (nat n')

  data res : Set where
    error : String → res
    done : mem × vals → res
    trap : res

  M = StEval res config

  pattern error' s = stop (error s)
  pattern trap' = stop (trap)
  pattern done' m vs = stop (done (m , vs))

  fromNumeric : ∀{X} → Numeric.M X → M X
  fromNumeric = zoom lens prism where
    lens : Lens config Numeric.cfg 
    Lens.view   lens (m , fs , vs , is) = vs
    Lens.update lens (m , fs , vs , is) vs' = (m , fs , vs' , is)
    prism : Prism res Numeric.res
    Prism.preview prism (error s) = Maybe.just s
    Prism.preview prism _ = Maybe.nothing
    Prism.review prism s = error s

  module C2Cfg where
    lens : Lens config Control.cfg 
    Lens.view   lens (m , fs , vs , is) = (fs , vs , is)
    Lens.update lens (m , fs , vs , is) (fs' , vs' , is') = (m , fs' , vs' , is')
    prism : Prism res Control.res
    Prism.preview prism (error s) = Maybe.just s
    Prism.preview prism _ = Maybe.nothing
    Prism.review prism s = error s

  fromControl : ∀{X} → Control.M X → M X
  fromControl = zoom C2Cfg.lens C2Cfg.prism

  fromControlE : ∀{X} → config → Eval Control.res (X × Control.cfg) → Eval res (X × config)
  fromControlE = zoomE C2Cfg.lens C2Cfg.prism where

  fromMemory : ∀{X} → Memory.M X → M X
  fromMemory = zoom lens prism where
    lens : Lens config Memory.cfg
    Lens.view   lens (m , fs , vs , is) = (m , vs)
    Lens.update lens (m , fs , vs , is) (m' , vs') = (m' , fs , vs' , is)
    prism : Prism res Memory.res
    Prism.preview prism (error s) = Maybe.just (Memory.error s)
    Prism.preview prism (trap) = Maybe.just (Memory.trap)
    Prism.preview prism _ = Maybe.nothing
    Prism.review prism (Memory.error s) = error s
    Prism.review prism (Memory.trap) = trap

  module _ where
    open RawMonad (StEvalMonad res config)

    einsn : insn → M ⊤
    einsn nop = return tt
    einsn (numeric i) = fromNumeric (Numeric.einsn i)
    einsn (control i) = fromControl (Control.einsn i)
    einsn (memory i) = fromMemory (Memory.einsn i)

    estep : M ⊤
    estep (m , fs , vs , i ∷ is) = einsn i (m , fs , vs , is)
    estep (m , fs' , vs , []) with fs'
    ... | [] = done' m  vs
    ... | f ∷ fs = fromControl (Control.eend f) (m , fs , vs , [])

    -- pattern matching for `fs` (the cases for `[]` and `f ∷ fs`) must be here on the bottom of the cases, and you can not place it to the beginning of the function definition.
    -- Otherwise, in the proof of safety, agda requires patttarn-matching on `fs` to normalize the term in any other case, and `estep (fs , vs , br n)` won't be able to normalize `eifstep ...` in a natural way.
    -- This is caused by difference in case tree

    estepn : ℕ → M ⊤
    estepn n (m , [] , vs , []) = done' m  vs
    estepn zero s = trap'
    estepn (suc n) = estep >> estepn n

module Example where
  open Product
  open List hiding (drop ; and ; _++_)
  open Syntax public
  open Interpreter
  open Bool hiding (not)
  open String
  open Nat
  open Unit
  open Show

  ex0 ex1 ex2 ex3 ex4 ex5 ex6 ex7 ex8 ex9 ex10 ex11 : config
  ex0 = (initmem , [] , (nat 1 ∷ nat 2 ∷ []) , (add ∷ []))
  ex1 = (initmem , [] , (bool true ∷ nat 1 ∷ nat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
  ex2 = (initmem , [] , [] , (block ([] ⇒ [ nat ]) (const (nat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
  ex3 = (initmem , [] , [] , (drop ∷ []))
  ex4 = (initmem , [] , [] , (loop ([] ⇒ nat ∷ nat ∷ []) ([ br 0 ])) ∷ [])
  ex5 = (initmem , [] , [] , block ([] ⇒ [ nat ]) (const (nat 1) ∷ []) ∷ [])
  ex6 = (initmem , [] , bool true ∷ bool true ∷ [] , and ∷ [])
  ex7 = (initmem , [] , bool true ∷ bool true ∷ [] , add ∷ [])
  ex8 = (initmem , [] , nat 1 ∷ [] , block (nat ∷ [] ⇒ bool ∷ []) (const (nat 1) ∷ block (nat ∷ [] ⇒ []) (const (bool true) ∷ br 1 ∷ []) ∷ []) ∷ [])
  ex9 = (initmem , [] , [] , const (nat 10) ∷ grow ∷ drop ∷ const (nat 5) ∷ const (nat 3) ∷ store ∷ [])
  ex10 = (initmem , [] , [] , const (nat 0) ∷ const (nat 0) ∷ store ∷ [])
  ex11 = (initmem , [] , [] , const (nat 0) ∷ load ∷ [])

  show-result : Eval res (⊤ × config) → String
  show-result (done' m vs) = "(" ++ concat-with-comma (show-mem m ∷ show-vals vs ∷ []) ++ ")"
  show-result (error' msg) = concat-with-colon ("error" ∷ msg ∷ [])
  show-result (trap') = concat-with-colon ("trap" ∷ [])
  show-result _ = "still running"

  show-eval : config → String
  show-eval ex = show-config ex ++ " ↦* " ++ show-result (estepn 1024 ex)

  run_ : List String
  run_ = (List.map show-eval (ex0 ∷ ex1 ∷ ex2 ∷ ex3 ∷ ex4 ∷ ex5 ∷ ex6 ∷ ex7 ∷ ex8 ∷ ex9 ∷ ex10 ∷ ex11 ∷ []))

