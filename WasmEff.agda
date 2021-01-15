module WasmEff where

import Data.List
import Data.Nat
import Data.Bool
import Data.Maybe
import Data.String
import Data.Integer
import Data.Fin
import Data.Sum
import Data.Product

import Data.Unit
import Relation.Nullary
import Relation.Binary
import Relation.Binary.PropositionalEquality

open import Data.Product
open import Level
open import Category.Monad

open Data.Unit using (⊤ ; tt)
open Data.Bool using (Bool ; _∧_ ; not ; true ; false ; if_then_else_)
open Data.Integer using (ℤ ; _+_ ; -_ ; +0)
open Data.Nat using (ℕ ; zero ; suc)
open Data.List using (List ; _∷_ ; [] ; [_])

open Data.String using (String)

module Syntax where

  data Val : Set where
    unit : Val
    int  : ℤ → Val
    bool : Bool → Val

  show-val : Val → String
  show-val unit = "()"
  show-val (int z) = show z where open Data.Integer
  show-val (bool true) = "true"
  show-val (bool false) = "false"
 

  data ValType : Set where
    unit : ValType
    int : ValType
    bool : ValType

  show-valtype : ValType → String
  show-valtype unit = "unit"
  show-valtype int  = "int"
  show-valtype bool = "bool"

  type-of : Val → ValType
  type-of (Val.unit)   = ValType.unit
  type-of (Val.int v)  = ValType.int
  type-of (Val.bool v) = ValType.bool

  open Data.String using (_++_)
  
  OpdStack = List Val
  show-opdstack : OpdStack → String
  show-opdstack vs = "[" ++ (go vs ++ "]")
    where go : OpdStack → String
          go [] = ""
          go (x ∷ []) = show-val x
          go (x ∷ xs) = show-val x ++ ", "

  ResultType = List ValType
  show-resulttype : ResultType → String
  show-resulttype t = "[" ++ (go t ++ "]")
    where go : ResultType → String
          go [] = ""
          go (x ∷ []) = show-valtype x
          go (x ∷ xs) = show-valtype x ++ " , "

  data Inst : Set where
    const : Val → Inst
    nop : Inst
    bool-not : Inst
    bool-and : Inst
    int-neg : Inst
    int-add : Inst
    eqz : Inst
    dup : Inst
    drop : Inst
    block : ResultType → ResultType → List Inst → Inst
    if-else : ResultType → ResultType → List Inst → List Inst → Inst
    loop : ResultType → ResultType → List Inst → Inst
    br : ℕ → Inst
    br-if : ℕ → Inst

  Insts = List Inst

  -- BlockCtx
  -- 1st Insts type states for instructions when you enter the label (empty sequence for block and if-then-else ,  loop ... end for loop label)
  -- 2nd Insts type states for rest continuation outside of the block
  BlockCtx = OpdStack × ResultType × Insts × Insts

  CtrlStack = List BlockCtx
  Config = CtrlStack × OpdStack × Insts

  -- BlockCtxType
  -- 1nd : labeltype
  -- 2rd : outputtype
  BlockCtxType = ResultType × ResultType
  CtrlStackType = List BlockCtxType

  label-type : BlockCtxType → ResultType
  label-type (l , o) = l
 
  -- 1st : type for saved operands stack
  -- 2nd : label type
  -- 3rd : output type of the block
  -- 4th : type of current operands stack
  -- 5th : type that evaluation context requires
  ConfigType = CtrlStackType × ResultType × ResultType

module Equality where
  open Syntax
  open Relation.Nullary using (yes ; no ; does)
  open Relation.Binary using (DecidableEquality)
  open Relation.Binary.PropositionalEquality using (refl)

  _==-v_ : Val → Val → Bool
  int i₁ ==-v int i₂ = does (i₁ ≟ i₂) where open Data.Integer
  bool b₁ ==-v bool b₂ = does (b₁ ≟ b₂) where open Data.Bool
  unit ==-v unit = true
  _ ==-v _ = false

  _==-vt_ : ValType → ValType → Bool
  int  ==-vt int  = true
  bool ==-vt bool = true
  unit ==-vt unit = true
  _    ==-vt _    = false

  _==-rt_ : ResultType → ResultType → Bool
  [] ==-rt [] = true
  (t ∷ ts)  ==-rt (t' ∷ ts') = (t ==-vt t') ∧ (ts ==-rt ts')
  _ ==-rt _ = false
  
  is-zero : ℤ → Bool
  is-zero +0 = true
  is-zero _ = false

module Evaluation where
  open Syntax
  open Equality
  open Data.Sum

  import Data.Sum.Categorical.Left as Left
  module L = Left String Level.zero
  -- type / stack consistency is checked dynamically
  TC : Set → Set
  TC = L.Sumₗ 

  open RawMonad L.monad

  pattern ok x = inj₂ x
  pattern err x = inj₁ x

  check-value : Val → ValType → TC Val
  check-value v t = if type-of v ==-vt t
    then ok v
    else err (show-valtype t ++ (" is expected, but actual type is " ++ show-valtype (type-of v) ))
    where open Data.String

  pop-blockctx : CtrlStack → TC (BlockCtx × CtrlStack)
  pop-blockctx (ctx ∷ ctrls) = ok (ctx , ctrls)
  pop-blockctx       []      = err "control stack underflow"
  
  pop-value : OpdStack → TC (Val × OpdStack)
  pop-value (v ∷ opds) = ok (v , opds)
  pop-value      []    = err "operand stack underflow"
  
  check-pop-value : OpdStack → ValType → TC (Val × OpdStack)
  check-pop-value opds t =
    do opd , opds ← pop-value opds
       opd ← check-value opd t
       ok (opd , opds)
  
  pop-bool : OpdStack → TC (Bool × OpdStack)
  pop-bool opds =
    do Val.bool(b) , opds ← check-pop-value opds ValType.bool
         where _ → err "this should be absurd patterns"
       ok (b , opds)
  
  pop-int : OpdStack → TC (ℤ × OpdStack)
  pop-int opds =
    do Val.int(z) , opds ← check-pop-value opds ValType.int
         where _ → err "this should be absurd patterns"
       ok (z , opds)
  
  check-opds : OpdStack → ResultType → TC ( OpdStack × OpdStack )
  check-opds opds [] = ok ([] , opds)
  check-opds opds (t ∷ ts) =
    do v , opds ← check-pop-value opds t
       vs , opds' ← check-opds opds ts
       ok ((v ∷ vs) , opds')
  
  check-ctrls-height : CtrlStack → ℕ → TC ( BlockCtx × CtrlStack )
  
  check-ctrls-height ctrls zero    = pop-blockctx ctrls
  check-ctrls-height ctrls (suc n) =
    do _ , ctrls ← pop-blockctx ctrls
       check-ctrls-height ctrls n

  br-common : CtrlStack → OpdStack → ℕ → TC Config
  br-common ctrls opds n =
    do (opds' , ltyp , is , is') , ctrls' ← check-ctrls-height ctrls n
       output , _ ← check-opds opds' ltyp
       ok (ctrls' , output ++ opds' , is ++ is')
    where open Data.List
  
  small-step : Config → TC Config

  small-step (ctrls , opds , nop ∷ is) = ok (ctrls , opds , is)
  
  small-step (ctrls , opds , const v ∷ is) = ok (ctrls , v ∷ opds , is)
  
  small-step (ctrls , opds , dup ∷ is) =
    do v , opds ← pop-value opds
       ok (ctrls , v ∷ v ∷ opds , is)
  
  small-step (ctrls , opds , drop ∷ is) =
    do _ , opds ← pop-value opds
       ok (ctrls , opds , is)
  
  small-step (ctrls , opds , ((block ts te is) ∷ is')) =
    do input , opds' ← check-opds opds ts
       ok ((opds' , te , [] , is') ∷ ctrls , input , is)
  
  small-step (ctrls , opds , (if-else ts te is-true is-false) ∷ is') =
    do b , opds ← pop-bool opds
       input , opds' ← check-opds opds ts
       if b then ok ((opds' , te , [] , is') ∷ ctrls , input , is-true)
            else ok ((opds' , te , [] , is') ∷ ctrls , input , is-false)
  
  small-step (ctrls , opds , (loop ts te is) ∷ is') =
    do input , opds' ← check-opds opds ts
       ok ((opds' , ts , [ loop ts te is ] , is') ∷ ctrls , input , is)
  
  small-step (ctrls , opds , br n ∷ _) = br-common ctrls opds n
  
  small-step (ctrls , opds , br-if n ∷ is) =
    do b , opds ← pop-bool opds
       if b then br-common ctrls opds n
            else ok (ctrls , opds , is)
  
  small-step (ctrls , opds , bool-and ∷ is) =
    do b0 , opds ← pop-bool opds
       b1 , opds ← pop-bool opds
       ok (ctrls , Val.bool (b0 ∧ b1) ∷ opds , is)
  
  small-step (ctrls , opds , bool-not ∷ is) =
    do b , opds ← pop-bool opds
       ok (ctrls , Val.bool (not b) ∷ opds , is)
  
  small-step (ctrls , opds , int-neg ∷ is) =
    do z , opds ← pop-int opds
       ok (ctrls , Val.int (- z) ∷ opds , is)
  
  small-step (ctrls , opds , int-add ∷ is) =
    do z0 , opds ← pop-int opds
       z1 , opds ← pop-int opds
       ok (ctrls , Val.int (z0 + z1) ∷ opds , is)
  
  small-step (ctrls , opds , eqz ∷ is) =
    do z , opds ← pop-int opds
       ok (ctrls , Val.bool (is-zero z) ∷ opds , is)
  
  small-step (ctrls , opds , []) =
    do (_ , _ , _ , is') , ctrls ← pop-blockctx ctrls
       ok (ctrls , opds , is')
  
  n-step : ℕ → Config → TC OpdStack
  n-step _ ([] , opds , []) = ok opds
  n-step zero config        = err "time out"
  n-step (suc n) config     = do config ← small-step config
                                 n-step n config

  show : TC OpdStack → String
  show (ok vs) = show-opdstack vs
  show (err x) = x

module Typed where
  -- static information about type and stack be enbedded in carrier of grading
  open import Category.Monad.State
  open Syntax
  open Equality

  data TyVal : ValType → Set where
    t-int  : ℤ → TyVal int
    t-bool : Bool → TyVal bool
    t-unit : TyVal unit

  elimtype-val : {t : ValType} → TyVal t → Val
  elimtype-val (t-int z) = int z
  elimtype-val (t-bool b) = bool b
  elimtype-val t-unit = unit

  infixr 20 _∷ₜ_
  infixr 20 _∷ᵢ_

  data TyOpdStack : ResultType → Set where
    []ₜ : TyOpdStack []
    _∷ₜ_ : {h-type : ValType} {t-type : ResultType} (h : TyVal h-type) (t : TyOpdStack t-type) → TyOpdStack (h-type ∷ t-type)

  elimtype-opdstack : {t : ResultType} → TyOpdStack t → OpdStack
  elimtype-opdstack []ₜ = []
  elimtype-opdstack (tv ∷ₜ topds) = elimtype-val tv ∷ elimtype-opdstack topds

  open Data.List using (_++_)
  splitₜ : {bs : ResultType}
         → (as : ResultType) → TyOpdStack (as ++ bs) → TyOpdStack as × TyOpdStack bs
  splitₜ []       ws        = ([]ₜ , ws)
  splitₜ (a ∷ as) (v ∷ₜ ws) = let vs , ws = splitₜ as ws
                              in  (v ∷ₜ vs , ws)

  takeₜ :{bs : ResultType}
         → (as : ResultType) → TyOpdStack (as ++ bs) → TyOpdStack as
  takeₜ as ws = proj₁ (splitₜ as ws)

  dropₜ :{bs : ResultType}
         → (as : ResultType) → TyOpdStack (as ++ bs) → TyOpdStack bs
  dropₜ as ws = proj₂ (splitₜ as ws)

  _++ₜ_ : {as bs : ResultType}
        → TyOpdStack as → TyOpdStack bs → TyOpdStack (as ++ bs)
  []ₜ       ++ₜ ws = ws
  (v ∷ₜ vs) ++ₜ ws = v ∷ₜ (vs ++ₜ ws)

  OpdStackStateT = IStateT TyOpdStack
  OpdStackStateTIMonadState = StateTIMonadState TyOpdStack

  -- up?cast by net-stack effect
  upT : {M : Set → Set} → RawMonad M
     → {as as' ds : ResultType} → {A : Set}
     → OpdStackStateT M as as' A → OpdStackStateT M (as ++ ds) (as' ++ ds) A
  upT m {as} f vs =
    do let vas , vbs = splitₜ as vs
       a , vas' ← f vas
       return (a , vas' ++ₜ vbs)
       where open RawMonad m

  -- partial order for subtyping
  data _val-≤_ : ValType → ValType → Set where
    val-refl : {a : ValType} → a val-≤ a
    val-unit : {a : ValType} → a val-≤ ValType.unit

  data _stk-≤_ : ResultType → ResultType → Set where
    stk-refl : {as : ResultType} → as stk-≤ as
    stk-cong  : {a b : ValType} {as bs : ResultType} → (a val-≤ b) → (as stk-≤ bs) → (a ∷ as) stk-≤ (b ∷ bs)
  
  sub-val : {a b : ValType}
          → (a val-≤ b) → TyVal a → TyVal b
  sub-val val-refl v = v
  sub-val val-unit _ = t-unit

  sub-stk : {as bs : ResultType}
          → (as stk-≤ bs) → TyOpdStack as → TyOpdStack bs
  sub-stk stk-refl vs = vs
  sub-stk (stk-cong p ps) (v ∷ₜ vs) = (sub-val p v) ∷ₜ (sub-stk ps vs)

  -- subsumption by subtyping relation
  subT : {M : Set → Set} → RawMonad M
       → {A : Set} {a a' b b' : ResultType}
       → (b stk-≤ a) → (a' stk-≤ b') → OpdStackStateT M a a' A → OpdStackStateT M b b' A
  subT m ps ps' f vs =
    do let vs' = sub-stk ps vs
       a , vs'' ← f vs'
       return (a , sub-stk ps' vs'')
       where open RawMonad m

  module OpdStackState where
    open import Function.Identity.Categorical as Id using (Identity)
    OS = OpdStackStateT Identity
    open RawIMonadState (OpdStackStateTIMonadState Id.monad)

    up = upT Id.monad
    sub = subT Id.monad

    pop-value : {t : ValType}
              → OS [ t ] [] (TyVal t)
    pop-value (v ∷ₜ []ₜ) = v , []ₜ

    pop-bool : OS [ bool ] [] Bool
    pop-bool ((t-bool b) ∷ₜ []ₜ) = b , []ₜ

    pop-int : OS [ int ] [] ℤ
    pop-int ((t-int i) ∷ₜ []ₜ) = i , []ₜ

    push-value : {t : ValType}
               → TyVal t → OS [] [ t ] ⊤
    push-value v []ₜ = tt , v ∷ₜ []ₜ

    push-bool : Bool → OS [] [ bool ] ⊤
    push-bool b []ₜ = tt , t-bool b ∷ₜ []ₜ

    push-int : ℤ → OS [] [ int ] ⊤
    push-int z []ₜ = tt , t-int z ∷ₜ []ₜ

    interp-nop : OS [] [] ⊤
    interp-nop = pure tt

    interp-const : {t : ValType} → TyVal t → (OS [] [ t ] ⊤)
    interp-const v = push-value v

    interp-not : OS [ bool ] [ bool ] ⊤
    interp-not = do b ← pop-bool
                    push-bool (not b)

    interp-and : OS (bool ∷ bool ∷ []) [ bool ] ⊤
    interp-and = do b1 ← up pop-bool  -- pop-bool has type [ bool ] to [], it differs from bool ∷ bool ∷ [] to [ bool ], so up is necessary
                    b2 ← pop-bool
                    push-bool (b1 ∧ b2)

    interp-neg : OS [ int ] [ int ] ⊤
    interp-neg = do z ← pop-int
                    push-int (- z)

    interp-add : OS (int ∷ int ∷ []) [ int ] ⊤
    interp-add = do z0 ← up pop-int
                    z1 ← pop-int
                    push-int (z0 + z1)
    interp-eqz : OS [ int ] [ bool ] ⊤
    interp-eqz = do z ← pop-int
                    push-bool (is-zero z)

    interp-drop : {t : ValType} → OS [ t ] [] ⊤
    interp-drop = do _ ← pop-value
                     pure tt

    interp-dup : {t : ValType} → OS [ t ] (t ∷ t ∷ []) ⊤
    interp-dup = do v ← pop-value
                    push-value v
                    up (push-value v)

  data TyPrimInst : ResultType → ResultType → Set where -- how to handle br ?
    t-nop : TyPrimInst [] []
    t-const : {t : ValType} → TyVal t → TyPrimInst [] [ t ]
    t-not : TyPrimInst [ bool ] [ bool ]
    t-and : TyPrimInst (bool ∷ bool ∷ []) [ bool ]
    t-neg : TyPrimInst [ int ] [ int ]
    t-add : TyPrimInst (int ∷ int ∷ []) [ int ]
    t-eqz : TyPrimInst [ int ] [ bool ]
    t-dup : {t : ValType} → TyPrimInst [ t ] (t ∷ t ∷ [])
    t-drop : {t : ValType} → TyPrimInst [ t ] []

  elimtype-pinst : {i j : ResultType} → TyPrimInst i j → Inst
  elimtype-pinst t-nop = nop
  elimtype-pinst (t-const tv) = const (elimtype-val tv)
  elimtype-pinst t-not = bool-not
  elimtype-pinst t-and = bool-and
  elimtype-pinst t-add = int-add
  elimtype-pinst t-neg = int-neg
  elimtype-pinst t-eqz = eqz
  elimtype-pinst t-dup = dup
  elimtype-pinst t-drop = drop

 
  mutual
    open Data.Fin
    open Data.List
    data TyInsts : CtrlStackType → ResultType → ResultType → Set where
      []ᵢ : {i : ResultType} → TyInsts [] i i -- open empty sequence
      _∷ᵢ_ : {cs : CtrlStackType} {i j k : ResultType} → TyInst cs i j → TyInsts cs j k → TyInsts cs i k

    data TyInst : CtrlStackType → ResultType → ResultType → Set where
      t-prim    : {cs : CtrlStackType} {i j : ResultType} → TyPrimInst i j → TyInst cs i j
      t-block   : {cs : CtrlStackType} (i j : ResultType) → TyInsts ((j , j) ∷ cs) i j → TyInst cs i j
      t-if-else : {cs : CtrlStackType} (i j : ResultType) → TyInsts ((j , j) ∷ cs) i j → TyInsts ((j , j) ∷ cs) i j → TyInst cs i j
      t-loop    : {cs : CtrlStackType} (i j : ResultType) → TyInsts ((i , j) ∷ cs) i j → TyInst cs i j
      t-br      : {cs : CtrlStackType} {j  : ResultType} → (n : Fin (length cs)) → TyInst cs (label-type (lookup cs n)) j
      t-br-if   : {cs : CtrlStackType} → (n : Fin (length cs)) → TyInst cs (bool ∷ (label-type (lookup cs n))) (label-type (lookup cs n))

  mutual
    elimtype-inst : {s : CtrlStackType} {i j : ResultType} → TyInst s i j → Inst
    elimtype-inst (t-prim tp) = elimtype-pinst tp
    elimtype-inst (t-block i j tis) = block i j (elimtype-insts tis)
    elimtype-inst (t-loop i j tis) = loop i j (elimtype-insts tis)
    elimtype-inst (t-if-else i j tis-t tis-f) = if-else i j (elimtype-insts tis-t) (elimtype-insts tis-f)
    elimtype-inst (t-br n ) = br (toℕ n)
    elimtype-inst (t-br-if n ) = br-if (toℕ n)

    elimtype-insts : {s : CtrlStackType} {i j : ResultType} → TyInsts s i j → Insts
    elimtype-insts []ᵢ         = []
    elimtype-insts (ti ∷ᵢ tis) = elimtype-inst ti ∷ elimtype-insts tis
  open OpdStackState using (OS)
  TyBlockCtx : BlockCtxType → CtrlStackType → ResultType → ResultType → Set
  TyBlockCtx (labeltype , outtype) cs savetype outtype' = TyOpdStack savetype × TyInsts cs labeltype outtype × TyInsts cs (outtype ++ savetype) outtype'

  elimtype-blockctx : {bc : BlockCtxType} {cs : CtrlStackType} {save outer : ResultType} → TyBlockCtx bc cs save outer → BlockCtx
  elimtype-blockctx {bc} (topds , tis-label , tis-out) = elimtype-opdstack topds , label-type bc ,  elimtype-insts tis-label , elimtype-insts tis-out

  data TyCtrlStack : CtrlStackType → Set where
    []ₗ : TyCtrlStack []
    _∷ₗ_ : {labeltype savetype outtype : ResultType} → {cs : CtrlStackType} → {outtype' : ResultType}
           → TyBlockCtx (labeltype , outtype) cs savetype outtype' → TyCtrlStack cs → TyCtrlStack ((labeltype , outtype) ∷ cs)

  CtrlStackStateT = IStateT TyCtrlStack
  CtrlStackStateTIMonadState = StateTIMonadState TyCtrlStack

  -- up?cast by net-stack effect
  ctrlupT : {M : Set → Set} → RawMonad M
     → {as as' ds : ResultType} → {A : Set}
     → CtrlStackStateT M as as' A → CtrlStackStateT M (as ++ ds) (as' ++ ds) A
  ctrlupT m {as} f vs =
    do let vas , vbs = splitₜ as vs
       a , vas' ← f vas
       return (a , vas' ++ₜ vbs)
       where open RawMonad m
  

  TyConfig : CtrlStackType → ResultType → ResultType → Set
  TyConfig cs i j = TyCtrlStack cs × TyOpdStack i × TyInsts cs i j
  t-small-step : {cs cs' : CtrlStackType} {i j i' j' : ResultType} → TyConfig cs i j → TyConfig cs' i' j'
  t-small-step (ctx , opds , t-prim (t-const v) ∷ᵢ tis) = (ctx , v ∷ opds , tis)

  

open import IO
open Syntax
open Evaluation
open Typed

t-sample' = t-prim (t-const (t-bool false)) ∷ᵢ t-if-else [] (int ∷  [])
     (t-prim (t-const (t-int 1ℤ)) ∷ᵢ t-prim (t-const (t-int 1ℤ)) ∷ᵢ t-add ∷ᵢ []ᵢ)
     (t-prim (t-const (t-int 0ℤ)) ∷ᵢ []ᵢ)
   ∷ᵢ []ᵢ where open Data.Integer
sample' = const (bool false) ∷ if-else [] [ int ] (const (int 1ℤ) ∷ const (int 1ℤ) ∷ int-add ∷ []) [ const (int 0ℤ) ] ∷ [] where open Data.Integer
sample = const (bool false) ∷ if-else [ int ] [ int ] (const (int 1ℤ) ∷ const (int 1ℤ) ∷ int-add ∷ []) [] ∷ [] where open Data.Integer

runner : Insts → IO ⊤
runner insts = putStrLn (show (n-step 100 ([] , [] , insts)))

main = run (runner sample)
