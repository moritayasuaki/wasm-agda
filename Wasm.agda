module Wasm where

import Category.Monad.Indexed
import Category.Monad
import Category.Applicative.Indexed
import Data.List as List
import Function
import Level
import Data.Fin as Fin

import Data.Unit as Unit
import Data.Product as Product
import Data.Sum as Sum


import Data.Nat as Nat
import Data.Bool as Bool
import Data.Empty as Empty
import Data.String as String
import Data.Maybe as Maybe
import Monad
import Category.Monad.State using (IStateT ; StateTIMonad)
import Category.Monad.Continuation using (DContT ; DContIMonad)

import Relation.Binary

infix 4.5 _⇒_
record arrow (I : Set) (O : Set) : Set where
  constructor _⇒_
  field
    dom : I
    cod : O

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

    data insn : Set where
      const : val → insn
      nop : insn
      not : insn
      and : insn
      add : insn
      sub : insn
      eqz : insn
      dup : insn
      drop : insn
      block : functype → List insn → insn
      if-else : functype → List insn → List insn → insn
      loop : functype → List insn → insn
      br : ℕ → insn
      br-if : ℕ → insn
  
    vals : Set
    vals = List val

    insns : Set
    insns = List insn

    -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
    frame : Set
    frame = vals × Nat.ℕ × insns × insns

    frames = List frame


    state = frames × vals × insns

    non-ctrl-insn : insn → Bool
    non-ctrl-insn nop = true
    non-ctrl-insn and = true
    non-ctrl-insn not = true
    non-ctrl-insn add = true
    non-ctrl-insn sub = true
    non-ctrl-insn eqz = true
    non-ctrl-insn dup = true
    non-ctrl-insn drop = true
    non-ctrl-insn _ = false

  module _ where
    open String
    open List hiding (_++_)
    open import Data.Nat.Show as NS
    open import Data.Bool.Show as BS

    show-list-with-sep : ∀{X : Set} → (X → String) → String → List X → String
    show-list-with-sep show _ [] = ""
    show-list-with-sep show _ (x ∷ []) = show x
    show-list-with-sep show sep (x ∷ x' ∷ xs) = show x ++ sep ++ show-list-with-sep show sep (x' ∷ xs)

    concat-with-space : List String → String
    concat-with-space = show-list-with-sep (λ s → s) " "

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

    mutual
      show-insns : insns → String
      show-insns is = "[" ++ go is ++ "]" where
        go : insns → String
        go [] = ""
        go (i ∷ []) = show-insn i
        go (i ∷ is) = show-insn i ++ " " ++ show-insns is

      show-insn : insn → String
      show-insn (const n) = concat-with-space ("const" ∷ show-val n ∷ [])
      show-insn nop = "nop"
      show-insn not = "not"
      show-insn and = "and"
      show-insn add = "add"
      show-insn sub = "sub"
      show-insn eqz = "eqz"
      show-insn dup = "dup"
      show-insn drop = "drop"
      show-insn (block ft is) = concat-with-space ("block" ∷ show-functype ft ∷ show-insns is ∷ [])
      show-insn (if-else ft ist isf) = concat-with-space ("if" ∷ show-functype ft ∷ show-insns ist ∷ show-insns isf ∷ [])
      show-insn (loop ft is) = concat-with-space ("loop" ∷ show-functype ft ∷ show-insns is ∷ [])
      show-insn (br n) = concat-with-space ("br" ∷ NS.show n ∷ [])
      show-insn (br-if n) = concat-with-space ("br-if" ∷ NS.show n ∷ [])

    show-frame : frame → String
    show-frame (vs , a , l , is) = show-vals vs ++ "ℓ" ++ NS.show a ++ "{" ++ show-insns l ++ "}" ++ "*" ++ show-insns is

    show-frames : frames → String
    show-frames fs = "[" ++ show-list-with-sep show-frame " " fs ++ "]"

    show-state : state → String
    show-state (fs , vs , is) = "(" ++ show-frames fs ++ ", " ++ show-vals vs ++ ", " ++ show-insns is ++ ")"

module InterpreterCore where
  open String using (String)
  open Category.Monad
  open Category.Monad.State
  open Product
  open Unit
  open Function
  data Step (V E S : Set) : Set where
    ok : S → Step V E S
    error : E → Step V E S

  bind : ∀{V E A B} → Step V E A → (A → Step V E B) → Step V E B
  bind (ok x) f = f x
  bind (error x) _ = error x

  StepMonad : (V E : Set) → RawMonad (Step V E)
  StepMonad V E = record
    { return = ok
    ; _>>=_ = bind
    }

  open Category.Monad.State

  state-machine : Set → Set → (Set → Set)
  state-machine S V = IStateT (λ where tt → S) (Step V (String × S)) tt tt

  state-machine-result : Set → Set → (Set → Set)
  state-machine-result S V X = Step V (String × S) (X × S)

  state-machine-monad : ∀ (S V : Set) → RawMonad (state-machine S V)
  state-machine-monad S V = StateTIMonad (λ where tt → S) (StepMonad V (String × S))

  pattern ok' a = ok (tt , a)
  pattern err a b = error (a , b)

  infixl 4 _<|>_
  _<|>_ : ∀ {S V X} → state-machine S V X → state-machine S V X → state-machine S V X
  (ma <|> mb) st = ma st |> λ where
    (err _ _) → mb st
    s → s

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
  module IList = Monad.IList


  interp-valtype : valtype → Set
  interp-valtype bool = Bool
  interp-valtype nat = ℕ
  interp-valtype unit = ⊤

  module _ where

  module _ where
    non-framed = state-machine (vals × insns) vals
    non-framed-result = state-machine-result (vals × insns) vals
    result-non-framed = Step (vals × insns) vals

    module non-framed-M = RawMonad (state-machine-monad (vals × insns) vals)
    open non-framed-M

    push : val → non-framed ⊤
    push v (vs , is) = ok' ((v ∷ vs) , is) 

    pop : non-framed val
    pop (v ∷ vs , is) = ok (v , vs , is)
    pop st = err "value stack underflow" st
  
    chkval : (t : valtype) → val → non-framed (interp-valtype t)
    chkval bool (bool b) = return b
    chkval nat (nat n) = return n
    chkval unit (unit tt) = return tt
    chkval expected v st = err (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (actual v) ∷ "instead of" ∷ show-valtype expected ∷ []) st
      where actual : val → valtype
            actual (bool _) = bool
            actual (nat _) = nat
            actual (unit _) = unit
  
    popchk : (t : valtype) → non-framed (interp-valtype t)
    popchk t = pop >>= chkval t
  
    fetch : non-framed insn
    fetch (vs , (i ∷ is)) = ok (i , vs , is)
    fetch st = err "no instuction to fetch" st

    feqz : ℕ → Bool
    feqz 0 = true
    feqz _ = false
  
    emit : insn → non-framed ⊤
    emit i (vs , is) = ok' (vs , i ∷ is)
  
    module NonFramed where
      einsn : insn → non-framed ⊤
      einsn (const v) = do push v
      einsn nop = return tt
      einsn and = do
        x ← popchk bool
        y ← popchk bool
        push $ bool $ x ∧ y
      einsn not = do
        x ← popchk bool
        push $ bool $ Bool.not x
      einsn add = do
        x ← popchk nat
        y ← popchk nat
        push $ nat ( x + y )
      einsn sub = do
        x ← popchk nat
        y ← popchk nat
        push $ nat ( x ∸ y )
      einsn eqz = do
        n ← popchk nat
        push $ bool (feqz n)
      einsn dup = do
        v ← pop
        push v
        push v
      einsn drop = do
        pop
        return tt
      einsn _ = err "illegal instruction"
  
      eistep : non-framed ⊤
      eistep s@(v , []) = ok' s
      eistep s@(v , i ∷ is) = (fetch >>= einsn) s


  module _ where
    framed = state-machine (frames × vals × insns) vals
    framed-result = state-machine-result (frames × vals × insns) vals
    module framed-M = RawMonad (state-machine-monad (frames × vals × insns) vals)
    open framed-M 

    lift : ∀{X : Set} → non-framed X → framed X
    lift {X} nf (fs , vs , is) = f (nf (vs , is))
      where f : non-framed-result X → framed-result X
            f (ok (x , s)) = ok (x , fs , s)
            f (error (e , s)) = error (e , fs , s)

    prepend : insns → framed ⊤
    prepend is' (fs , vs , is) = ok' (fs , vs , is' ++ is)

    append : vals → framed ⊤
    append vs' (fs , vs , is) = ok' (fs , vs' ++ vs , is)

    split : ℕ → framed vals
    split n (fs , vs , is) = ok (take n vs , fs , List.drop n vs , is)
  
    vswap : vals → framed vals
    vswap vs (fs , vs' , is) = ok (vs' , fs , vs , is)

    enter : frame → framed ⊤
    enter (vs' , a , l , is') (fs , vs , is) = ok' ((vs , a , l , is) ∷ fs , vs' , is')
  
    lookup-label-nargs : ℕ → framed ℕ
    lookup-label-nargs l st@(fs , _ , _) with List.head (List.drop l fs)
    ...                               | Maybe.just (_ , a , _ , _)  = ok (a , st)
    ...                               | Maybe.nothing = err "jump terget does not exist" st
  
    leave : framed frame
    leave ((vs , a , l , is) ∷ fs , vs' , is') = ok ((vs' , a , l , is') , fs , vs , is)
    leave st = err "control stack underflow" st
  
    br-helper : ℕ → framed ⊤
    br-helper zero = do
      (vs , n , lcont , _) ← leave
      prepend lcont
      append (take n vs)
    br-helper (suc m) = do
      (vs , _ , _ , _) ← leave
      vswap vs
      br-helper m
  
    einsn : insn → framed ⊤
    einsn (block (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length b , [] , is)
    einsn (if-else (a ⇒ b) ist isf) = do
      p ← lift (popchk bool)
      vs ← split (length a)
      if p then enter (vs , length b , [] , ist)
           else enter (vs , length b , [] , isf)
    einsn (loop (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length a , loop (a ⇒ b) is ∷ [] , is)
  
    einsn (br n) = do
      br-helper n
  
    einsn (br-if n) = lift (popchk bool) >>= λ where
        false → return tt
        true → br-helper n

    einsn i = lift (NonFramed.einsn i)

    eend : framed ⊤
    eend = do
      vs , _ , _ , _ ← leave
      append vs

    eifstep : framed ⊤
    eifstep = lift fetch >>= einsn
 
    estep : framed ⊤
    estep st@([] , vs , []) = ok' ([] , vs , [])
    estep st@(fs , vs , i ∷ is) with non-ctrl-insn i
    ...                         | true = (lift NonFramed.eistep) st
    ...                         | false = eifstep st
    estep st@(f ∷ fs , vs , []) = eend st
  
    estepn : ℕ → framed ⊤
    estepn zero = return tt
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

  ex0 ex1 ex2 ex3 ex4 ex5 ex6 ex7 ex8 : state
  ex0 = ([] , (nat 1 ∷ nat 2 ∷ []) , (add ∷ []))
  ex1 = ([] , (bool true ∷ nat 1 ∷ nat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
  ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (nat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
  ex3 = ([] , [] , (drop ∷ []))
  ex4 = ([] , [] , (loop ([] ⇒ nat ∷ nat ∷ []) ([ br 0 ])) ∷ [])
  ex5 = ([] , [] , block ([] ⇒ [ nat ]) (const (nat 1) ∷ []) ∷ [])
  ex6 = ([] , bool true ∷ bool true ∷ [] , and ∷ [])
  ex7 = ([] , bool true ∷ bool true ∷ [] , add ∷ [])
  ex8 = ([] , nat 1 ∷ [] , block (nat ∷ [] ⇒ bool ∷ []) (const (nat 1) ∷ block (nat ∷ [] ⇒ []) (const (bool true) ∷ br 1 ∷ []) ∷ []) ∷ [])

  show-colonlist : List String → String
  show-colonlist = show-list-with-sep (λ x → x) ": " 

  show-result : Step vals (String × state) (⊤ × state) → String
  show-result (ok' st) = show-colonlist (show-state st ∷ "timeout" ∷ [])
  show-result (err emesg st) = show-colonlist (show-state st ∷ emesg ∷ [])

  show-eval : state → String
  show-eval ex = show-state ex ++ " ↪* " ++ show-result (estepn 1024 ex)

  run : List String
  run = (List.map show-eval (ex0 ∷ ex1 ∷ ex2 ∷ ex3 ∷ ex4 ∷ ex5 ∷ ex6 ∷ ex7 ∷ ex8 ∷ []))
{-
module Conv where
  open Nat
  open List hiding (and ; drop)
  open Product

  open Syntax using (val ; vals ; resulttype ; functype) public
  data insn : Set where
    const : val → insn
    nop : insn
    not : insn
    and : insn
    add : insn
    sub : insn
    eqz : insn
    dup : insn
    drop : insn

  insns = List insn

  data cinsn : Set where
    block : functype → List (insns × cinsn) →  cinsn
    if : functype → List (insns × cinsn) → List (insns × cinsn) → cinsn
    else : functype → List (insns × cinsn) → cinsn
    loop : functype → List (insns × cinsn) → cinsn
    end : functype → cinsn
    br : functype → List (insns × cinsn) → cinsn
    br-if : functype → List (insns × cinsn) → cinsn

  ctrl = insns × cinsn
  ctrls = List ctrl
  frame = vals × ctrls
  frames = List frame
  state = frames × vals × ctrls × insns

  add-inner : insn → ctrls × insns → ctrls × insns
  add-inner i ([] , is) = ([] , i ∷ [])
  add-inner i ((is' , c) ∷ cs , is) = ((i ∷ is' , c) ∷ cs , is)
  
  convert : Syntax.insns → ctrls × insns
  convert [] = [] , [] 
  convert (Syntax.const v ∷ w) = add-inner (const v) (convert w)
  convert (Syntax.nop ∷ w) =  add-inner nop (convert w)
  convert (Syntax.not ∷ w) =  add-inner not (convert w)
  convert (Syntax.and ∷ w) =  add-inner and (convert w)
  convert (Syntax.add ∷ w) =  add-inner add (convert w)
  convert (Syntax.sub ∷ w) =  add-inner sub (convert w)
  convert (Syntax.eqz ∷ w) =  add-inner eqz (convert w)
  convert (Syntax.dup ∷ w) =  add-inner dup (convert w)
  convert (Syntax.drop ∷ w) =  add-inner drop (convert w)

  convert (Syntax.block (a ⇒ b) is ∷ js) =
    let (cis , js') , (cjs , ks') = convert is , convert js
    in (([] , block (a ⇒ b) cjs) ∷ cis) ++ ((js' , end (a ⇒ b)) ∷ cjs) , ks'

  convert (Syntax.if-else (a ⇒ b) is js ∷ ks) =
    let (cis , js') , (cjs , ks') , (cks , ls')  = convert is , convert js , convert ks
    in (([] , if (a ⇒ b) cjs cks) ∷ cis) ++ ((js' , else (a ⇒ b) cks) ∷ cjs) ++ ((ks' , end (a ⇒ b)) ∷ cks) , ls'
  convert (Syntax.loop (a ⇒ b) is ∷ js) =
    let (cis , js') , (cjs , ks') = convert is , convert js
    in (([] , loop (a ⇒ b) cis) ∷ cis) ++ ((js' , end (a ⇒ b)) ∷ cjs) , ks'
  convert (Syntax.br n ∷ is) =
    let (cis , is') = convert is
    in (([] , br n) ∷ cis) , is'
  convert (Syntax.br-if n ∷ is) =
    let (cis , is') = convert is
    in (([] , br-if n) ∷ cis) , is'

  module Ctrls where
    open Unit
    open InterpreterCore
    open Category.Monad
    CN = state-machine state vals
    CN-result = state-machine-result state vals
    module CN-M = RawMonad (state-machine-monad state vals)
    open CN-M 

    push : val → CN ⊤
    push v (fs , vs , cs , is) = ok' (fs , v ∷ vs , cs , is) 

    pop : CN val
    pop (fs , v ∷ vs , cs , is) = ok (v , fs , vs , cs , is)
    pop st = err "stack underflow" st

    leave : CN frame
    leave ((vs , cs) ∷ fs , vs' , cs' , is) = ok ((vs' , cs') , fs , vs , cs , is)
    leave st = err "ctrl stack underflow" st

    enter : frame → CN ⊤
    enter (vs' , cs') (fs , vs , cs , is) = ok' ((vs , cs) ∷ fs , vs' , cs' , is)
  
    einsn : insn → CN ⊤
    einsn (const v) = push v
    einsn nop = return tt
    einsn drop = pop >> return tt
    einsn _ = return tt

    ectrl : ctrl → CN ⊤
    ectrl (is , end (a ⇒ b)) ((vs' , cs') ∷ fs , vs , [] , cs) = ? 
    ectrl (is , block (a ⇒ b) cs') (fs , vs , [] , cs) = ok' (((drop a vs) , cs') ∷ fs , vs , is , cs)
    ectrl (is , if (a ⇒ b) cs') (fs , vs , [] , cs) = ok' (((drop a vs) , cs') ∷ fs , vs , is , cs)

    estep : CN ⊤
    estep (fs , vs , [] , []) = ok' (fs , vs , [] , [])
    estep (fs , vs , i ∷ is , cs) = einsn i (fs , vs , is , cs)
    estep (fs , vs , [] , c ∷ cs) = ectrl c (fs , vs , [] , cs)
-}
