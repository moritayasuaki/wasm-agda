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

    feqz : ℕ → Bool
    feqz 0 = true
    feqz _ = false
    
    data valtype : Set where
      bool : valtype
      nat : valtype
      unit : valtype

    resulttype : Set
    resulttype = List valtype

    infix 4.5 _⇒_
    record functype {X : Set} : Set where
      constructor _⇒_
      field
        input : resulttype
        output : X

    data val : Set where
      cbool : Bool → val
      cnat : ℕ → val
      cunit : ⊤ → val

    vals : Set
    vals = List val

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
      block : functype {resulttype} → List insn → insn
      if-else : functype {resulttype} → List insn → List insn → insn
      loop : functype {resulttype} → List insn → insn
      br : ℕ → insn
      br-if : ℕ → insn

    insns : Set
    insns = List insn

    -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
    frame : Set
    frame = vals × Nat.ℕ × insns × insns

    frames = List frame


    state = frames × vals × insns

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
    show-val (cunit tt) = "tt"
    show-val (cnat n) = NS.show n
    show-val (cbool b) = BS.show b

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
  module IList = Monad.IList

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

  state' = vals × insns
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

  module non where
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
  
    typeof-val : val → valtype
    typeof-val (cbool _) = bool
    typeof-val (cnat _) = nat
    typeof-val (cunit _) = unit
  
    interp-valtype : valtype → Set
    interp-valtype bool = Bool
    interp-valtype nat = ℕ
    interp-valtype unit = ⊤
  
    interp-resulttype : resulttype → Set
    interp-resulttype ts = IList.IList interp-valtype ts
  
    encval : ∀{t} → interp-valtype t → val
    encval {bool} v = cbool v
    encval {unit} v = cunit v
    encval {nat} v = cnat v
  
    encvals : ∀{ts} → interp-resulttype ts → vals
    encvals IList.[] = []
    encvals (v IList.∷ vs) = encval v ∷ encvals vs
  
    chkval : (t : valtype) → val → non-framed (interp-valtype t)
    chkval bool (cbool b) = return b
    chkval nat (cnat n) = return n
    chkval unit (cunit tt) = return tt
    chkval t v st = err (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (typeof-val v) ∷ "instead of" ∷ show-valtype t ∷ []) st
  
    chkvals : (t : resulttype) → vals → non-framed (interp-resulttype t × vals)
    chkvals (t ∷ ts) (v ∷ vs) = do
      v' ← chkval t v
      (vs' , rest) ← chkvals ts vs
      return (v' IList.∷ vs' , rest)
    chkvals [] vs = return (IList.[] , vs)
    chkvals (_ ∷ _) [] st = err "not enough elements in input" st
  
    popchk : (t : valtype) → non-framed (interp-valtype t)
    popchk t = pop >>= chkval t
  
    popchks : (ts : resulttype) → non-framed (interp-resulttype ts)
    popchks [] = return IList.[]
    popchks (t ∷ ts) = do
      v ← popchk t 
      vs ← popchks ts
      return $ v IList.∷ vs
  
    pushvs : vals → non-framed ⊤
    pushvs [] = return tt
    pushvs (v ∷ vs) = push v >> pushvs vs
  
    fetch : non-framed insn
    fetch (vs , (i ∷ is)) = ok (i , vs , is)
    fetch st = err "no instuction to fetch" st
  
    emit : insn → non-framed ⊤
    emit i (vs , is) = ok' (vs , i ∷ is)
  
  
 
    einsn : insn → non-framed ⊤
    einsn (const v) = do push v
    einsn nop = return tt
    einsn and = do
      x ← popchk bool
      y ← popchk bool
      push $ cbool $ x ∧ y
    einsn not = do
      x ← popchk bool
      push $ cbool $ Bool.not x
    einsn add = do
      x ← popchk nat
      y ← popchk nat
      push $ cnat $ x + y
    einsn sub = do
      x ← popchk nat
      y ← popchk nat
      push $ cnat $ x ∸ y
    einsn eqz = do
      n ← popchk nat
      push $ cbool (feqz n)
    einsn dup = do
      v ← pop
      push v
      push v
    einsn drop = do
      pop
      return tt
    einsn _ = err "illegal instruction"

    eistep : non-framed ⊤
    eistep = fetch >>= einsn

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
    framed = state-machine (frames × vals × insns) vals
    framed-result = state-machine-result (frames × vals × insns) vals
    module framed-M = RawMonad (state-machine-monad (frames × vals × insns) vals)
    open framed-M 

    lift : ∀{X : Set} → non.non-framed X → framed X
    lift {X} nf (fs , vs , is) = f (nf (vs , is))
      where f : non.non-framed-result X → framed-result X
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
      p ← lift (non.popchk bool)
      vs ← split (length a)
      if p then enter (vs , length b , [] , ist)
           else enter (vs , length b , [] , isf)
    einsn (loop (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length a , loop (a ⇒ b) is ∷ [] , is)
  
    einsn (br n) = do
      br-helper n
  
    einsn (br-if n) = lift (non.popchk bool) >>= λ where
        false → return tt
        true → br-helper n

    einsn i = lift (non.einsn i)

    eend : framed ⊤
    eend = do
      vs , _ , _ , _ ← leave
      append vs

    eifstep : framed ⊤
    eifstep = lift (non.fetch) >>= einsn
 
    estep : framed ⊤
    estep st@([] , vs , []) = ok' ([] , vs , [])
    estep st@(fs , vs , i ∷ is) with non.non-ctrl-insn i
    ...                         | true = (lift non.eistep) st
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
  ex0 = ([] , (cnat 1 ∷ cnat 2 ∷ []) , (add ∷ []))
  ex1 = ([] , (cbool true ∷ cnat 1 ∷ cnat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
  ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (cnat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
  ex3 = ([] , [] , (drop ∷ []))
  ex4 = ([] , [] , (loop ([] ⇒ nat ∷ nat ∷ []) ([ br 0 ])) ∷ [])
  ex5 = ([] , [] , block ([] ⇒ [ nat ]) (const (cnat 1) ∷ []) ∷ [])
  ex6 = ([] , cbool true ∷ cbool true ∷ [] , and ∷ [])
  ex7 = ([] , cbool true ∷ cbool true ∷ [] , add ∷ [])
  ex8 = ([] , cnat 1 ∷ [] , block (nat ∷ [] ⇒ bool ∷ []) (const (cnat 1) ∷ block (nat ∷ [] ⇒ []) (const (cbool true) ∷ br 1 ∷ []) ∷ []) ∷ [])

  show-colonlist : List String → String
  show-colonlist = show-list-with-sep (λ x → x) ": " 

  show-result : Step vals (String × state) (⊤ × state) → String
  show-result (ok' st) = show-colonlist (show-state st ∷ "timeout" ∷ [])
  show-result (err emesg st) = show-colonlist (show-state st ∷ emesg ∷ [])

  show-eval : state → String
  show-eval ex = show-state ex ++ " ↪* " ++ show-result (estepn 1024 ex)

  run : List String
  run = (List.map show-eval (ex0 ∷ ex1 ∷ ex2 ∷ ex3 ∷ ex4 ∷ ex5 ∷ ex6 ∷ ex7 ∷ ex8 ∷ []))
