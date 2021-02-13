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
    frame = vals × Nat.ℕ × insn × insns

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
    show-frame (vs , a , l , is) = show-vals vs ++ "ℓ" ++ NS.show a ++ "{" ++ show-insn l ++ "}" ++ "*" ++ show-insns is

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

  import Data.Sum.Categorical.Left as Left
  module Error = Left (String × state) Level.zero
  error = Error.Sumₗ

  open Category.Monad.State
  E = IStateT (λ _ → state) error tt tt

  pattern ok a = inj₂ a
  pattern err a b = inj₁ (a , b)

  monad = StateTIMonad {_} {⊤} (λ _ → state) Error.monad 
  open RawMonad monad


  push : val → E ⊤
  push v (fs , vs , is) = ok (tt , fs , (v ∷ vs) , is)

  pop : E val
  pop (fs , v ∷ vs , is) = ok (v , fs , vs , is)
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

  infixl 4 _<|>_
  _<|>_ : ∀ {X} → E X → E X → E X
  (ma <|> mb) st = ma st |> λ where
    (ok st') → ok st'
    (err _ _) → mb st 

  chkval : (t : valtype) → val → E (interp-valtype t)
  chkval bool (cbool b) = return b
  chkval nat (cnat n) = return n
  chkval unit (cunit tt) = return tt
  chkval t v st = err (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (typeof-val v) ∷ "instead of" ∷ show-valtype t ∷ []) st

  chkvals : (t : resulttype) → vals → E (interp-resulttype t × vals)
  chkvals (t ∷ ts) (v ∷ vs) = do
    v' ← chkval t v
    (vs' , rest) ← chkvals ts vs
    return (v' IList.∷ vs' , rest)
  chkvals [] vs = return (IList.[] , vs)
  chkvals (_ ∷ _) [] st = err "not enough elements in input" st

  popchk : (t : valtype) → E (interp-valtype t)
  popchk t = pop >>= chkval t

  popchks : (ts : resulttype) → E (interp-resulttype ts)
  popchks [] = return IList.[]
  popchks (t ∷ ts) = do
    v ← popchk t 
    vs ← popchks ts
    return $ v IList.∷ vs

  pushvs : vals → E ⊤
  pushvs [] = return tt
  pushvs (v ∷ vs) = push v >> pushvs vs

  fetch : E insn
  fetch (fs , vs , (i ∷ is)) = ok (i , fs , vs , is)
  fetch st = err "no instuction to fetch" st

  emit : insn → E ⊤
  emit i (fs , vs , is) = ok (tt , fs , vs , i ∷ is)
  
  enter : frame → E ⊤
  enter (vs' , a , l , is') (fs , vs , is) = ok (tt , (vs , a , l , is) ∷ fs , vs' , is')

  lookup-label-nargs : ℕ → E ℕ
  lookup-label-nargs l st@(fs , _ , _) with List.head (List.drop l fs)
  ...                               | Maybe.just (_ , a , _ , _)  = ok (a , st)
  ...                               | Maybe.nothing = err "jump terget does not exist" st

  leave : E frame
  leave ((vs , a , l , is) ∷ fs , vs' , is') = ok ((vs' , a , l , is') , fs , vs , is)
  leave st = err "control stack underflow" st

  append : vals → E ⊤
  append vs' (fs , vs , is) = ok (tt , fs , vs' ++ vs , is)

  vswap : vals → E vals
  vswap vs (fs , vs' , is) = ok (vs' , fs , vs , is)

  br-helper : ℕ → E ⊤
  br-helper zero = do
    (vs , n , l , _) ← leave
    emit l
    append (take n vs)
  br-helper (suc m) = do
    (vs , _ , _ , _) ← leave
    vswap vs
    br-helper m

  einsn : insn → E ⊤
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
    zero ← popchk nat
      where suc _ → push $ cbool false
    push $ cbool true
  einsn dup = do
    v ← pop
    push v
    push v
  einsn drop = do
    pop
    return tt
  einsn (block (a ⇒ b) is) = do
    vs ← popchks a
    enter (encvals vs , length b , nop , is)
  einsn (if-else (a ⇒ b) ist isf) = do
    p ← popchk bool
    vs ← popchks a
    if p then enter (encvals vs , length b , nop , ist)
         else enter (encvals vs , length b , nop , isf)
  einsn (loop (a ⇒ b) is) = do
    vs ← popchks a
    enter (encvals vs , length a , loop (a ⇒ b) is , is)

  einsn (br n) = do
    br-helper n

  einsn (br-if n) = popchk bool >>= λ where
      false → return tt
      true → br-helper n

  eend : E ⊤
  eend = do
    vs , _ , _ , _ ← leave
    append vs

  estep : E ⊤
  estep st@([] , vs , []) = ok (tt , [] , vs , [])
  estep st@(fs , vs , []) = eend st
  estep st@(fs , vs , is) = (fetch >>= einsn) st

module Example where
  open Product
  open List hiding (drop ; and ; _++_)
  open Syntax public
  open Interpreter
  open Bool hiding (not)
  open String
  open Nat

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

  evaln : state → ℕ → error vals
  evaln ([] , vs , []) _ = ok vs
  evaln st zero = err "time out" st
  evaln st (suc n) with estep st
  ...                 | ok (tt , st') = evaln st' n
  ...                 | (err emsg st') = err emsg st'

  show-result : error vals → String
  show-result (ok vs) = show-vals vs
  show-result (err emesg st) = show-list-with-sep (λ x → x) ": " (show-state st ∷ emesg ∷ [])

  show-eval : state → String
  show-eval ex = show-state ex ++ " ↪* " ++ show-result (evaln ex 1024)

  run : List String
  run = List.map show-eval (ex0 ∷ ex1 ∷ ex2 ∷ ex3 ∷ ex4 ∷ ex5 ∷ ex6 ∷ ex7 ∷ ex8 ∷ [])
