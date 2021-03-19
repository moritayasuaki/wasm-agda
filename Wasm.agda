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
  concat-with s ss = show-list-with-sep (λ s → s) s ss

  concat-with-space : List String → String
  concat-with-space = concat-with " "

  concat-with-colon : List String → String
  concat-with-colon = concat-with ": "


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

    open Fin using (Fin)
    data insn' : ℕ → Set where
      const' : {n : ℕ} → val → insn' n
      nop' : {n : ℕ} → insn' n
      not' : {n : ℕ} → insn' n
      and' : {n : ℕ} → insn' n
      add' : {n : ℕ} → insn' n
      sub' : {n : ℕ} → insn' n
      eqz' : {n : ℕ} → insn' n
      dup' : {n : ℕ} → insn' n
      drop' : {n : ℕ} → insn' n
      block' : {n : ℕ} → functype → List (insn' (suc n)) → insn' n
      if-else' : {n : ℕ} → functype → List (insn' (suc n)) → List (insn' (suc n)) → insn' n
      loop' : {n : ℕ} → functype → List (insn' (suc n)) → insn' n
      br' : {n : ℕ} → Fin n → insn' n
      br-if' : {n : ℕ} → Fin n → insn' n

    lightcheck : (n : ℕ) → List insn → List (insn' n)
    lightcheck n (const v ∷ is) = const' {n} v ∷ lightcheck n is
    lightcheck n (nop ∷ is) = nop' {n} ∷ lightcheck n is
    lightcheck n (not ∷ is) = not' {n} ∷ lightcheck n is
    lightcheck n (and ∷ is) = and' {n} ∷ lightcheck n is
    lightcheck n (add ∷ is) = add' {n} ∷ lightcheck n is
    lightcheck n (sub ∷ is) = sub' {n} ∷ lightcheck n is
    lightcheck n (eqz ∷ is) = eqz' {n} ∷ lightcheck n is
    lightcheck n (dup ∷ is) = dup' {n} ∷ lightcheck n is
    lightcheck n (drop ∷ is) = drop' {n} ∷ lightcheck n is
    lightcheck n (block ft is' ∷ is) = block' {n} ft (lightcheck (suc n) is') ∷ lightcheck n is
    lightcheck n (if-else ft is' is'' ∷ is) = if-else' {n} ft (lightcheck (suc n) is') (lightcheck (suc n) is'') ∷ lightcheck n is
    lightcheck n (loop ft is' ∷ is) = loop' {n} ft (lightcheck (suc n) is') ∷ lightcheck n is
    lightcheck n (br l  ∷ is) = br' {n} l ∷ lightcheck n is       -- should report error when n ≤ l?
    lightcheck n (br-if l  ∷ is) = br-if' {n} l ∷ lightcheck n is
    lightcheck n [] = []
  
    vals : Set
    vals = List val

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
  data result (S : Set) : Set where
    ok : S → result S
    error : String → result S

  bind : ∀{A B} → result A → (A → result B) → result B
  bind (ok x) f = f x
  bind (error x) _ = error x

  resultMonad : RawMonad result
  resultMonad = record
    { return = ok
    ; _>>=_ = bind
    }

  open Category.Monad.State

  state-machine : Set → Set → Set
  state-machine S = IStateT (λ _ → S) result tt tt

  state-machine-result : Set → Set → Set
  state-machine-result S X = result (X × S)

  state-machine-monad : ∀ (S : Set) → RawMonad (state-machine S)
  state-machine-monad S = StateTIMonad (λ _ → S) resultMonad

  lift-result : ∀{S X} → result X → state-machine S X
  lift-result x s = do
    v ← x
    ok (v , s)
    where open RawMonad resultMonad

  pattern ok' a = ok (tt , a)

  record substate (S : Set) (S' : Set) : Set where
    field
      view : S → S'
      update : S → S' → S
      eq : ∀(x : S) → update x (view x) PropositionalEquality.≡ x

  upgrade : {S' S X : Set} → (substate S S') → state-machine S' X → state-machine S X
  upgrade {S'} r ms' s = do
    x , t' ← ms' (view s)
    return $ x , update s t'
    where open substate r
          open RawMonad resultMonad

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

  module _ where
    non-framed = state-machine (vals × insns)
    non-framed-result = state-machine-result (vals × insns)
    result-non-framed = result (vals × insns)

    module non-framed-M = RawMonad (state-machine-monad (vals × insns))
    open non-framed-M

    push : val → non-framed ⊤
    push v (vs , is) = ok' ((v ∷ vs) , is) 

    pop : non-framed val
    pop (v ∷ vs , is) = ok (v , vs , is)
    pop _ = error "value stack underflow"
  
    chkval : (t : valtype) → val → non-framed (interp-valtype t)
    chkval bool (bool b) = return b
    chkval nat (nat n) = return n
    chkval unit (unit tt) = return tt
    chkval expected v _ = error (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (actual v) ∷ "instead of" ∷ show-valtype expected ∷ [])
      where actual : val → valtype
            actual (bool _) = bool
            actual (nat _) = nat
            actual (unit _) = unit
  
    popchk : (t : valtype) → non-framed (interp-valtype t)
    popchk t = pop >>= chkval t
  
    fetch : non-framed insn
    fetch (vs , (i ∷ is)) = ok (i , vs , is)
    fetch _ = error "no instuction to fetch"

  
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
      einsn _ _ = error "illegal instruction"
  
      eistep : non-framed ⊤
      eistep s@(v , []) = ok' s
      eistep s@(v , i ∷ is) = (fetch >>= einsn) s


  module _ where
    framed = state-machine (frames × vals × insns)
    framed-result = state-machine-result (frames × vals × insns)
    module framed-M = RawMonad (state-machine-monad (frames × vals × insns))
    open framed-M 

    lift : ∀{X : Set} → non-framed X → framed X
    lift {X} nf (fs , vs , is) = f (nf (vs , is))
      where f : non-framed-result X → framed-result X
            f (ok (x , s)) = ok (x , fs , s)
            f (error e) = (error e)

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
    ...                               | Maybe.nothing = error "jump terget does not exist"
  
    leave : framed frame
    leave ((vs , a , l , is) ∷ fs , vs' , is') = ok ((vs' , a , l , is') , fs , vs , is)
    leave _ = error "control stack underflow"
  
    br-helper : ℕ → framed ⊤
    br-helper n (fs , vs , _) with List.drop n fs
    ... | [] = error "branch to outside" 
    ... | (vs' , m , lis , cis) ∷ fs' = ok' (fs' , (take m vs) ++ vs' , lis ++ cis)


    {-
    br-helper zero = do
      (vs , n , lcont , _) ← leave
      prepend lcont
      append (take n vs)
    br-helper (suc m) = do
      (vs , _ , _ , _) ← leave
      vswap vs
      br-helper m
    -}
  
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
    estep (fs , vs , br n ∷ is) = eifstep (fs , vs , br n ∷ is)
    estep (fs , vs , nop ∷ is) = (lift NonFramed.eistep) (fs , vs , nop ∷ is)
    estep (fs , vs , const v ∷ is) = (lift NonFramed.eistep) (fs , vs , insn.const v ∷ is)
    estep (fs , vs , and ∷ is) = (lift NonFramed.eistep) (fs , vs , and ∷ is)
    estep (fs , vs , not ∷ is) = (lift NonFramed.eistep) (fs , vs , not ∷ is)
    estep (fs , vs , add ∷ is) = (lift NonFramed.eistep) (fs , vs , add ∷ is)
    estep (fs , vs , sub ∷ is) = (lift NonFramed.eistep) (fs , vs , sub ∷ is)
    estep (fs , vs , eqz ∷ is) = (lift NonFramed.eistep) (fs , vs , eqz ∷ is)
    estep (fs , vs , dup ∷ is) = (lift NonFramed.eistep) (fs , vs , dup ∷ is)
    estep (fs , vs , drop ∷ is) = (lift NonFramed.eistep) (fs , vs , insn.drop ∷ is)
    estep (fs , vs , block t is' ∷ is) = eifstep (fs , vs , block t is' ∷ is)
    estep (fs , vs , if-else t is' is'' ∷ is) = eifstep (fs , vs , if-else t is' is'' ∷ is)
    estep (fs , vs , loop t is' ∷ is) = eifstep (fs , vs , loop t is' ∷ is)
    estep (fs , vs , br-if n ∷ is) = eifstep (fs , vs , br-if n ∷ is)
    estep ([] , vs , []) = ok' ([] , vs , [])
    estep (f ∷ fs , vs , []) = eend (f ∷ fs , vs , [])
    -- pattern matching for `fs` (the cases for `[]` and `f ∷ fs`) must be here on the bottom of the cases, and you can not place it to the beginning of the function definition.
    -- Otherwise, in the proof of safety, agda requires patttarn-matching on `fs` to normalize the term in any other case, and `estep (fs , vs , br n)` won't be able to normalize `eifstep ...` in a natural way.
    -- This is caused by difference in case tree
   
    estepn : ℕ → framed ⊤
    estepn zero ([] , vs , []) = ok' ([] , vs , [])
    estepn zero _ = error "timeout"
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

  show-result : result (⊤ × state) → String
  show-result (ok' st) = concat-with-colon (show-state st ∷ [])
  show-result (error emesg) = concat-with-colon ("error" ∷ emesg ∷ [])

  show-eval : state → String
  show-eval ex = show-state ex ++ " ↪* " ++ show-result (estepn 1024 ex)

  run : List String
  run = (List.map show-eval (ex0 ∷ ex1 ∷ ex2 ∷ ex3 ∷ ex4 ∷ ex5 ∷ ex6 ∷ ex7 ∷ ex8 ∷ []))
