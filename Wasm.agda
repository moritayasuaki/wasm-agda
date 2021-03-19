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
    open Fin
    open Unit
    open List hiding (and ; drop)
    open Monad.IList hiding (drop)
    open Monad.IExc
    open Vec using (Vec ; _∷_ ; [])

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

    data insn : ℕ → Set where
      const : {n : ℕ} → val → insn n
      nop : {n : ℕ} → insn n
      not : {n : ℕ} → insn n
      and : {n : ℕ} → insn n
      add : {n : ℕ} → insn n
      sub : {n : ℕ} → insn n
      eqz : {n : ℕ} → insn n
      dup : {n : ℕ} → insn n
      drop : {n : ℕ} → insn n
      block : {n : ℕ} → functype → List (insn (suc n)) → insn n
      if-else : {n : ℕ} → functype → List (insn (suc n)) → List (insn (suc n)) → insn n
      loop : {n : ℕ} → functype → List (insn (suc n)) → insn n
      br : {n : ℕ} → (l : Fin n) → insn n
      br-if : {n : ℕ} → (l : Fin n) → insn n

    vals : Set
    vals = List val

    insns : ℕ → Set
    insns n = List (insn n)

    -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
    frame : ℕ → Set
    frame n = vals × ℕ × insns n × insns n

    data frames : ℕ → Set where
      [] : frames zero
      _∷_ : {n : ℕ} → frame n → frames n → frames (suc n)

    state : ℕ → Set
    state n = frames n × vals × insns n

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
      show-insns : ∀{n} → insns n → String
      show-insns is = "[" ++ go is ++ "]" where
        go : ∀ {n} → insns n → String
        go [] = ""
        go (i ∷ []) = show-insn i
        go (i ∷ is) = show-insn i ++ " " ++ show-insns is

      show-insn : ∀{n} → insn n → String
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
      show-insn (br n) = concat-with-space ("br" ∷ NS.show (Fin.toℕ n) ∷ [])
      show-insn (br-if n) = concat-with-space ("br-if" ∷ NS.show (Fin.toℕ n) ∷ [])

    show-frame : ∀{n} → frame n → String
    show-frame (vs , a , l , is) = show-vals vs ++ "ℓ" ++ NS.show a ++ "{" ++ show-insns l ++ "}" ++ "*" ++ show-insns is

    show-frames : ∀{n} → frames n → String
    show-frames [] = ""
    show-frames (f ∷ fs) = show-frame f ++ " " ++ show-frames fs

    show-state : {n : Nat.ℕ} → state n → String
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
  open Category.Monad.Indexed
  open Product
  open Unit
  open Function
  open Nat
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

  state-machine : (ℕ → Set) → (ℕ → ℕ → Set → Set)
  state-machine S n m = IStateT S result n m

  state-machine-result : (ℕ → Set) → Set → (ℕ → Set)
  state-machine-result S X n = result (X × (S n))

  state-machine-monad : (S : ℕ → Set) → RawIMonad (state-machine S)
  state-machine-monad S = StateTIMonad S resultMonad

  lift-result : ∀{S X n} → result X → state-machine S n n X
  lift-result x s = do
    v ← x
    ok (v , s)
    where open RawMonad resultMonad

  pattern ok' a = ok (tt , a)

  record substate (S : ℕ → Set) (S' : ℕ → Set) : Set where
    field
      view : ∀{n} → S n → S' n
      update : ∀{n} → S n → S' n → S n
      eq : ∀{n} → ∀(x : S n) → update x (view x) PropositionalEquality.≡ x

  upgrade : {X : Set} → ∀{S S' n} → (substate S S') → state-machine S' n n X → state-machine S n n X
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
  open Category.Monad.Indexed
  open Sum
  open Product
  open Unit
  open List hiding (and)
  open Vec using (Vec ; _∷_ ; [])
  open Nat
  open Bool hiding (not)
  open Category.Monad.State
  open InterpreterCore public
  open Show
  open Fin


  interp-valtype : valtype → Set
  interp-valtype bool = Bool
  interp-valtype nat = ℕ
  interp-valtype unit = ⊤

  module _ where
    non-framed = state-machine (λ n → vals × insns n)
    non-framed-result = state-machine-result (λ n → vals × insns n)
    result-non-framed = λ n → result (vals × insns n)

    module non-framed-M = RawIMonad (state-machine-monad (λ n → vals × insns n))
    open non-framed-M

    push : ∀{n} → val → non-framed n n ⊤
    push v (vs , is) = ok' ((v ∷ vs) , is) 

    pop : ∀{n} → non-framed n n val
    pop (v ∷ vs , is) = ok (v , vs , is)
    pop _ = error "value stack underflow"
  
    chkval : ∀{n} → (t : valtype) → val → non-framed n n (interp-valtype t)
    chkval bool (bool b) = return b
    chkval nat (nat n) = return n
    chkval unit (unit tt) = return tt
    chkval expected v _ = error (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (actual v) ∷ "instead of" ∷ show-valtype expected ∷ [])
      where actual : val → valtype
            actual (bool _) = bool
            actual (nat _) = nat
            actual (unit _) = unit
  
    popchk : ∀{n} → (t : valtype) → non-framed n n (interp-valtype t)
    popchk t = pop >>= chkval t
  
    fetch : ∀{n} → non-framed n n (insn n)
    fetch (vs , (i ∷ is)) = ok (i , vs , is)
    fetch _ = error "no instuction to fetch"

  
    emit : ∀{n} → insn n → non-framed n n ⊤
    emit i (vs , is) = ok' (vs , i ∷ is)
  
    module NonFramed where
      einsn : ∀{n} → insn n → non-framed n n ⊤
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
        push $ nat ( x Nat.+ y )
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
  
      eistep : ∀{n} → non-framed n n ⊤
      eistep s@(v , []) = ok' s
      eistep s@(v , i ∷ is) = (fetch >>= einsn) s


  module _ where
    framed = state-machine (λ n → frames n × vals × insns n)
    framed-result = state-machine-result (λ n → frames n × vals × insns n)

    module framed-M = RawIMonad (state-machine-monad (λ n → frames n × vals × insns n))
    open framed-M 

    lift' : ∀{X : Set} → ∀ {n} → non-framed n n X → framed n n X
    lift' {X} {n} nf (fs , vs , is) = f (nf (vs , is))
      where f : non-framed-result X n → framed-result X n
            f (ok (x , s)) = ok (x , fs , s)
            f (error e) = (error e)

    prepend : ∀{n} → insns n → framed n n ⊤
    prepend is' (fs , vs , is) = ok' (fs , vs , is' ++ is)

    append : ∀{n} → vals → framed n n ⊤
    append vs' (fs , vs , is) = ok' (fs , vs' ++ vs , is)

    split : ∀{n} → ℕ → framed n n vals
    split n (fs , vs , is) = ok (take n vs , fs , List.drop n vs , is)
  
    vswap : ∀{n} → vals → framed n n vals
    vswap vs (fs , vs' , is) = ok (vs' , fs , vs , is)

    enter : ∀{n} → vals → ℕ → insns n → insns (suc n) → framed n (suc n) ⊤
    enter vs' a l is' (fs , vs , is) = ok' ((vs , a , l , is) ∷ fs , vs' , is')
  
    leave : ∀{n} → framed (suc n) n (vals × ℕ × insns n)
    leave ((vs , a , l , is) ∷ fs , vs' , is') = ok ((vs' , a , l) , fs , vs , is)
  
    open import Relation.Binary.PropositionalEquality
    toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
    toℕ-fromℕ zero = refl
    toℕ-fromℕ (suc n) = cong suc (toℕ-fromℕ n)

    br-helper : ∀{n} → (m : Fin (suc n)) → framed (suc n) (n ∸ (toℕ m)) ⊤
    br-helper {n} zero = do
      let p = subst (λ x → framed (suc n) x (vals × ℕ × insns n)) (sym (toℕ-fromℕ n))
      (vs , a , lcont) ← leave
      prepend lcont
      append (take a vs)
    br-helper {suc n} (suc m) = do
      (vs , _ , _) ← leave
      vswap vs
      br-helper m

    eenter : ∀{n} → insn n → framed n (suc n) ⊤
    eenter (block (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length b , [] , is)
    eenter (if-else (a ⇒ b) ist isf) = do
      p ← lift (popchk bool)
      vs ← split (length a)
      if p then enter (vs , length b , [] , ist)
           else enter (vs , length b , [] , isf)
    eenter (loop (a ⇒ b) is) = do
      vs ← split (length a)
      enter (vs , length a , loop (a ⇒ b) is ∷ [] , is)
    eenter _ = error "unsupported instruction"

    eend : ∀{n} → framed (suc n) n ⊤
    eend = do
      vs , _ , _ , _ ← leave
      append vs
  
    -- When we define frames as a type family indexed by a natural number, type of state which includes frames also be indexed by a natural number.
    -- Then, its small-step state transition can be indexed by a pair of natural number (a pair of indices of pre- and post-state).
    -- Similary, should each instruction be indexed by a pair of natural number?
    ebr : ∀{n} → insn (suc n) → framed (suc n) (n ∸ (toℕ m)) ⊤
    ebr (br n) = br-helper n
    ebr (br-if n) = lift (popchk bool) >>= λ where
      false → return tt
      true → br-helper n
    ebr _ = error "unsupported instruction"


    estep : framed ⊤
    estep (fs , vs , nop ∷ is) = (lift NonFramed.eistep) (fs , vs , nop ∷ is)
    estep (fs , vs , const v ∷ is) = (lift NonFramed.eistep) (fs , vs , insn.const v ∷ is)
    estep (fs , vs , and ∷ is) = (lift NonFramed.eistep) (fs , vs , and ∷ is)
    estep (fs , vs , not ∷ is) = (lift NonFramed.eistep) (fs , vs , not ∷ is)
    estep (fs , vs , add ∷ is) = (lift NonFramed.eistep) (fs , vs , add ∷ is)
    estep (fs , vs , sub ∷ is) = (lift NonFramed.eistep) (fs , vs , sub ∷ is)
    estep (fs , vs , eqz ∷ is) = (lift NonFramed.eistep) (fs , vs , eqz ∷ is)
    estep (fs , vs , dup ∷ is) = (lift NonFramed.eistep) (fs , vs , dup ∷ is)
    estep (fs , vs , drop ∷ is) = (lift NonFramed.eistep) (fs , vs , insn.drop ∷ is)
    estep (fs , vs , block t is' ∷ is) = eenter (block t is') (fs , vs , is)
    estep (fs , vs , if-else t is' is'' ∷ is) = eenter (if-else t is' is'') (fs , vs , is)
    estep (fs , vs , loop t is' ∷ is) = eenter (loop t is') (fs , vs , is)
    estep (fs , vs , br n ∷ is) = ebr (br n) (fs , vs , is)
    estep (fs , vs , br-if n ∷ is) = ebr (br-if n) (fs , vs , is)
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
