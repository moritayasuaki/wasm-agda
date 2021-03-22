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

    vals : Set
    vals = List val

    insns : ℕ → Set
    insns n = List (insn' n)

    -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
    frame' : ℕ → Set
    frame' n = vals × Nat.ℕ × (insns n) × (insns n)

    data frames : ℕ → Set where
      [] : frames zero
      _∷_ : ∀{n} → frame' n → frames n → frames (suc n)

    state' : ℕ → Set
    state' n = frames n × vals × insns n

    state = ∃ λ n → state' n

  module _ where
    open String
    open List hiding (_++_)
    open import Data.Nat.Show as NS
    open import Data.Bool.Show as BS
    open Show
    open Nat
    open Fin

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
        go : ∀{n} → insns n → String
        go [] = ""
        go (i ∷ []) = show-insn' i
        go (i ∷ is) = show-insn' i ++ " " ++ show-insns is

      show-insn' : ∀{n} → insn' n → String
      show-insn' (const' n) = concat-with-space ("const" ∷ show-val n ∷ [])
      show-insn' nop' = "nop"
      show-insn' not' = "not"
      show-insn' and' = "and"
      show-insn' add' = "add"
      show-insn' sub' = "sub"
      show-insn' eqz' = "eqz"
      show-insn' dup' = "dup"
      show-insn' drop' = "drop"
      show-insn' (block' ft is) = concat-with-space ("block" ∷ show-functype ft ∷ show-insns is ∷ [])
      show-insn' (if-else' ft ist isf) = concat-with-space ("if" ∷ show-functype ft ∷ show-insns ist ∷ show-insns isf ∷ [])
      show-insn' (loop' ft is) = concat-with-space ("loop" ∷ show-functype ft ∷ show-insns is ∷ [])
      show-insn' (br' n) = concat-with-space ("br" ∷ NS.show (toℕ n) ∷ [])
      show-insn' (br-if' n) = concat-with-space ("br-if" ∷ NS.show (toℕ n) ∷ [])

    show-frame : ∀{n} → frame' n → String
    show-frame (vs , a , l , is) = show-vals vs ++ "ℓ" ++ NS.show a ++ "{" ++ show-insns l ++ "}" ++ "*" ++ show-insns is

    show-frames : ∀{n} → frames n → String
    show-frames fs = "[" ++ go fs ++ "]" where
      go : ∀{n} → frames n → String
      go [] = ""
      go (f ∷ []) = show-frame f
      go (f ∷ fs) = show-frame f ++ " " ++ show-frames fs

    show-state : state → String
    show-state (n , fs , vs , is) = "(" ++ show-frames fs ++ ", " ++ show-vals vs ++ ", " ++ show-insns is ++ ")"

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
  open Fin


  interp-valtype : valtype → Set
  interp-valtype bool = Bool
  interp-valtype nat = ℕ
  interp-valtype unit = ⊤

  st = state-machine (state)
  module st-M = RawMonad (state-machine-monad state)
  open st-M
  module _ where
    push : val → st ⊤
    push v (n , fs , vs , is) = ok' (n , fs , (v ∷ vs) , is) 

    pop : st val
    pop (n , fs , v ∷ vs , is) = ok (v , n , fs , vs , is)
    pop _ = error "value stack underflow"
  
    chkval : (t : valtype) → val → st (interp-valtype t)
    chkval bool (bool b) = return b
    chkval nat (nat n) = return n
    chkval unit (unit tt) = return tt
    chkval expected v _ = error (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (actual v) ∷ "instead of" ∷ show-valtype expected ∷ [])
      where actual : val → valtype
            actual (bool _) = bool
            actual (nat _) = nat
            actual (unit _) = unit
  
    popchk : (t : valtype) → st (interp-valtype t)
    popchk t = pop >>= chkval t

    append : vals → st ⊤
    append vs' (n , fs , vs , is) = ok' (n , fs , vs' ++ vs , is)

    split : ℕ → st vals
    split n (n' , fs , vs , is) = ok (take n vs , n' , fs , List.drop n vs , is)
  
    vswap : vals → st vals
    vswap vs (n , fs , vs' , is) = ok (vs' , n , fs , vs , is)

    br-helper : ∀{n} → (m : Fin n) → (frames n × vals) → state
    br-helper {suc n} zero ((vs' , m , lis , cis) ∷ fs , vs) = (n , fs , (take m vs) ++ vs' , lis ++ cis)
    br-helper (suc m) ((_ , _ , lis , cis) ∷ fs , vs) = br-helper m (fs , vs)

    einsn : ∀ {n} → insn' n → st ⊤
    einsn (const' v) = do push v
    einsn nop' = return tt
    einsn and' = do
        x ← popchk bool
        y ← popchk bool
        push $ bool $ x ∧ y
    einsn not' = do
        x ← popchk bool
        push $ bool $ Bool.not x
    einsn add' = do
        x ← popchk nat
        y ← popchk nat
        push $ nat ( x Nat.+ y )
    einsn sub' = do
        x ← popchk nat
        y ← popchk nat
        push $ nat ( x ∸ y )
    einsn eqz' = do
        n ← popchk nat
        push $ bool (feqz n)
    einsn dup' = do
        v ← pop
        push v
        push v
    einsn drop' = do
        pop
        return tt
    einsn _ _ = error "unsupported instruction"

    estep : st ⊤
    estep (n , fs , vs , br' m ∷ is) = ok' (br-helper m (fs , vs))
    estep (n , fs , vs , nop' ∷ is) = einsn {n} nop' (n , fs , vs , is)
    estep (n , fs , vs , const' v ∷ is) = einsn {n} (const' v) (n , fs , vs , is)
    estep (n , fs , vs , and' ∷ is) = einsn {n} and' (n , fs , vs , is)
    estep (n , fs , vs , not' ∷ is) = einsn {n} not' (n , fs , vs , is)
    estep (n , fs , vs , add' ∷ is) = einsn {n} add' (n , fs , vs , is)
    estep (n , fs , vs , sub' ∷ is) = einsn {n} sub' (n , fs , vs , is)
    estep (n , fs , vs , dup' ∷ is) = einsn {n} dup' (n , fs , vs , is)
    estep (n , fs , vs , drop' ∷ is) = einsn {n} drop' (n , fs , vs , is)
    estep (n , fs , vs , block' (a ⇒ b) is' ∷ is) = ok' (suc n , f ∷ fs , vs' , is')
      where lena = length a
            vs' = List.take lena vs
            vs'' = List.drop lena vs
            f = (vs'' , lena , [] , is)
    estep (n , fs , (bool true) ∷ vs , if-else' (a ⇒ b) is' is'' ∷ is) = ok' (suc n , f ∷ fs , vs' , is')
      where lena = length a
            vs' = List.take lena vs
            vs'' = List.drop lena vs
            f = (vs'' , lena , [] , is)
    estep (n , fs , (bool false) ∷ vs , if-else' (a ⇒ b) is' is'' ∷ is) = ok' (suc n , f ∷ fs , vs' , is'')
      where lena = length a
            vs' = List.take lena vs
            vs'' = List.drop lena vs
            f = (vs'' , lena , [] , is)
    estep (n , fs , vs , loop' (a ⇒ b) is' ∷ is) = ok' (suc n , f ∷ fs , vs' , is')
      where lena = length a
            lenb = length b
            vs' = List.take lena vs
            vs'' = List.drop lena vs
            f = (vs'' , lenb , loop' (a ⇒ b) is' ∷ [] , is)

    estep (n , [] , vs , []) = ok' (n , [] , vs , [])
    estep ((suc n) , (vs' , l , lis , cis) ∷ fs , vs , []) = ok' (n , fs , vs ++ vs' , cis)
    estep _ = error "error"

 
{-
  module _ where


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

-}
