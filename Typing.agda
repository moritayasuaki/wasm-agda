open import Wasm

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
import Category.Monad.State using (IStateT ; StateTIMonad)
import Category.Monad.Continuation using (DContT ; DContIMonad)

open Wasm.Wasm

module Typing where
  open String using (String)
  open Syntax 
  open Category.Monad
  open IExc
  open Sum
  open Product
  open Fin
  open List using (_∷_ ; [] ; [_] ; _++_ ; length ; lookup ; List)
  open functype


  labelstype = List resulttype

  infix 4.9 _/_ 
  record lresulttype : Set where
    constructor _/_
    field
      main : resulttype
      labels : labelstype

  infix 4.5 _↠_
  record ctxtype {X : Set} : Set where
    constructor _↠_
    field
      delim : X
      answer : resulttype

  record scopetype : Set where
    constructor sc
    field
      vstacktype : resulttype
      outputtype : resulttype

  record frametype : Set where
    constructor fr
    field
      vstacktype : resulttype
      labeltype : resulttype
      outputtype : resulttype

  infix 2 _∈-v_
  infix 2 _∈-vs_
  infix 2 _∈-i_
  infix 2 _∈-is_
  infix 2 _∈-fs_
  infix 2 _∈-s_
  data _∈-v_ : val → valtype → Set where
    tbool : ∀{b} → cbool b ∈-v bool
    tnat : ∀{n} → cnat n ∈-v nat
    tunit : cunit Unit.tt ∈-v unit

  data _∈-vs_ : vals → resulttype → Set where
    tvempty : [] ∈-vs []
    tvstack : ∀{v t vs ts} → v ∈-v t → vs ∈-vs ts → v ∷ vs ∈-vs t ∷ ts

  mutual
    data _∈-i_ : insn → functype → Set where
      tconst : ∀{v t} → v ∈-v t → const v ∈-i [] ⇒ [ t ] / []
      tnop : nop ∈-i [] ⇒ [] / []
      tnot : not ∈-i [ bool ] ⇒ [ bool ] / []
      tand : and ∈-i (bool ∷ bool ∷ []) ⇒ [ bool ] / []
      tadd : add ∈-i (nat ∷ nat ∷ []) ⇒ [ nat ] / []
      tsub : sub ∈-i (nat ∷ nat ∷ []) ⇒ [ nat ] / []
      teqz : eqz ∈-i [ nat ] ⇒ [ bool ] / []
      tdup : ∀{t} → dup ∈-i [ t ] ⇒ t ∷ t ∷ [] / []
      tdrop : ∀{t} → drop ∈-i [ t ] ⇒ [] / []
      tblock : ∀{is a b ks}
        → is ∈-is a ⇒ b / b ∷ ks
        → block (a ⇒ b) is ∈-i a ⇒ b / ks
      tif-else : ∀{ist isf a ks b}
        → ist ∈-is a ⇒ b / b ∷ ks
        → isf ∈-is a ⇒ b / b ∷ ks
        → if-else (a ⇒ b) ist isf ∈-i bool ∷ a ⇒ b / ks
      tloop : ∀{is a b ks}
        → is ∈-is a ⇒ b / a ∷ ks
        → loop (a ⇒ b) is ∈-i a ⇒ b / ks
      tbrn : ∀{ks b} → {n : Fin (length ks)} → br (toℕ n) ∈-i lookup ks n ⇒ b / ks
  
    data _∈-is_ : insns → functype → Set where
      tiempty : ∀ {a ks} → [] ∈-is a ⇒ a / ks
      tiseq : ∀ {i is a b c d ks} → i ∈-i a ⇒ b / ks → is ∈-is b ++ d ⇒ c / ks → i ∷ is ∈-is a ++ d ⇒ c / ks

  data _∈-fs_ : frames → ctxtype → Set where
    tfempty : ∀ {a} → [] ∈-fs (a / [] ↠ a)
    tfstack : ∀ {vs l cont r k a b c fs ks}
              → vs ∈-vs r
              → l ∈-i k ⇒ a / ks
              → cont ∈-is a ++ r ⇒ b / ks
              → fs ∈-fs b / ks ↠ c
              → (vs , length k , l , cont) ∷ fs ∈-fs a / k ∷ ks ↠ c

  data _∈-s_ : state → resulttype → Set where
    tstate : ∀ {fs vs is a b c ks}
             → fs ∈-fs b / ks ↠ c
             → vs ∈-vs a
             → is ∈-is a ⇒ b / ks
             → (fs , vs , is) ∈-s c

  ∈-vs-append : ∀ {vs vs' ts ts' } → vs ∈-vs ts → vs' ∈-vs ts' → vs ++ vs' ∈-vs ts ++ ts'
  ∈-vs-append tvempty ps' = ps'
  ∈-vs-append (tvstack p ps) ps' = tvstack p (∈-vs-append ps ps')

  open Interpreter
  open import Relation.Binary.PropositionalEquality


  safety : ∀{t} → (st : state) → st ∈-s t → ∃ λ st' → (eval1 st ≡ ok st') × (st' ∈-s t)
  safety ([] , vs , []) p = ([] , vs , []) , (refl , p)
  safety ((vs , _ , _ , cont) ∷ fs , vs' , []) (tstate (tfstack pvs _ pcont pfs) pvs' tiempty) = (fs , vs' ++ vs , cont) , (refl , tstate pfs (∈-vs-append pvs' pvs) pcont)
  safety ([] , vs , (const v) ∷ is) (tstate pfs pvs (tiseq (tconst pv) pis)) = ([] , (v ∷ vs) , is) , (refl , tstate pfs (tvstack pv pvs) pis)
  safety (f ∷ fs , vs , (const v) ∷ is) (tstate pfs pvs (tiseq (tconst pv) pis)) = (f ∷ fs , (v ∷ vs) , is) , (refl , tstate pfs (tvstack pv pvs) pis)
  safety ([] , vs , nop ∷ is) (tstate pfs pvs (tiseq tnop pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
--   safety (fs , (cbool b) ∷ vs , not ∷ is) (tstate pfs (tvstack pv pvs) (tiseq tnot pis)) = (fs , (cbool (Bool.not b)) ∷ vs , is) , (refl , tstate pfs (tvstack tbool pvs) pis)
  safety ([] , (cbool b) ∷ (cbool b') ∷ vs , and ∷ is) (tstate pfs (tvstack tbool (tvstack tbool pvs)) (tiseq tand pis)) = ([] , (cbool (b Bool.∧ b')) ∷ vs , is) , (refl , tstate pfs (tvstack tbool pvs) pis)

--  safety ((vs' , _ , _ , cont) ∷ fs , vs , []) (tstate (tfstack pvs' _ pcont pfs) pvs _) = (fs , vs ++ vs' , cont) , (refl , tstate pfs (∈-vs-append pvs pvs') pcont)
