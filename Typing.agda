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

open Wasm

module Typing where
  open String using (String)
  open Syntax 
  open Category.Monad
  open Sum
  open Product
  open Fin
  open List using (_∷_ ; [] ; [_] ; _++_ ; length ; lookup ; List)
  open functype
  open import Relation.Binary.PropositionalEquality


  labelstype = List resulttype

  infix 4.9 _/_ 
  record lresulttype : Set where
    constructor _/_
    field
      main : resulttype
      labels : labelstype

  infix 4.5 _↠_
  record ctxtype : Set where
    constructor _↠_
    field
      delim : lresulttype
      answer : resulttype

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
      tconst : ∀{v t ts ks} → v ∈-v t → const v ∈-i ts ⇒ t ∷ ts / ks
      tnop : ∀{ts ks} → nop ∈-i ts  ⇒ ts / ks
      tnot : ∀{ts ks} → not ∈-i bool ∷ ts ⇒ bool ∷ ts / ks
      tand : ∀{ts ks} → and ∈-i bool ∷ bool ∷ ts ⇒ bool ∷ ts / ks
      tadd : ∀{ts ks} → add ∈-i nat ∷ nat ∷ ts ⇒ nat ∷ ts / ks
      tsub : ∀{ts ks} → sub ∈-i nat ∷ nat ∷ ts ⇒ nat ∷ ts / ks
      teqz : ∀{ts ks} → eqz ∈-i nat ∷ ts ⇒ bool ∷ ts / ks
      tdup : ∀{t ts ks } → dup ∈-i t ∷ ts ⇒ t ∷ t ∷ ts / ks
      tdrop : ∀{t ts ks} → drop ∈-i t ∷ [] ⇒ [] / ks
      tblock : ∀{is a b ks}
        → is ∈-is a ⇒ b / b ∷ ks
        → block (a ⇒ b) is ∈-i a ⇒ b / ks
      tif-else : ∀{ist isf a ks b ts}
        → ist ∈-is a ⇒ b / b ∷ ks
        → isf ∈-is a ⇒ b / b ∷ ks
        → if-else (a ⇒ b) ist isf ∈-i bool ∷ a ⇒ b / ks
      tloop : ∀{is a b ks}
        → is ∈-is a ⇒ b / a ∷ ks
        → loop (a ⇒ b) is ∈-i a ⇒ b / ks
      tbrn : ∀{ks b n}
        → (n' : Fin (length ks))
        → n ≡ toℕ n'
        → br n ∈-i lookup ks n' ⇒ b / ks

    data _∈-is_ : insns → functype → Set where
      tiempty : ∀ {a ks} → [] ∈-is a ⇒ a / ks
      tiseq : ∀ {r i is a b c ks} → i ∈-i a ⇒ b / ks → is ∈-is b ++ r ⇒ c / ks → i ∷ is ∈-is a ++ r ⇒ c / ks

  data _∈-fs_ : frames → ctxtype → Set where
    tfempty : ∀ {a} → [] ∈-fs (a / [] ↠ a)
    tfstack : ∀ {k ks a b r vs l cont  c fs}
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


  ∈-vs-append : ∀ {vs vs' ts ts'} → vs ∈-vs ts → vs' ∈-vs ts' → vs ++ vs' ∈-vs ts ++ ts'
  ∈-vs-append tvempty ps' = ps'
  ∈-vs-append (tvstack p ps) ps' = tvstack p (∈-vs-append ps ps')

  ∈-vs-take : ∀ {vs ts} → ( n : Nat.ℕ ) → vs ∈-vs ts → List.take n vs ∈-vs List.take n ts
  ∈-vs-take Nat.zero _ = tvempty
  ∈-vs-take (Nat.suc n) tvempty = tvempty
  ∈-vs-take (Nat.suc n) (tvstack p ps) = tvstack p (∈-vs-take n ps)

  length-take : ∀{X : Set} → ∀{ys : List X} → (xs : List X) → List.take (List.length xs) (xs ++ ys) ≡ xs
  length-take [] = refl
  length-take (x ∷ xs) = cong (x ∷_) (length-take xs)

  lookup-zero : ∀{X : Set} → ∀{xs : List X} → (x : X) → lookup (x ∷ xs) zero ≡ x
  lookup-zero x = refl

  length-take-lookup-zero : ∀ {X : Set} → (k : List X) → (ks : List (List X)) → {ts : List X} → List.take (length k) (lookup (k ∷ ks) zero ++ ts) ≡ k
  length-take-lookup-zero k ks {ts} = subst (λ x → List.take (List.length k) (x ++ ts) ≡ k) (lookup-zero {_} {ks} k) (length-take k)

  open Interpreter
  eval1 : state → error state
  eval1 st with estep st
  ...         | ok (Unit.tt , st') = ok st'
  ...         | err msg st' = err msg st'

  safety : ∀{t} → (st : state) → st ∈-s t → ∃ λ st' → (eval1 st ≡ ok st') × (st' ∈-s t)
  safety ([] , vs , []) p = ([] , vs , []) , (refl , p)
  safety ((vs , _ , _ , cont) ∷ fs , vs' , []) (tstate (tfstack pvs _ pcont pfs) pvs' tiempty) = (fs , vs' ++ vs , cont) , (refl , tstate pfs (∈-vs-append pvs' pvs) pcont)
  safety ((vs' , n , l , cont) ∷ fs , vs , br Nat.zero ∷ is) (tstate (tfstack {k} {ks} {a} {b} {r} pvs' pl pcont pfs) pvs (tiseq (tbrn Fin.zero p) pis)) =
    (fs , List.take n vs ++ vs' , l ∷ cont) , (refl , tstate pfs (∈-vs-append (∈-vs-take n pvs) pvs') tmp)
       where tmp = subst (λ x → l ∷ cont ∈-is x ++ r ⇒ b / ks) (sym (length-take-lookup-zero k ks {_})) (tiseq pl pcont)
  safety ([] , vs , (const v) ∷ is) (tstate pfs pvs (tiseq (tconst pv) pis)) = ([] , (v ∷ vs) , is) , (refl , tstate pfs (tvstack pv pvs) pis)
  safety (f ∷ fs , vs , (const v) ∷ is) (tstate pfs pvs (tiseq (tconst pv) pis)) = (f ∷ fs , (v ∷ vs) , is) , (refl , tstate pfs (tvstack pv pvs) pis)
  safety ([] , vs , nop ∷ is) (tstate pfs pvs (tiseq tnop pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
  safety (f ∷ fs , vs , nop ∷ is) (tstate pfs pvs (tiseq tnop pis)) = (f ∷ fs , vs , is) , (refl , tstate pfs pvs pis)
  safety ([] , cbool b ∷ vs , not ∷ is) (tstate pfs (tvstack tbool pvs) (tiseq tnot pis)) = ([] , (cbool (Bool.not b)) ∷ vs , is) , (refl , tstate pfs (tvstack tbool pvs) pis)
  safety (f ∷ fs , cbool b ∷ vs , not ∷ is) (tstate pfs (tvstack tbool pvs) (tiseq tnot pis)) = (f ∷ fs , (cbool (Bool.not b)) ∷ vs , is) , (refl , tstate pfs (tvstack tbool pvs) pis)
  safety ([] , (cbool b) ∷ (cbool b') ∷ vs , and ∷ is) (tstate pfs (tvstack tbool (tvstack tbool pvs)) (tiseq tand pis)) = ([] , (cbool (b Bool.∧ b')) ∷ vs , is) , (refl , tstate pfs (tvstack tbool pvs) pis)
  safety (f ∷ fs , (cbool b) ∷ (cbool b') ∷ vs , and ∷ is) (tstate pfs (tvstack tbool (tvstack tbool pvs)) (tiseq tand pis)) = (f ∷ fs , (cbool (b Bool.∧ b')) ∷ vs , is) , (refl , tstate pfs (tvstack tbool pvs) pis)
  safety ([] , v ∷ vs , drop ∷ is) (tstate pfs (tvstack pv pvs) (tiseq tdrop pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
  safety (f ∷ fs , v ∷ vs , drop ∷ is) (tstate pfs (tvstack pv pvs) (tiseq tdrop pis)) = (f ∷ fs , vs , is) , (refl , tstate pfs pvs pis)
