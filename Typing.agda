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
  open import Data.List.Properties

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
  infix 2 _∈-i''_
  infix 2 _∈-i'_
  infix 2 _∈-is_
  infix 2 _∈-fs_
  infix 2 _∈-s_
  data _∈-v_ : val → valtype → Set where
    tbool : ∀{b} → cbool b ∈-v bool
    tnat : ∀{n} → cnat n ∈-v nat
    tunit : cunit Unit.tt ∈-v unit

  data _∈-vs_ : vals → resulttype → Set where
    tv[] : [] ∈-vs []
    _tv∷_ : ∀{t ts v vs} → v ∈-v t → vs ∈-vs ts → v ∷ vs ∈-vs t ∷ ts

  data non-empty {X : Set} : List X → Set where
    singleton : ∀{x} → non-empty (x ∷ [])
    more : ∀{x xs} → non-empty xs → non-empty (x ∷ xs)

  mutual
    data _∈-i''_ : insn → functype → Set where
      tconst : ∀{t v} → v ∈-v t → const v ∈-i'' [] ⇒ t ∷ []
      tnop : nop ∈-i'' [] ⇒ []
      tnot : not ∈-i'' bool ∷ [] ⇒ bool ∷ []
      tand : and ∈-i'' bool ∷ bool ∷ [] ⇒ bool ∷ []
      tadd : add ∈-i'' nat ∷ nat ∷ [] ⇒ nat ∷ []
      tsub : sub ∈-i'' nat ∷ nat ∷ [] ⇒ nat ∷ []
      teqz : eqz ∈-i'' nat ∷ [] ⇒ bool ∷ []
      tdup : ∀{t} → dup ∈-i'' t ∷ [] ⇒ t ∷ t ∷ []
      tdrop : ∀{t} → drop ∈-i'' t ∷ [] ⇒ []

    data _∈-i'_ : insn → functype → Set where
      tinsn : ∀{a b ks i} → i ∈-i'' a ⇒ b → i ∈-i' a ⇒ b / []
      tblock : ∀{is a b ks}
        → is ∈-is a ⇒ b / b ∷ ks
        → block (a ⇒ b) is ∈-i' a ⇒ b / ks
      tif-else : ∀{ist isf a ks b}
        → ist ∈-is a ⇒ b / b ∷ ks
        → isf ∈-is a ⇒ b / b ∷ ks
        → if-else (a ⇒ b) ist isf ∈-i' bool ∷ a ⇒ b / ks
      tloop : ∀{is a b ks}
        → is ∈-is a ⇒ b / a ∷ ks
        → loop (a ⇒ b) is ∈-i' a ⇒ b / ks
      tbrn : ∀{ks b n}
        → (n' : Fin (length ks))
        → n ≡ toℕ n'
        → br n ∈-i' lookup ks n' ⇒ b / ks

    data _∈-i_ : insn → functype → Set where
      tiup : ∀ {b' a' ks' a ks i}
           → i ∈-i' a' ⇒ b' / ks'
           → {a' ≡ List.take (length a') a} → {ks' ≡ List.take (List.length ks') ks}
           → i ∈-i a ⇒ (b' ++ List.drop (List.length a') a) / ks

    data _∈-is_ : insns → functype → Set where
      ti[] : ∀ {a ks} → [] ∈-is a ⇒ a / ks
      _ti∷_ : ∀ {b ks i is a c} → i ∈-i a ⇒ b / ks → is ∈-is b ⇒ c / ks → i ∷ is ∈-is a ⇒ c / ks

  data _∈-fs_ : frames → ctxtype → Set where
    tf[] : ∀ {a} → [] ∈-fs a / [] ↠ a
    _tf∷_ : ∀ {k ks a b r vs lcont cont c fs}
              → (vs ∈-vs r) × (lcont ∈-is k ⇒ a / ks) × (cont ∈-is a ++ r ⇒ b / ks)
              → fs ∈-fs b / ks ↠ c
              → (vs , length k , lcont , cont) ∷ fs ∈-fs a / k ∷ ks ↠ c

  data _∈-s_ : state → resulttype → Set where
    tstate : ∀ {a b c ks fs vs is}
             → fs ∈-fs b / ks ↠ c
             → vs ∈-vs a
             → is ∈-is a ⇒ b / ks
             → (fs , vs , is) ∈-s c

  _tv++_ : ∀ {vs vs' ts ts'} → vs ∈-vs ts → vs' ∈-vs ts' → vs ++ vs' ∈-vs ts ++ ts'
  _tv++_ tv[] ps' = ps'
  _tv++_ (p tv∷ ps) ps' = p tv∷ (ps tv++ ps')

  _ti++_ : ∀ {is is' a b c ks} → (is ∈-is a ⇒ b / ks) → (is' ∈-is b ⇒ c / ks) → is ++ is' ∈-is a ⇒ c / ks
  _ti++_ ti[] pis' = pis'
  _ti++_ (pi ti∷ pis) pis' = pi ti∷ (pis ti++ pis')

  tvtake : ∀ {vs ts} → ( n : Nat.ℕ ) → vs ∈-vs ts → List.take n vs ∈-vs List.take n ts
  tvtake Nat.zero _ = tv[]
  tvtake (Nat.suc n) tv[] = tv[]
  tvtake (Nat.suc n) (p tv∷ ps) = p tv∷ (tvtake n ps)

  tvdrop : ∀ {vs ts} → ( n : Nat.ℕ ) → vs ∈-vs ts → List.drop n vs ∈-vs List.drop n ts
  tvdrop Nat.zero p = p
  tvdrop (Nat.suc n) tv[] = tv[]
  tvdrop (Nat.suc n) (p tv∷ ps) = (tvdrop n ps)

  take-length : ∀{X : Set} → ∀{ys : List X} → (xs : List X) → xs ≡ List.take (List.length xs) (xs ++ ys)
  take-length [] = refl
  take-length (x ∷ xs) = cong (x ∷_) (take-length xs)

  lookup-zero : ∀{X : Set} → ∀{xs : List X} → (x : X) → x ≡ lookup (x ∷ xs) zero
  lookup-zero x = refl

  length-take-lookup-zero : ∀ {X : Set} → (k : List X) → (ks : List (List X)) → {ts : List X} → k ≡ List.take (length k) (lookup (k ∷ ks) zero ++ ts)
  length-take-lookup-zero k ks {ts} = subst (λ x → k ≡ List.take (List.length k) (x ++ ts)) (lookup-zero {_} {ks} k) (take-length k)

  open Interpreter

  safety : ∀{t} → (st : state) → st ∈-s t → ∃ λ st' → (estep st ≡ ok' st') × (st' ∈-s t)
  safety ([] , vs , []) p = ([] , vs , []) , (refl , p)
  safety ((vs , _ , _ , cont) ∷ fs , vs' , []) (tstate ((pvs , _ , pcont) tf∷ pfs) pvs' ti[]) = (fs , vs' ++ vs , cont) , (refl , tstate pfs (pvs' tv++ pvs) pcont)
  safety ([] , cnat n' ∷ vs , eqz ∷ is) (tstate pfs (tnat tv∷ pvs) ((tiup (tinsn teqz)) ti∷ pis)) = ([] , (cbool (feqz n')) ∷ vs , is) , (refl , tstate pfs (tbool tv∷ pvs) pis)
  safety ([] , vs , const v ∷ is) (tstate pfs pvs ((tiup (tinsn (tconst pv))) ti∷ pis)) = ([] , (v ∷ vs) , is) , (refl , tstate pfs (pv tv∷ pvs) pis)
  safety ([] , vs , nop ∷ is) (tstate pfs pvs (tiup (tinsn tnop) ti∷ pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
  safety ([] , cbool b ∷ vs , not ∷ is) (tstate pfs (tbool tv∷ pvs) (tiup (tinsn tnot) ti∷ pis)) = ([] , (cbool (Bool.not b)) ∷ vs , is) , (refl , tstate pfs (tbool tv∷ pvs) pis)
  safety ([] , cbool b ∷ cbool b' ∷ vs , and ∷ is) (tstate pfs (tbool tv∷ (tbool tv∷ pvs)) ((tiup (tinsn tand)) ti∷ pis)) = ([] , (cbool (b Bool.∧ b')) ∷ vs , is) , (refl , tstate pfs (tbool tv∷ pvs) pis)
  safety ([] , v ∷ vs , drop ∷ is) (tstate pfs (pv tv∷ pvs) (tiup (tinsn tdrop) ti∷ pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
  safety ([] , cnat n ∷ cnat m ∷ vs , sub ∷ is) (tstate pfs (tnat tv∷ (tnat tv∷ pvs)) (tiup (tinsn tsub) ti∷ pis)) = ([] , (cnat (n Nat.∸ m) ∷ vs , is)) , (refl , tstate pfs (tnat tv∷ pvs) pis)
  safety ([] , v ∷ vs , dup ∷ is) (tstate pfs (_tv∷_ {t1} pv pvs) ((tiup {b} {ks} (tinsn (tdup {t})) {pp}) ti∷ pis)) = ([] , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv tv∷ (pv tv∷ pvs)) pis)
  safety ((vs' , n , lcont , cont) ∷ [] , vs , br l ∷ is) (tstate ((pvs' , plcont , pcont) tf∷ pfs) pvs (pi ti∷ pis)) =
    ([] , List.take n vs ++ vs' , lcont ++ cont) , (refl , tstate pfs ( (tvtake n pvs) tv++ pvs') (plcont ti++ pcont))

