open import Wasm
open import Monad

import Category.Monad.Indexed
import Category.Monad
import Category.Applicative.Indexed
import Data.List as List
import Function
import Level
import Data.Fin as Fin hiding (_≟_)

import Data.Unit as Unit hiding (_≟_)
import Data.Product as Product
import Data.Sum as Sum

import Data.Nat as Nat
import Data.Bool as Bool
import Data.Empty as Empty
import Data.String as String
import Data.Maybe as Maybe
import Category.Monad.State using (IStateT ; StateTIMonad)
import Category.Monad.Continuation using (DContT ; DContIMonad)

module Typing where
  open String using (String)
  open Syntax 
  open Category.Monad
  open Sum
  open Product
  open Fin
  open Unit
  open Empty
  open Maybe using (Maybe ; just ; nothing)
  open Bool using (Bool ; if_then_else_ ; true ; false)
  open Nat using (ℕ)
  open List using (_∷_ ; [] ; [_] ; _++_ ; length ; lookup ; List)
  open Function using (_$_ ; id)
  open arrow
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.Structures
  open import Relation.Nullary
  open import Data.List.Properties

  labelstype = List resulttype

  infix 4.9 _/_ 
  record slash (X : Set) (Y : Set): Set where
    constructor _/_
    field
      right : X
      left : Y

  lresulttype  = slash resulttype labelstype
  lfunctype = arrow resulttype lresulttype
  lctxtype = arrow lresulttype lresulttype
  ctxtype = arrow lresulttype resulttype

  eqvt : valtype → valtype → Bool
  eqvt bool bool = true
  eqvt nat nat = true
  eqvt unit unit = true
  eqvt _ _ = false

  eqrt : resulttype → resulttype → Bool
  eqrt (x ∷ xs) (y ∷ ys) = if eqvt x y then eqrt xs ys else false
  eqrt [] [] = true
  eqrt _ _ = false


  diff : ∀ {X : Set} → (X → X → Bool) → List X → List X → List X × List X
  diff eq (x ∷ xs) (y ∷ ys) = if eq x y then diff eq xs ys else (x ∷ xs , y ∷ ys)
  diff eq xs ys = (xs , ys)

  max : ∀ {X : Set} → (X → X → Bool) → List X → List X → Maybe (List X)
  max eq xs ys with diff eq xs ys
  ...             | (rs , []) = just xs
  ...             | ([] , rs) = just ys
  ...             | _ = nothing

  eqls : ∀ {X : Set} → (X → X → Bool) → List X → List X → Bool
  eqls eq xs ys with diff eq xs ys
  ... | ([] , []) = true
  ... | _ = false
  
  module _ where
    open import Data.Maybe

    gtef : ∀ {X : Set} → (X → X → Bool) → List X × List X → List X × List X → Maybe Bool
    gtef eq (xs , ys) (xs' , ys') with (diff eq xs xs' , diff eq ys ys')
    ...  | (rxs , []) , (rys , []) = if eqls eq rxs rys then just true else nothing
    ...  | ([] , rxs') , ([] , rys') = if eqls eq rxs' rys' then just false else nothing
    ...  | _ = nothing

    maxf : ∀ {X : Set} → (X → X → Bool) → List X × List X → List X × List X → Maybe (List X × List X)
    maxf eq w z with gtef eq w z
    ...  | just true = just w
    ...  | just false = just z
    ...  | _ = nothing

    composef : ∀ {X : Set} → (X → X → Bool) → List X × List X → List X × List X → Maybe (List X × List X)
    composef eq (a , b) (c , d) with diff eq b c
    ... | (b' , []) = just (a , d ++ b')
    ... | ([] , c') = just (a ++ c' , [])
    ... | _ = nothing

    tcomp : lfunctype → lfunctype → Maybe lfunctype
    tcomp (a ⇒ b / p) (c ⇒ d / q) = do
      (a' , d') ← composef eqvt (a , b) (c , d)
      q' ← max eqrt p q
      just $ a' ⇒ d' / q'

    tmax : lfunctype → lfunctype → Maybe lfunctype
    tmax (a ⇒ b / p) (a' ⇒ b' / p') = do
      (a'' , b'') ← maxf eqvt (a , b) (a' , b')
      p'' ← max eqrt p p'
      just $ a'' ⇒ b'' / p''

  infix 2 _:-v_
  infix 2 _:-vs_
  infix 2 _:-i_
  infix 2 _:-i'_
  infix 2 _:-is_
  infix 2 _:-f_
  infix 2 _:-f'_
  infix 2 _:-fs_
  infix 2 _:-_

  data _:-v_ : val → valtype → Set where
    tbool : ∀{b} → bool b :-v bool
    tnat : ∀{n} → nat n :-v nat
    tunit : unit tt :-v unit

  data _:-vs_ : vals → resulttype → Set where
    [] : [] :-vs []
    _∷_ : ∀{t ts v vs} → v :-v t → vs :-vs ts → v ∷ vs :-vs t ∷ ts

  mutual
    data _:-i_ : insn → functype → Set where
      tconst : ∀{t v} → v :-v t → const v :-i [] ⇒ t ∷ []
      tnop : nop :-i [] ⇒ []
      tnot : not :-i bool ∷ [] ⇒ bool ∷ []
      tand : and :-i bool ∷ bool ∷ [] ⇒ bool ∷ []
      tadd : add :-i nat ∷ nat ∷ [] ⇒ nat ∷ []
      tsub : sub :-i nat ∷ nat ∷ [] ⇒ nat ∷ []
      teqz : eqz :-i nat ∷ [] ⇒ bool ∷ []
      tdup : ∀{t} → dup :-i t ∷ [] ⇒ t ∷ t ∷ []
      tdrop : ∀{t} → drop :-i t ∷ [] ⇒ []
data insns × ctrli :: insns
    data _:-ci_ : insns → lfunctype
      tblock : ∀{a b p is}
            → is :-is a ⇒ b / b ∷ p
            → block (a ⇒ b) is :-i a ⇒ b / p
      tif-else : ∀{tis fis a b p}
            → tis :-is a ⇒ b / b ∷ p
            → fis :-is a ⇒ b / b ∷ p
            → if-else (a ⇒ b) tis fis :-i bool ∷ a ⇒ b / p
      tloop : ∀{a b p is}
            → is :-is a ⇒ b / a ∷ p
            → loop (a ⇒ b) is :-i a ⇒ b / p
      tbrn : ∀{a b p}
            → (n : ℕ)
            → (f : Fin (length p))
            → n ≡ toℕ f
            → a ≡ lookup p f
            → br n :-i a ⇒ b / p

    data _:-is_ : insns → lfunctype → Set where
      [] : ∀ {a p} → [] :-is a ⇒ a / p
      _∷_ : ∀ {a b c p i is}
            → i :-i' a ⇒ b / p
            → is :-is b ⇒ c / p
            → i ∷ is :-is a ⇒ c / p

    _:-i'_ : insn → lfunctype → Set
    i :-i' t = ∃ {A = lfunctype × resulttype × labelstype} λ (a ⇒ b / p , c , q) → (i :-i a ⇒ b / p) × (t ≡ a ++ c ⇒ b ++ c / p ++ q)

  data _:-f_ : frame → lctxtype → Set where
    tframe : ∀ {a b p c d vs lis n cis}
             → lis :-is a ⇒ b / p
             → vs :-vs c
             → cis :-is b ++ c ⇒ d / p
             → (vs , n , lis , cis) :-f b / a ∷ p ⇒ d / p

  _:-f'_ : frame → lctxtype → Set
  f :-f' t = ∃ {A = lctxtype × labelstype} λ (a / p ⇒ b / q , r) → (f :-f a / p ⇒ b / q) × (t ≡ a / p ++ r ⇒ b / q ++ r)
  
  data _:-fs_ : frames → ctxtype → Set where
    []  : ∀ {a} → [] :-fs a / [] ⇒ a
    _∷_ : ∀ {f fs a b c}
          → f :-f' (a ⇒ b)
          → fs :-fs b ⇒ c
          → f ∷ fs :-fs a ⇒ c

  data _:-_ : state → resulttype → Set where
    tstate : ∀ {a b c vs is fs}
             → fs :-fs b ⇒ c
             → vs :-vs a
             → is :-is a ⇒ b 
             → (fs , vs , is) :- c

  _tv++_ : ∀ {vs vs' ts ts'} → vs :-vs ts → vs' :-vs ts' → vs ++ vs' :-vs ts ++ ts'
  _tv++_ [] pvs' = pvs'
  _tv++_ (p ∷ pvs) pvs' = p ∷ (pvs tv++ pvs')

  _ti++_ : ∀ {is is' a b c p} → (is :-is a ⇒ b / p) → (is' :-is b ⇒ c / p) → is ++ is' :-is a ⇒ c / p
  _ti++_ [] pis' = pis'
  _ti++_ (pi ∷ pis) pis' = pi ∷ (pis ti++ pis')

  {-
  _tf++_ : ∀ {fs fs' a b c} → (fs :-fs a ⇒ b) → (fs' :-fs b ⇒ c) → fs ++ fs' :-fs a ⇒ c
  _tf++_ [] pfs' = pfs'
  _tf++_ (pf ∷ pfs) pfs' = pf ∷ (pfs tf++ pfs')
  -}

  tvtake : ∀ {vs ts} → ( n : Nat.ℕ ) → vs :-vs ts → List.take n vs :-vs List.take n ts
  tvtake Nat.zero _ = []
  tvtake (Nat.suc n) [] = []
  tvtake (Nat.suc n) (p ∷ ps) = p ∷ (tvtake n ps)

  tvdrop : ∀ {vs ts} → ( n : Nat.ℕ ) → vs :-vs ts → List.drop n vs :-vs List.drop n ts
  tvdrop Nat.zero p = p
  tvdrop (Nat.suc n) [] = []
  tvdrop (Nat.suc n) (p ∷ ps) = (tvdrop n ps)

  take-length : ∀{X : Set} → ∀{ys : List X} → (xs : List X) → xs ≡ List.take (List.length xs) (xs ++ ys)
  take-length [] = refl
  take-length (x ∷ xs) = cong (x ∷_) (take-length xs)

  lookup-zero : ∀{X : Set} → ∀{xs : List X} → (x : X) → x ≡ lookup (x ∷ xs) zero
  lookup-zero x = refl

  length-take-lookup-zero : ∀ {X : Set} → (k : List X) → (ks : List (List X)) → {ts : List X} → k ≡ List.take (length k) (lookup (k ∷ ks) zero ++ ts)
  length-take-lookup-zero k ks {ts} = subst (λ x → k ≡ List.take (List.length k) (x ++ ts)) (lookup-zero {_} {ks} k) (take-length k)

  open Interpreter
  safety : ∀{t} → (st : state) → st :- t → ∃ λ st' → (estep st ≡ ok' st') × (st' :- t)
  safety ([] , vs , []) p = ([] , vs , []) , (refl , p)
  safety ((vs , _ , _ , cis) ∷ fs , vs' , []) (tstate {a'} (((a / p ⇒ b / q , r) , (tframe _ pvs pcis) , eq) ∷ pfs) pvs' []) = (fs , vs' ++ vs , cis) , (refl , tstate pfs (pvs' tv++ pvs) ({!!}))
  -- ?0 : cis :-is a₁ ++ c ⇒ b₁
  -- ?1 : 
  -- pcis : cis :-is a ++ c ⇒ b / q
  -- eq : a₁ / p₁ ⇒ b₁ ≡ a / a₂ ∷ q ++ r ⇒ b / q ++ r

  {-
  safety ([] , nat n' ∷ vs , eqz ∷ is) (tstate pfs (tnat tv∷ pvs) ((tiup (tinsn teqz)) ti∷ pis)) = ([] , (bool (feqz n')) ∷ vs , is) , (refl , tstate pfs (tbool tv∷ pvs) pis)
  safety ([] , vs , const v ∷ is) (tstate pfs pvs ((tiup (tinsn (tconst pv))) ti∷ pis)) = ([] , (v ∷ vs) , is) , (refl , tstate pfs (pv tv∷ pvs) pis)
  safety ([] , vs , nop ∷ is) (tstate pfs pvs (tiup (tinsn tnop) ti∷ pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
  safety ([] , bool b ∷ vs , not ∷ is) (tstate pfs (tbool tv∷ pvs) (tiup (tinsn tnot) ti∷ pis)) = ([] , (bool (Bool.not b)) ∷ vs , is) , (refl , tstate pfs (tbool tv∷ pvs) pis)
  safety ([] , bool b ∷ bool b' ∷ vs , and ∷ is) (tstate pfs (tbool tv∷ (tbool tv∷ pvs)) ((tiup (tinsn tand)) ti∷ pis)) = ([] , (bool (b Bool.∧ b')) ∷ vs , is) , (refl , tstate pfs (tbool tv∷ pvs) pis)
  safety ([] , v ∷ vs , drop ∷ is) (tstate pfs (pv tv∷ pvs) (tiup (tinsn tdrop) ti∷ pis)) = ([] , vs , is) , (refl , tstate pfs pvs pis)
  safety ([] , nat n ∷ nat m ∷ vs , sub ∷ is) (tstate pfs (tnat tv∷ (tnat tv∷ pvs)) (tiup (tinsn tsub) ti∷ pis)) = ([] , (nat (n Nat.∸ m) ∷ vs , is)) , (refl , tstate pfs (tnat tv∷ pvs) pis)
  safety ([] , v ∷ vs , dup ∷ is) (tstate pfs (_tv∷_ {t1} pv pvs) ((tiup {b} {ks} (tinsn (tdup {t})) {pp}) ti∷ pis)) = ([] , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv tv∷ (pv tv∷ pvs)) pis)
  safety ((vs' , n , lcont , cont) ∷ [] , vs , br l ∷ is) (tstate ((pvs' , plcont , pcont) tf∷ pfs) pvs (pi ti∷ pis)) =
    ([] , List.take n vs ++ vs' , lcont ++ cont) , (refl , tstate pfs ( (tvtake n pvs) tv++ pvs') (plcont ti++ pcont))

-}
