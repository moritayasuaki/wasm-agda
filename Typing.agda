open import Wasm
open import Monad

import Category.Monad.Indexed
import Category.Monad
import Category.Applicative.Indexed
import Data.List as List
import Data.Vec as Vec
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
open import Data.Fin.Properties

infix 4.9 _/_ 
record slash (X : Set) (Y : Set): Set where
  constructor _/_
  field
    left : X
    right : Y

module _ where
  open List
  open Nat
  open import Data.List.Properties
  open import Relation.Binary.PropositionalEquality
  lemma : ∀ {X : Set} → (ab a b c : List X) → (ab ≡ a ++ b) → a ++ b ++ c ≡ (ab ++ c)
  lemma .(a ++ b) a b c refl = sym (++-assoc a b c)

  lemma3' : ∀ {X : Set} → (b c : List X) → b ≡ take (length b) (b ++ c)
  lemma3' [] ys = refl
  lemma3' (x ∷ xs) ys = cong (x ∷_ ) (lemma3' xs ys)

  lemma3 : ∀ {X : Set} → (a b c : List X) → a ≡ b ++ c → b ≡ take (length b) a
  lemma3 .(b ++ c) b c refl = lemma3' b c

  lemma4' : ∀ {X : Set} → (b c : List X) → c ≡ drop (length b) (b ++ c)
  lemma4' [] ys = refl
  lemma4' (x ∷ xs) ys = lemma4' xs ys

  lemma4 : ∀ {X : Set} → (a b c : List X) → a ≡ b ++ c → c ≡ drop (length b) a
  lemma4 .(b ++ c) b c refl = lemma4' b c

  lemma5' : ∀ {X : Set} → (n : ℕ) → List.drop n [] ≡ []
  lemma5' zero = refl
  lemma5' (suc n) = refl

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
  open Function using (_$_ ; id ; _∘_ ; _|>_)
  open arrow
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.Structures
  open import Relation.Nullary
  open import Data.List.Properties

  labelstype = List resulttype

  lresulttype  = slash resulttype labelstype
  lfunctype = arrow resulttype lresulttype
  lctxtype = arrow lresulttype lresulttype
  ctxtype = arrow lresulttype resulttype

 
  infix 2 _:-v_
  infix 2 _:-vs_
  infix 2 _:-i_
  infix 2 _:-i'_
  infix 2 _:-is_
  infix 2 _:-f_
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
    data _:-i_ : insn → lfunctype → Set where
      tconst : ∀{t v p} → v :-v t → const v :-i [] ⇒ t ∷ [] / p
      tnop : ∀{p} → nop :-i [] ⇒ [] / p
      tnot : ∀{p} → not :-i bool ∷ [] ⇒ bool ∷ [] / p
      tand : ∀{p} → and :-i bool ∷ bool ∷ [] ⇒ bool ∷ [] / p
      tadd : ∀{p} → add :-i nat ∷ nat ∷ [] ⇒ nat ∷ [] / p
      tsub : ∀{p} → sub :-i nat ∷ nat ∷ [] ⇒ nat ∷ [] / p
      teqz : ∀{p} → eqz :-i nat ∷ [] ⇒ bool ∷ [] / p
      tdup : ∀{p t} → dup :-i t ∷ [] ⇒ t ∷ t ∷ [] / p
      tdrop : ∀{p t} → drop :-i t ∷ [] ⇒ [] / p
      tblock : ∀{a b p is}
            → is :-is a ⇒ b / b ∷ p
            → block (a ⇒ b) is :-i a ⇒ b / p
      tif-else : ∀{a b p tis fis}
            → tis :-is a ⇒ b / b ∷ p
            → fis :-is a ⇒ b / b ∷ p
            → if-else (a ⇒ b) tis fis :-i bool ∷ a ⇒ b / p
      tloop : ∀{a b p is}
            → is :-is a ⇒ b / a ∷ p
            → loop (a ⇒ b) is :-i a ⇒ b / p
      tbrn : ∀{a b p q r}
            → (n : ℕ)
            → p ≡ q ++ (a ∷ r)
            → n ≡ length q
            → br n :-i a ⇒ b / p

    data _:-is_ : insns → lfunctype → Set where
      [] : ∀ {a p} → [] :-is a ⇒ a / p
      _∷_ : ∀ {a b c p i is}
            → i :-i' a ⇒ b / p
            → is :-is b ⇒ c / p
            → i ∷ is :-is a ⇒ c / p

    _:-i'_ : insn → lfunctype → Set
    i :-i' t = ∃ {A = lfunctype × resulttype} λ (a ⇒ b / p , c) → (i :-i a ⇒ b / p) × (t ≡ a ++ c ⇒ b ++ c / p)

  weaken:-i : ∀{a b p i} → (c : resulttype) → (i :-i a ⇒ b / p) → i :-i' a ++ c ⇒ b ++ c / p
  weaken:-i {a} {b} {p} {i} c pi = (a ⇒ b / p , c) , (pi , refl)

  weaken':-i : ∀{a b p i} → (i :-i a ⇒ b / p) → i :-i' a ⇒ b / p
  weaken':-i {a} {b} {p} {i} pi = pi'
    where pi' = subst (λ x → i :-i' x ⇒ b / p) (++-identityʳ a) (subst (λ x → i :-i' a ++ [] ⇒ x / p) (++-identityʳ b) (weaken:-i [] pi))


  data _:-f_ : frame → lctxtype → Set where
    tframe : ∀ {a b n p c d vs lis cis}
             → lis :-is a ⇒ b / p
             → vs :-vs c
             → cis :-is b ++ c ⇒ d / p
             → (n ≡ length a)
             → (vs , n , lis , cis) :-f b / a ∷ p ⇒ d / p

  data _:-fs_ : frames → ctxtype → Set where
    []  : ∀ {a} → [] :-fs a / [] ⇒ a
    _∷_ : ∀ {f fs a b c}
          → f :-f (a ⇒ b)
          → fs :-fs b ⇒ c
          → f ∷ fs :-fs a ⇒ c

{-
  tflookup-drop : ∀{a c n p fs} → (pfs : fs :-fs a / p ⇒ c) → (fn : Fin (length p)) → ∃ λ vs → ∃ λ n → ∃ λ lis → ∃ λ cis → ∃ λ b → ∃ λ d → ((vs , n , lis , cis) :-f b / List.drop (toℕ fn) p ⇒ d / List.drop (Nat.suc (toℕ fn)) p) × (List.drop (Nat.suc (toℕ fn)) fs :-fs d / List.drop (Nat.suc (toℕ fn)) p ⇒ c) × ((vs , n , lis , cis) ≡ lookup' fs pfs fn)
  tflookup-drop {p = a ∷ p} (_∷_ {fs = fs} (tframe {b = b} {d = d} {vs} {.(List.length a)} {lis} {cis} plis pvs pcis refl) pfs) zero = vs , (List.length a) , lis , cis , b , d , tframe plis pvs pcis refl , pfs , refl
  tflookup-drop {p = a ∷ p} (tframe _ _ _ refl ∷ pfs) (suc fn) = tflookup-drop pfs fn
-}

  tftail : ∀{a b c p f fs} → ((f ∷ fs) :-fs a / (b ∷ p) ⇒ c) → ∃ λ a' → (fs :-fs a' / p ⇒ c)
  tftail (tframe {d = d} plis pvs pcis refl ∷ pfs) = (d , pfs)

  tfdrop2 : ∀{a c fs p q r b} → (fs :-fs a / p ⇒ c) → (p ≡ q ++ (b ∷ r)) → ∃ λ a' → ∃ λ fs' → (fs' :-fs a' / b ∷ r ⇒ c) × (List.drop (length q) fs ≡ fs')
  tfdrop2 {a = a} {fs = fs} {q = []} (pf ∷ pfs) refl = (a , fs , pf ∷ pfs , refl)
  tfdrop2 {q = p ∷ ps} (pf ∷ pfs) refl with tftail (pf ∷ pfs)
  ... | _ , pfs' = tfdrop2 pfs' refl

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

  eq-lfunctype : ∀{a a' b b' : resulttype} → ∀{p p' : labelstype} → a ⇒ b / p ≡ a' ⇒ b' / p' → a ≡ a' × b ≡ b' × p ≡ p' 
  eq-lfunctype refl = refl , refl , refl

  eq-lctxtype : ∀{a a' b b' : resulttype} → ∀{p p' q q' : labelstype} → a / p ⇒ b / q ≡ a' / p' ⇒ b' / q' → a ≡ a' × p ≡ p' × b ≡ b' × q ≡ q'
  eq-lctxtype refl = refl , refl , refl , refl

  weaken:-is : ∀{is a b p} → (c : resulttype) → is :-is a ⇒ b / p → is :-is a ++ c ⇒ b ++ c / p
  weaken:-is c [] = []
  weaken:-is {i ∷ is} {a} {b} {p} c (_∷_ {b = d} pi' pis) with pi'
  ... | (a' ⇒ d' / p' , c') , (pi , eq) =
    let (a≡a'++c' , d≡d'++c' , p≡p') = eq-lfunctype eq in
    let pi-w = weaken:-i (c' ++ c) pi |>
               subst (λ x → i :-i' x ⇒ d' ++ c' ++ c / p') (lemma a a' c' c a≡a'++c') |>
               subst (λ x → i :-i' a ++ c ⇒ x / p') (lemma d d' c' c d≡d'++c') |>
               subst (λ x → i :-i' a ++ c ⇒ d ++ c / x) (sym p≡p') in
    let pis-w = weaken:-is c pis in pi-w ∷ pis-w

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
  safety ((vs , _ , _ , cis) ∷ fs , vs' , []) (tstate ((tframe _ pvs pcis _) ∷ pfs) pvs' []) =
    (fs , vs' ++ vs , cis) , (refl , tstate pfs (pvs' tv++ pvs) pcis)
  safety (fs' , vs , const x ∷ is) (tstate {_} {_ / _} pfs pvs (((.[] ⇒ _ ∷ .[] / _ , _) , tconst {_} pv , refl) ∷ pis)) with fs'
  ... | [] = ([] , x ∷ vs , is) , (refl , tstate pfs (pv ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , x ∷ vs , is) , (refl , tstate pfs (pv ∷ pvs) pis)

  safety (fs' , vs , nop ∷ is) (tstate {_} {_ / _} pfs pvs (((.[] ⇒ .[] / _ , _) , tnop , refl) ∷ pis)) with fs'
  ... | [] = ([] , vs , is) , (refl , tstate pfs pvs pis)
  ... | f ∷ fs = (f ∷ fs , vs , is) , (refl , tstate pfs pvs pis)

  safety (fs' , bool v ∷ vs , not ∷ is) (tstate pfs (tbool ∷ pvs) ((_ , tnot , refl) ∷ pis)) with fs'
  ... | [] = ([] , bool (Bool.not v) ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , bool (Bool.not v) ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)

  safety (fs' , bool v ∷ bool v' ∷ vs , and ∷ is) (tstate pfs (tbool ∷ tbool ∷ pvs) ((_ , tand , refl) ∷ pis)) with fs'
  ... | [] = ([] , bool (v Bool.∧ v') ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , bool (v Bool.∧ v') ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)

  safety (fs' , nat n ∷ nat m ∷ vs , add ∷ is) (tstate pfs (tnat ∷ (tnat ∷ pvs)) ((_ , tadd , refl) ∷ pis)) with fs'
  ... | [] = ([] , nat (n Nat.+ m) ∷ vs , is) , (refl , tstate pfs (tnat ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , nat (n Nat.+ m) ∷ vs , is) , (refl , tstate pfs (tnat ∷ pvs) pis)

  safety (fs' , nat n ∷ nat m ∷ vs , sub ∷ is) (tstate pfs (tnat ∷ (tnat ∷ pvs)) ((_ , tsub , refl) ∷ pis)) with fs'
  ... | [] = ([] , nat (n Nat.∸ m) ∷ vs , is) , (refl , tstate pfs (tnat ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , nat (n Nat.∸ m) ∷ vs , is) , (refl , tstate pfs (tnat ∷ pvs) pis)

  safety (fs' , nat n ∷ vs , eqz ∷ is) (tstate pfs (tnat ∷ pvs) ((_ , teqz , refl) ∷ pis)) with fs'
  ... | [] = ([] , bool (feqz n) ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , bool (feqz n) ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)

  safety (fs' , v ∷ vs , dup ∷ is) (tstate {_} {_ / _} pfs (pv ∷ pvs) (((_ ∷ .[] ⇒ .(_ ∷ _ ∷ []) / _ , _) , tdup , refl) ∷ pis)) with fs'
  ... | [] = ([] , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv ∷ pv ∷ pvs) pis)
  ... | f ∷ fs = (f ∷ fs , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv ∷ pv ∷ pvs) pis)

  safety (fs' , (._ ∷ vs) , drop ∷ is) (tstate pfs (x ∷ pvs) (((t ∷ .[] ⇒ .[] / p , c) , tdrop , refl) ∷ pis)) with fs'
  ... | [] = ([] , vs , is) , (refl , tstate pfs pvs pis)
  ... | f ∷ fs = (f ∷ fs , vs , is) , (refl , tstate pfs pvs pis)

  safety (fs' , vs , block (a ⇒ b) is ∷ cis) (tstate pfs pvs (_∷_ {c = d} (((.a ⇒ .b / p) , c) , tblock pis , refl) pcis)) with fs'
  ... | [] = ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (lemma4' a c) pcis
          pis' = subst (λ x → is :-is x ⇒ b / b ∷ p) (lemma3' a c) pis
  ... | f ∷ fs = ((List.drop (length a) vs , length b , [] , cis) ∷ f ∷ fs , List.take (length a) vs , is) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (lemma4' a c) pcis
          pis' = subst (λ x → is :-is x ⇒ b / b ∷ p) (lemma3' a c) pis

  safety (fs' , bool bb ∷ vs , if-else (a ⇒ b) is-t is-f ∷ cis) (tstate pfs (tbool ∷ pvs) (_∷_ {c = d} (((.(bool ∷ a) ⇒ .b / p) , c) , tif-else pis-t pis-f , refl) pcis)) with fs' | bb
  ... | [] | true = ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is-t) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis-t')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (lemma4' a c) pcis
          pis-t' = subst (λ x → is-t :-is x ⇒ b / b ∷ p) (lemma3' a c) pis-t
  ... | [] | false = ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is-f) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis-f')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (lemma4' a c) pcis
          pis-f' = subst (λ x → is-f :-is x ⇒ b / b ∷ p) (lemma3' a c) pis-f
  ... | f ∷ fs | true = ((List.drop (length a) vs , length b , [] , cis) ∷ f ∷ fs , List.take (length a) vs , is-t) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis-t')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (lemma4' a c) pcis
          pis-t' = subst (λ x → is-t :-is x ⇒ b / b ∷ p) (lemma3' a c) pis-t
  ... | f ∷ fs | false = ((List.drop (length a) vs , length b , [] , cis) ∷ f ∷ fs , List.take (length a) vs , is-f) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis-f')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (lemma4' a c) pcis
          pis-f' = subst (λ x → is-f :-is x ⇒ b / b ∷ p) (lemma3' a c) pis-f

  safety (fs' , vs , loop (a ⇒ b) is ∷ cis) (tstate pfs pvs (_∷_ {c = d} (((.a ⇒ .b / p) , c) , tloop pis , refl) pcis)) with fs'
  ... | [] = ((List.drop (length a) vs , length a , loop (a ⇒ b) is ∷ [] , cis) ∷ [] , List.take (length a) vs , is) ,
             (refl , tstate ((tframe (weaken:-i [] (tloop pis) ∷ []) (tvdrop (length a) pvs) pcis' len-a) ∷ pfs) (tvtake (length a) pvs) pis')
             where pcis' = subst (λ x → cis :-is (b ++ []) ++ x ⇒ d / p) (lemma4' a c) ∘ subst (λ x → cis :-is x ++ c ⇒ d / p ) (sym (++-identityʳ b)) $ pcis
                   len-a = sym (cong List.length (++-identityʳ a))
                   pis' = subst (λ x → is :-is x ⇒ b ++ [] / (a ++ []) ∷ p) (lemma3' a c) (subst (λ x → is :-is a ⇒ x / (a ++ []) ∷ p) (sym (++-identityʳ b)) (subst (λ x → is :-is a ⇒ b / x ∷ p) (sym (++-identityʳ a)) pis))
  ... | f ∷ fs = ((List.drop (length a) vs , length a , loop (a ⇒ b) is ∷ [] , cis) ∷ f ∷ fs , List.take (length a) vs , is) ,
                 (refl , tstate ((tframe (weaken:-i [] (tloop pis) ∷ []) (tvdrop (length a) pvs) pcis' len-a) ∷ pfs) (tvtake (length a) pvs) pis')
             where pcis' = subst (λ x → cis :-is (b ++ []) ++ x ⇒ d / p) (lemma4' a c) ∘ subst (λ x → cis :-is x ++ c ⇒ d / p ) (sym (++-identityʳ b)) $ pcis
                   len-a = sym (cong List.length (++-identityʳ a))
                   pis' = subst (λ x → is :-is x ⇒ b ++ [] / (a ++ []) ∷ p) (lemma3' a c) (subst (λ x → is :-is a ⇒ x / (a ++ []) ∷ p) (sym (++-identityʳ b)) (subst (λ x → is :-is a ⇒ b / x ∷ p) (sym (++-identityʳ a)) pis))


  safety (((vs' , .(length a) , lis , cis) ∷ fs') , vs , br .0 ∷ _) (tstate {b = b' / a'' ∷ p'} {c = c'} (tframe {c = c''} plis pvs' pcis refl ∷ pfs) pvs (((a ⇒ b / .(a ∷ _) , c) , tbrn {q = []} .0 refl refl , refl) ∷ _)) =
    let plis' =  weaken:-is c'' ((subst λ x → lis :-is x ⇒ b' / p') (lemma3' a'' c) plis) in
      (fs' , List.take (length a) vs ++ vs' , lis ++ cis) , (refl , tstate pfs (tvtake (length a) pvs tv++ pvs') (plis' ti++ pcis))
  safety (fs , vs , br .(Nat.suc (length q)) ∷ _) (tstate pfs pvs (((a ⇒ b / .(x ∷ q ++ a ∷ _) , c) , tbrn {q = x ∷ q} .(Nat.suc (length q)) refl refl , refl) ∷ _)) with tfdrop2 pfs refl
  ... | a' , .(List.drop (length {!!}) fs) , pfs'' , refl = {!!} , {!!}

{-
  safety (fs , vs , br n ∷ _) (tstate pfs pvs (((a ⇒ b / p , c) , tbrn , e3) ∷ _)) with tfdrop n pfs
  safety (fs , vs , br .(toℕ fn) ∷ _) (tstate pfs pvs (((.(lookup p fn) ⇒ b / p , c) , tbrn .(toℕ fn) fn refl refl , refl) ∷ _)) | d , pf ∷ pfs' =
    (List.drop (Nat.suc (toℕ fn)) fs , ? , {!!}) , ({!!} , {!!})
-}
  {-
  ... | d , (_∷_ {b = d / p} (tframe plis'' pvs'' pcis'' refl) pfs'') = ?
    where plis' = weaken:-is c' ((subst λ x → lis :-is x ⇒ b' / p) (lemma3' a c) plis)
          plis'++pcis = subst (λ x → lis ++ cis :-is x ++ c' ⇒ d' / p) (sym (lemma3' a c)) (plis' ti++ pcis)
          pbrn = (((lookup p fm ⇒ a / p , c') , tbrn (toℕ fm) fm refl refl , {!!}) ∷ pcis)
          -- pbrn'' = (weaken:-i c (tbrn (toℕ fm) fm refl refl)) ∷ plis'++pcis
          pp = safety (fs' , List.take (length (lookup p fm)) vs , br (toℕ fm) ∷ cis) (tstate pfs' (tvtake (List.length (lookup p fm)) pvs) pbrn)
  -}
--     where  ff = safety (fs' , vs , br (toℕ fm) ∷ cis) (tstate pfs' pvs (((lookup p fm ⇒ d' / p , c) , tbrn (toℕ fm) fm refl refl , refl) ∷ {!!}))
--            gg = safety ((vs' , List.length a , lis , cis) ∷ fs' , {!!} , is) (tstate (tframe plis pvs' pcis refl ∷ pfs') {!!} pis)
--           ff' = tfdrop (toℕ fm) pfs'
{-
    let (vs' , m , lis , cis) = lookup' fs p pfs f in
    let fs' = List.drop (Nat.suc (toℕ f)) fs in
    (fs' , List.take m vs ++ vs' , lis ++ cis) , (refl , ?)
-}
{-
  safety ((vs' , .(List.foldr (λ _ → Nat.suc) 0 a'') , lis , cis) ∷ fs , vs , br 0 ∷ is) (tstate {a = a'} {b = b' / a'' ∷ p'} {c'} (tframe {c = c''} {d} plis pvs' pcis refl ∷ pfs) pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = .(a'' ∷ p')} ((dom₁ ⇒ .(_ / _) , snd₁) , tbrn .0 f x x₁ , snd) pis)) = {!!}
  -}
  {-
    let plis' = subst (λ x → lis :-is x ⇒ b' / p') (lemma3' a'' c) plis in
    (fs , List.take m vs ++ vs' , lis ++ cis) , (refl , tstate pfs (tvtake m pvs tv++ pvs') ((weaken:-is c'' plis') ti++ pcis))
  safety ((vs' , m , lis , cis) ∷ fs , vs , br (Nat.suc n) ∷ is) (tstate tfs tvs (((.(lookup (l ∷ p) f) ⇒ b / l ∷ p , snd) , tbrn .(toℕ f) f refl refl , qq) ∷ tis)) = ?
-}
    -- safety (fs , vs , br (toℕ fn) ∷ cis) (tstate pfs pvs ?)
    {-
    let (vs'' , m' , lis' , cis') = lookup' fs p' pfs fn in
    let fs' = List.drop (toℕ fn) fs in
    let p'' = List.drop (toℕ fn) p' in
    (fs' , List.take m' vs ++ vs'' , lis' ++ cis') , (refl , ?)
    -}
{-
  safety ((vs' , m , lis , cis) ∷ fs , vs , br 0 ∷ is) (tstate {a = a'} {b = b' / a'' ∷ p'} {c'} ((tframe {c = c''} plis pvs' pcis refl) ∷ pfs) pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = a'' ∷ p'} pi' pis)) with pi'
  ... | (.a'' ⇒ b / .(a'' ∷ p') , c) , tbrn .0 zero refl refl , refl =
    let plis' = subst (λ x → lis :-is x ⇒ b' / p') (lemma3' a'' c) plis in
    (fs , List.take m vs ++ vs' , lis ++ cis) , (refl , tstate pfs (tvtake m pvs tv++ pvs') ((weaken:-is c'' plis') ti++ pcis))
  safety ((vs' , m , lis , cis) ∷ fs , vs , br (Nat.suc n) ∷ is) (tstate {a = a'} {b = b' / a'' ∷ p'} {c'} ((tframe {c = c''} {d} plis pvs' pcis refl) ∷ pfs) pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = a'' ∷ p'} pi' pis)) with pi'
  ... | (.(lookup p' f) ⇒ b / .(a'' ∷ p') , c) , tbrn .(Nat.suc (toℕ f)) (suc f) refl refl , refl =
    let aa : br (toℕ f) :-i' lookup p' f ++ [] ⇒ d ++ [] / p'
        aa = weaken:-i [] (tbrn (toℕ f) f refl refl) in
    let aa' = subst (λ x → br (toℕ f) :-i' x ⇒ d ++ [] / p') (++-identityʳ (lookup p' f)) aa in
    let aa'' = subst (λ x → br (toℕ f) :-i' lookup p' f ⇒ x / p') (++-identityʳ d) aa' in
    let s = safety (fs , vs , br n ∷ []) (tstate pfs pvs {!!}) in {!!}
-}

{-
    -}
{-    let (g , h , q ) = eq-lfunctype eq in
    let t = cong (λ x → lis :-is List.take x a' ⇒ b' / p') meq in
    let leneq : length p ≡ (Nat.suc (length p'))
        leneq = cong length (sym q) in
    let fn-zero = toℕ-injective {i = fn} {j = ?} refl in
    let s' = subst (λ x → a ≡ lookup x fn) (sym q) p2 in
    (fs , List.take m vs ++ vs' , lis ++ cis) ,
    (refl , tstate pfs (tvtake m pvs tv++ pvs') {!!}) -- ((weaken:-is c'' plis) ti++ pcis))
-}
