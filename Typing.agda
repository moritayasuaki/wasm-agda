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

  take-length : ∀ {X : Set} → (b c : List X) → b ≡ take (length b) (b ++ c)
  take-length [] ys = refl
  take-length (x ∷ xs) ys = cong (x ∷_ ) (take-length xs ys)

  drop-length : ∀ {X : Set} → (b c : List X) → c ≡ drop (length b) (b ++ c)
  drop-length [] ys = refl
  drop-length (x ∷ xs) ys = drop-length xs ys

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
      tbrifn : ∀{a p q r}
             → (n : ℕ)
             → p ≡ q ++ (a ∷ r)
             → n ≡ length q
             → br-if n :-i bool ∷ a ⇒ a / p

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

  to:-i' : ∀{a b p i} → (i :-i a ⇒ b / p) → i :-i' a ⇒ b / p
  to:-i' {a} {b} {p} {i} pi = pi'
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

  tfheadtail : ∀{a b c p ffs} → (ffs :-fs a / (b ∷ p) ⇒ c) → ∃ λ f → ∃ λ fs' → ∃ λ a' → (f :-f a / b ∷ p ⇒ a' / p) × (fs' :-fs a' / p ⇒ c) × (ffs ≡ f ∷ fs')
  tfheadtail  (_∷_ {f@.(_ , length a , _ , _)} {fs'} {b = b / _} (pf@(tframe {a} _ _ _ refl)) pfs) = (f , fs' , b , pf , pfs , refl)

  tfdrop : ∀{a c fs q r b} → (fs :-fs a / q ++ (b ∷ r) ⇒ c) → ∃ λ a' → (List.drop (length q) fs :-fs a' / b ∷ r ⇒ c)
  tfdrop {a = a} {fs = fs} {q = []} (pf ∷ pfs) = (a , pf ∷ pfs)
  tfdrop {q = p ∷ ps} (pf ∷ pfs) with tfheadtail (pf ∷ pfs)
  ... | _ , _ , _ , _ , pfs' , refl = tfdrop pfs'

  tbr-helper : ∀{a b c d q r fs vs is} → (fs :-fs a / q ++ (b ∷ r) ⇒ c) → (vs :-vs b ++ d) → ∃ λ a' → ∃ λ fs' → ∃ λ vs' → ∃ λ lis' → ∃ λ cis' → Interpreter.br-helper (length q) (fs , vs , is) ≡ Interpreter.ok' (fs' , List.take (length b) vs ++ vs' , lis' ++ cis') × ((vs' , length b , lis' , cis') ∷ fs' :-fs a' / (b ∷ r) ⇒ c)
  tbr-helper {b = b} {q = q} {fs = fs} {vs = vs} pfs pvs with List.drop (length q) fs | inspect (List.drop (length q)) fs
  ... | ffs' | [ dropq-fs≡ffs' ] with tfdrop pfs 
  ...                               |  (a' , pffs') with tfheadtail pffs'
  ...                                                  | (f , fs' , b' , pf' , pfs' , dropq-fs≡f'∷fs') with trans (sym dropq-fs≡ffs') dropq-fs≡f'∷fs'
  tbr-helper {b = b} {q = q} {fs = fs} {vs = vs} pfs pvs | .((vs' , length a , lis' , cis') ∷ fs') | [ dropq-fs≡ffs' ] | a' , pffs' | (vs' , .(length a) , lis' , cis') , fs' , b' , tframe {a} plis' pvs' pcis' refl , pfs' , dropq-fs≡f'∷fs' | refl = (a' , fs' , vs' , lis' , cis' , refl , tframe plis' pvs' pcis' refl ∷ pfs')

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

  weaken:-is : ∀{is a b p} → (c : resulttype) → is :-is a ⇒ b / p → is :-is a ++ c ⇒ b ++ c / p
  weaken:-is c [] = []
  weaken:-is {i ∷ is} {a} {b} {p} c (_∷_ {b = d} ((a' ⇒ d' / p' , c') , pi , refl) pis) = s (weaken:-i (c' ++ c) pi) ∷ weaken:-is c pis
    where s = subst (λ t → i :-i' t) (sym (cong₂ (λ x y → x ⇒ y / p') (++-assoc a' c' c) (++-assoc d' c' c)))

  tvtake : ∀ {vs ts} → ( n : Nat.ℕ ) → vs :-vs ts → List.take n vs :-vs List.take n ts
  tvtake Nat.zero _ = []
  tvtake (Nat.suc n) [] = []
  tvtake (Nat.suc n) (p ∷ ps) = p ∷ (tvtake n ps)

  tvdrop : ∀ {vs ts} → ( n : Nat.ℕ ) → vs :-vs ts → List.drop n vs :-vs List.drop n ts 
  tvdrop Nat.zero p = p
  tvdrop (Nat.suc n) [] = []
  tvdrop (Nat.suc n) (p ∷ ps) = (tvdrop n ps)

  open Interpreter

  safety : ∀{t} → (st : state) → st :- t → ∃ λ st' → (estep st ≡ ok' st') × (st' :- t)
  safety ([] , vs , []) p = ([] , vs , []) , (refl , p)
  safety ((vs , _ , _ , cis) ∷ fs , vs' , []) (tstate ((tframe _ pvs pcis _) ∷ pfs) pvs' []) =
    (fs , vs' ++ vs , cis) , (refl , tstate pfs (pvs' tv++ pvs) pcis)

  safety (fs' , vs , const x ∷ is) (tstate {_} {_ / _} pfs pvs (((.[] ⇒ _ ∷ .[] / _ , _) , tconst {_} pv , refl) ∷ pis)) = (fs' , x ∷ vs , is) , (refl , tstate pfs (pv ∷ pvs) pis)

  safety (fs' , vs , nop ∷ is) (tstate {_} {_ / _} pfs pvs (((.[] ⇒ .[] / _ , _) , tnop , refl) ∷ pis)) = (fs' , vs , is) , (refl , tstate pfs pvs pis)

  safety (fs' , bool v ∷ vs , not ∷ is) (tstate pfs (tbool ∷ pvs) ((_ , tnot , refl) ∷ pis)) = (fs' , bool (Bool.not v) ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)

  safety (fs' , bool v ∷ bool v' ∷ vs , and ∷ is) (tstate pfs (tbool ∷ tbool ∷ pvs) ((_ , tand , refl) ∷ pis)) = (fs' , bool (v Bool.∧ v') ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)

  safety (fs' , nat n ∷ nat m ∷ vs , add ∷ is) (tstate pfs (tnat ∷ (tnat ∷ pvs)) ((_ , tadd , refl) ∷ pis)) = (fs' , nat (n Nat.+ m) ∷ vs , is) , (refl , tstate pfs (tnat ∷ pvs) pis)

  safety (fs' , nat n ∷ nat m ∷ vs , sub ∷ is) (tstate pfs (tnat ∷ (tnat ∷ pvs)) ((_ , tsub , refl) ∷ pis)) = (fs' , nat (n Nat.∸ m) ∷ vs , is) , (refl , tstate pfs (tnat ∷ pvs) pis)

  safety (fs' , nat n ∷ vs , eqz ∷ is) (tstate pfs (tnat ∷ pvs) ((_ , teqz , refl) ∷ pis)) = (fs' , bool (feqz n) ∷ vs , is) , (refl , tstate pfs (tbool ∷ pvs) pis)

  safety (fs' , v ∷ vs , dup ∷ is) (tstate {_} {_ / _} pfs (pv ∷ pvs) (((_ ∷ .[] ⇒ .(_ ∷ _ ∷ []) / _ , _) , tdup , refl) ∷ pis)) = (fs' , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv ∷ pv ∷ pvs) pis)

  safety (fs' , (._ ∷ vs) , drop ∷ is) (tstate pfs (x ∷ pvs) (((t ∷ .[] ⇒ .[] / p , c) , tdrop , refl) ∷ pis)) = (fs' , vs , is) , (refl , tstate pfs pvs pis)

  safety (fs' , vs , block (a ⇒ b) is ∷ cis) (tstate pfs pvs (_∷_ {c = d} (((.a ⇒ .b / p) , c) , tblock pis , refl) pcis)) = ((List.drop (length a) vs , length b , [] , cis) ∷ fs' , List.take (length a) vs , is) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (drop-length a c) pcis
          pis' = subst (λ x → is :-is x ⇒ b / b ∷ p) (take-length a c) pis

  safety (fs' , bool bb ∷ vs , if-else (a ⇒ b) is-t is-f ∷ cis) (tstate pfs (tbool ∷ pvs) (_∷_ {c = d} (((.(bool ∷ a) ⇒ .b / p) , c) , tif-else pis-t pis-f , refl) pcis)) with bb
  ... | true = ((List.drop (length a) vs , length b , [] , cis) ∷ fs' , List.take (length a) vs , is-t) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis-t')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (drop-length a c) pcis
          pis-t' = subst (λ x → is-t :-is x ⇒ b / b ∷ p) (take-length a c) pis-t
  ... | false = ((List.drop (length a) vs , length b , [] , cis) ∷ fs' , List.take (length a) vs , is-f) , (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis' refl) ∷ pfs) (tvtake (length a) pvs) pis-f')
    where pcis' = subst (λ x → cis :-is b ++ x ⇒ d / p) (drop-length a c) pcis
          pis-f' = subst (λ x → is-f :-is x ⇒ b / b ∷ p) (take-length a c) pis-f

  safety (fs' , vs , loop (a ⇒ b) is ∷ cis) (tstate pfs pvs (_∷_ {c = d} (((.a ⇒ .b / p) , c) , tloop pis , refl) pcis)) = ((List.drop (length a) vs , length a , loop (a ⇒ b) is ∷ [] , cis) ∷ fs' , List.take (length a) vs , is) ,
             (refl , tstate ((tframe (weaken:-i [] (tloop pis) ∷ []) (tvdrop (length a) pvs) pcis' len-a) ∷ pfs) (tvtake (length a) pvs) pis')
             where pcis' = subst (λ x → cis :-is (b ++ []) ++ x ⇒ d / p) (drop-length a c) ∘ subst (λ x → cis :-is x ++ c ⇒ d / p ) (sym (++-identityʳ b)) $ pcis
                   len-a = sym (cong List.length (++-identityʳ a))
                   pis' = subst (λ x → is :-is x ⇒ b ++ [] / (a ++ []) ∷ p) (take-length a c) (subst (λ x → is :-is a ⇒ x / (a ++ []) ∷ p) (sym (++-identityʳ b)) (subst (λ x → is :-is a ⇒ b / x ∷ p) (sym (++-identityʳ a)) pis))

  safety (fs , vs , br .(length q) ∷ is) (tstate pfs pvs (((.(_ ⇒ _ / q ++ a ∷ _) , e) , tbrn {a = a} {q = q} {r = r} .(length q) refl refl , refl) ∷ pis)) with tbr-helper {is = is} pfs pvs
  ... | a' , fs' , vs' , lis' , cis' , pbr , (tframe {c = c} plis' pvs' pcis' refl ∷ pfs') = (fs' , List.take (length a) vs ++ vs' , lis' ++ cis') , (pbr , tstate pfs' (tvtake (length a) pvs tv++ pvs') (plis'' ti++ pcis')) 
    where plis'' = weaken:-is c ( subst (λ x → lis' :-is x ⇒ a' / r) (take-length a e) plis')

  safety (fs , bool true ∷ vs , br-if .(length q) ∷ is) (tstate pfs (tbool ∷ pvs) (((.(_ ⇒ _ / q ++ a ∷ _) , e) , tbrifn {a = a} {q = q} {r = r} .(length q) refl refl , refl) ∷ pis)) with tbr-helper {is = is} pfs pvs
  ... | a' , fs' , vs' , lis' , cis' , pbr , (tframe {c = c} plis' pvs' pcis' refl ∷ pfs') = (fs' , List.take (length a) vs ++ vs' , lis' ++ cis') , (pbr , tstate pfs' (tvtake (length a) pvs tv++ pvs') (plis'' ti++ pcis')) 
    where plis'' = weaken:-is c ( subst (λ x → lis' :-is x ⇒ a' / r) (take-length a e) plis')

  safety (fs , bool false ∷ vs , br-if .(length q) ∷ is) (tstate pfs (tbool ∷ pvs) (((.(_ ⇒ _ / q ++ a ∷ _) , e) , tbrifn {a = a} {q = q} {r = r} .(length q) refl refl , refl) ∷ pis)) =
    (fs , vs , is) , (refl , tstate pfs pvs pis)

module TypeExample where
  open Typing
  open Example
  open List using ([] ; _∷_)
  open import Relation.Binary.PropositionalEquality
  -- ex0 = ([] , (nat 1 ∷ nat 2 ∷ []) , (add ∷ []))
  tex0 : ex0 :- nat ∷ []
  tex0 = tstate [] (tnat ∷ tnat ∷ []) (to:-i' tadd ∷ [])
  -- ex1 = ([] , (bool true ∷ nat 1 ∷ nat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
  tex1 : ex1 :- nat ∷ []
  tex1 = tstate [] (tbool ∷ tnat ∷ tnat ∷ []) (weaken:-i (nat ∷ nat ∷ []) tnot ∷ to:-i' p ∷ [])
    where p = tif-else (to:-i' tadd ∷ []) (weaken:-i (nat ∷ []) tdrop ∷ [])
  -- ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (nat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
  tex2 : ex2 :- nat ∷ []
  tex2 = tstate [] [] (to:-i' (tblock (to:-i' (tconst tnat) ∷  to:-i' (tblock (to:-i' (tbrn {q = (nat ∷ []) ∷ []} {r = []} 1 refl refl) ∷ [])) ∷ [])) ∷ []) 
