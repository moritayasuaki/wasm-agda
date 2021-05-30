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

  {-
  module Numeric where
    infix 2 _:-i_
    data _:-i_ : n-insn → functype → Set

    data _:-i_ where
      tn-const : ∀{t v} → v :-v t → n-const v :-i [] ⇒ t ∷ []
      tn-nop : n-nop :-i bool ∷ [] ⇒ bool ∷ []
      tn-not : n-not :-i bool ∷ bool ∷ [] ⇒ bool ∷ []
      tn-and : n-and :-i bool ∷ bool ∷ [] ⇒ bool ∷ []
      tn-add : n-add :-i nat ∷ nat ∷ [] ⇒ nat ∷ []
      tn-sub : n-sub :-i nat ∷ nat ∷ [] ⇒ nat ∷ []
      tn-eqz : n-eqz :-i nat ∷ [] ⇒ bool ∷ []
      tn-dup : ∀{t} → n-dup :-i t ∷ [] ⇒ t ∷ t ∷ []
      tn-drop : ∀{t} → n-drop :-i t ∷ [] ⇒ []
  -}

  data _:-is_ : insns → lfunctype → Set
  data _:-i_ : insn → lfunctype → Set
  _:-i'_ : insn → lfunctype → Set

  data _:-i_ where
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
      tstore : ∀{p} → store :-i nat ∷ nat ∷ [] ⇒ [] / p
      tload : ∀{p} → load :-i nat ∷ [] ⇒ nat ∷ [] / p
      tgrow : ∀{p} → grow :-i nat ∷ [] ⇒ nat ∷ [] / p

  data _:-is_ where
      [] : ∀ {a p} → [] :-is a ⇒ a / p
      _∷_ : ∀ {a b c p i is}
            → i :-i' a ⇒ b / p
            → is :-is b ⇒ c / p
            → i ∷ is :-is a ⇒ c / p

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

  tbr-helper : ∀{a b c d q r fs vs is} →
    (fs :-fs a / q ++ (b ∷ r) ⇒ c) →
    (vs :-vs b ++ d) → ∃ λ a' → ∃ λ fs' → ∃ λ vs' → ∃ λ lis' → ∃ λ cis' →
    Interpreter.Control.br-helper (length q) (fs , vs , is) ≡ Interpreter.ok' (fs' , List.take (length b) vs ++ vs' , lis' ++ cis') × ((vs' , length b , lis' , cis') ∷ fs' :-fs a' / (b ∷ r) ⇒ c)
  tbr-helper {b = b} {q = q} {fs = fs} {vs = vs} pfs pvs with List.drop (length q) fs | inspect (List.drop (length q)) fs
  ... | ffs' | [ dropq-fs≡ffs' ] with tfdrop pfs 
  ...                               |  (a' , pffs') with tfheadtail pffs'
  ...                                                  | (f , fs' , b' , pf' , pfs' , dropq-fs≡f'∷fs') with trans (sym dropq-fs≡ffs') dropq-fs≡f'∷fs'
  tbr-helper {b = b} {q = q} {fs = fs} {vs = vs} pfs pvs | .((vs' , length a , lis' , cis') ∷ fs') | [ dropq-fs≡ffs' ] | a' , pffs' | (vs' , .(length a) , lis' , cis') , fs' , b' , tframe {a} plis' pvs' pcis' refl , pfs' , dropq-fs≡f'∷fs' | refl = (a' , fs' , vs' , lis' , cis' , refl , tframe plis' pvs' pcis' refl ∷ pfs')
{-
  tbr-helper' : ∀{m a b c d q r fs vs is} →
    (fs :-fs a / q ++ (b ∷ r) ⇒ c) →
    (vs :-vs b ++ d) → ∃ λ a' → ∃ λ fs' → ∃ λ vs' → ∃ λ lis' → ∃ λ cis' →
    (Interpreter.fromControl Interpreter.Control.br-helper) (length q) (m , fs , vs , is) ≡ Interpreter.ok' (m , fs' , List.take (length b) vs ++ vs' , lis' ++ cis') × ((vs' , length b , lis' , cis') ∷ fs' :-fs a' / (b ∷ r) ⇒ c)
  tbr-helper' {b = b} {q = q} {fs = fs} {vs = vs} pfs pvs with List.drop (length q) fs | inspect (List.drop (length q)) fs
  ... | ffs' | [ dropq-fs≡ffs' ] with tfdrop pfs 
  ...                               |  (a' , pffs') with tfheadtail pffs'
  ...                                                  | (f , fs' , b' , pf' , pfs' , dropq-fs≡f'∷fs') with trans (sym dropq-fs≡ffs') dropq-fs≡f'∷fs'
  tbr-helper' {b = b} {q = q} {fs = fs} {vs = vs} pfs pvs | .((vs' , length a , lis' , cis') ∷ fs') | [ dropq-fs≡ffs' ] | a' , pffs' | (vs' , .(length a) , lis' , cis') , fs' , b' , tframe {a} plis' pvs' pcis' refl , pfs' , dropq-fs≡f'∷fs' | refl = (a' , fs' , vs' , lis' , cis' , refl , tframe plis' pvs' pcis' refl ∷ pfs')
-}
  data _:-_ : config → resulttype → Set where
    tconfig : ∀ {a b c m vs is fs}
             → fs :-fs b ⇒ c
             → vs :-vs a
             → is :-is a ⇒ b
             → (m , fs , vs , is) :- c

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

  data safe (st : config) {t : resulttype} (p : st :- t) : Set where
    prog-trap : (s : String) → (estep st ≡ trap') → safe st p
    prog-done : (m : mem) → (vs : vals) → (estep st ≡ done' m vs) → (vs :-vs t) → safe st p
    prog-ok : (st' : config) → (estep st ≡ ok' st') → (st' :- t) → safe st p

  safety : (st : config) {t : resulttype} (p : st :- t) → safe st p
  safety (m , [] , vs , []) (tconfig [] tvs []) = prog-done m vs refl tvs
  safety (m , (vs' , _ , _ , cis) ∷ fs , vs , []) (tconfig (tframe _ pvs' pcis _ ∷ pfs) pvs []) = prog-ok (m , fs , vs ++ vs' , cis) refl ((tconfig pfs (pvs tv++ pvs') pcis))
  safety (m , fs , vs , const x ∷ is) (tconfig pfs pvs ((_ , tconst pv , refl) ∷ pis)) = prog-ok (m , fs , x ∷ vs , is) refl (tconfig pfs (pv ∷ pvs) pis)
  safety (m , fs , vs , nop ∷ is) (tconfig pfs pvs ((_ , tnop , refl) ∷ pis)) = prog-ok (m , fs , vs , is) refl (tconfig pfs pvs pis)
  safety (m , fs , bool b ∷ vs , not ∷ is) (tconfig pfs (tbool ∷ pvs) ((_ , tnot , refl) ∷ pis)) = prog-ok (m , fs , ( bool (Bool.not b) ∷ vs) , is) refl (tconfig pfs (tbool ∷ pvs) pis)
  safety (m , fs , bool b0 ∷ bool b1 ∷ vs , and ∷ is) (tconfig pfs (tbool ∷ tbool ∷ pvs) ((_ , tand , refl) ∷ pis)) =  prog-ok (m , fs , (bool (b0 Bool.∧ b1) ∷ vs) , is) refl (tconfig pfs (tbool ∷ pvs) pis) 
  safety (m , fs , nat n0 ∷ nat n1 ∷ vs , add ∷ is) (tconfig pfs (tnat ∷ tnat ∷ pvs) ((_ , tadd , refl) ∷ pis)) = prog-ok (m , fs , (nat (n0 Nat.+ n1) ∷ vs) , is) refl (tconfig pfs (tnat ∷ pvs) pis)
  safety (m , fs , nat n0 ∷ nat n1 ∷ vs , sub ∷ is) (tconfig pfs (tnat ∷ tnat ∷ pvs) ((_ , tsub , refl) ∷ pis)) = prog-ok (m , fs , (nat (n0 Nat.∸ n1) ∷ vs) , is) refl (tconfig pfs (tnat ∷ pvs) pis)
  safety (m , fs , nat n ∷ vs , eqz ∷ is) (tconfig pfs (tnat ∷ pvs) ((_ , teqz , refl) ∷ pis)) = prog-ok (m , fs , (bool (feqz n) ∷ vs) , is) refl (tconfig pfs (tbool ∷ pvs) pis)
  safety (m , fs , v ∷ vs , dup ∷ is) (tconfig pfs (pv ∷ pvs) ((_ , tdup , refl) ∷ pis)) =  prog-ok (m , fs , (v ∷ v ∷ vs) , is) refl (tconfig pfs (pv ∷ pv ∷ pvs) pis) 
  safety (m , fs , v ∷ vs , drop ∷ is) (tconfig pfs (_ ∷ pvs) ((_ , tdrop , refl) ∷ pis)) =  prog-ok (m , fs , vs , is) refl (tconfig pfs pvs pis)

  safety (m , fs , nat a ∷ nat v ∷ vs , store ∷ is) (tconfig tfs (tnam ∷ tnat ∷ tvs) ((_ , tstore , refl) ∷ tis)) = prog-ok ({!!} , fs , vs , is) {!!} {!!}
  safety (m , fs , nat a ∷ vs , load ∷ is) (tconfig tfs (tnat ∷ tvs) ((_ , tload , refl) ∷ tis)) =  prog-ok (m , fs , {!!} ∷ vs , is) {!!} {!!}
  safety (m , fs , vs , grow ∷ is) (tconfig tfs (tnat ∷ tvs) ((_ , tgrow , refl) ∷ tis)) =  prog-ok ({!!}  , fs , nat {!!} ∷ vs , is) {!!} {!!}

  safety (m , fs , vs , block (a ⇒ b) bis ∷ is) (tconfig pfs pvs (_∷_ {c = d} ((.a ⇒ b / p , c) , tblock pbis , refl) pis)) =
    prog-ok (m , ((List.drop (length a) vs , length b , [] , is)) ∷ fs ,  List.take (length a) vs ,  bis)  refl (tconfig (((tframe [] (tvdrop (length a) pvs) pis' refl) ∷ pfs)) ((tvtake (length a) pvs)) pbis') where
      pis' = subst (λ x → is :-is b ++ x ⇒ d / p) (drop-length a c) pis
      pbis' = subst (λ x → bis :-is x ⇒ b / b ∷ p) (take-length a c) pbis
  safety (m , fs , bool bb ∷ vs , if-else (a ⇒ b) tis fis ∷ is) (tconfig pfs (tbool ∷ pvs) (_∷_ {c = d} (((.(bool ∷ a) ⇒ .b / p) , c) , tif-else ptis pfis , refl) pis)) with bb
  ... | true = prog-ok (m , (List.drop (length a) vs , length b , [] , is) ∷ fs , List.take (length a) vs , tis) refl (tconfig ((tframe [] (tvdrop (length a) pvs) pis' refl) ∷ pfs) (tvtake (length a) pvs) pbis')  where
    pis' = subst (λ x → is :-is b ++ x ⇒ d / p) (drop-length a c) pis
    pbis' = subst (λ x → tis :-is x ⇒ b / b ∷ p) (take-length a c) ptis
  ... | false =  prog-ok (m , (List.drop (length a) vs , length b , [] , is) ∷ fs , List.take (length a) vs , fis) refl (tconfig ((tframe [] (tvdrop (length a) pvs) pis' refl) ∷ pfs) (tvtake (length a) pvs) pbis')  where
    pis' = subst (λ x → is :-is b ++ x ⇒ d / p) (drop-length a c) pis
    pbis' = subst (λ x → fis :-is x ⇒ b / b ∷ p) (take-length a c) pfis

  safety (m , fs , vs , loop (a ⇒ b) lis ∷ is) (tconfig pfs pvs (_∷_ {c = d} (((.a ⇒ .b / p) , c) , tloop plis , refl) pis)) =
     prog-ok (m , (List.drop (length a) vs , length a , loop (a ⇒ b) lis ∷ [] , is) ∷ fs , List.take (length a) vs , lis) refl (tconfig ((tframe (weaken:-i [] (tloop plis) ∷ []) (tvdrop (length a) pvs) pis' len-a) ∷ pfs) (tvtake (length a) pvs) plis') where
      pis' = subst (λ x → is :-is (b ++ []) ++ x ⇒ d / p) (drop-length a c) ∘ subst (λ x → is :-is x ++ c ⇒ d / p) (sym (++-identityʳ b)) $ pis
      len-a = sym (cong List.length (++-identityʳ a))
      plis' = subst (λ x → lis :-is x ⇒ b ++ [] / (a ++ []) ∷ p) (take-length a c) (subst (λ x → lis :-is a ⇒ x / (a ++ []) ∷ p) (sym (++-identityʳ b)) (subst (λ x → lis :-is a ⇒ b / x ∷ p) (sym (++-identityʳ a)) plis))

  safety (m , fs , vs , br .(length q) ∷ is) (tconfig pfs pvs (((.(_ ⇒ _ / q ++ a ∷ _) , e) , tbrn {a = a} {q = q} {r = r} .(length q) refl refl , refl) ∷ pis)) with tbr-helper {is = is} pfs pvs
  ... | a' , fs' , vs' , lis' , is' , pbr , (tframe {c = c} plis' pvs' pis' refl ∷ pfs') = prog-ok (m , fs' , List.take (length a) vs ++ vs' , lis' ++ is') pbr' (tconfig pfs' (tvtake (length a) pvs tv++ pvs') (plis'' ti++ pis')) where
    plis'' = weaken:-is c (subst (λ x → lis' :-is x ⇒ a' / r) (take-length a e) plis')
    pbr' = cong (fromControlE (m , fs , vs , is)) pbr

  safety (m , fs , bool true ∷ vs , br-if .(length q) ∷ is) (tconfig pfs (tbool ∷ pvs) (((.(_ ⇒ _ / q ++ a ∷ _) , e) , tbrifn {a = a} {q = q} {r = r} .(length q) refl refl , refl) ∷ pis)) with tbr-helper {is = is} pfs pvs
  ... | a' , fs' , vs' , lis' , is' , pbr , (tframe {c = c} plis' pvs' pis' refl ∷ pfs') = prog-ok (m , fs' , List.take (length a) vs ++ vs' , lis' ++ is') pbr' (tconfig pfs' (tvtake (length a) pvs tv++ pvs') (plis'' ti++ pis')) where
    plis'' = weaken:-is c (subst (λ x → lis' :-is x ⇒ a' / r) (take-length a e) plis')
    pbr' = cong (fromControlE (m , fs , bool true ∷ vs , is)) pbr

  safety (m , fs , bool false ∷ vs , br-if .(length q) ∷ is) (tconfig pfs (tbool ∷ pvs) (((.(_ ⇒ _ / q ++ a ∷ _) , e) , tbrifn {a = a} {q = q} {r = r} .(length q) refl refl , refl) ∷ pis)) =
    prog-ok (m , fs , vs , is) refl (tconfig pfs pvs pis)


module TypeExample where
  open Typing
  open Example
  open List using ([] ; _∷_)
  open import Relation.Binary.PropositionalEquality
  -- ex0 = ([] , (nat 1 ∷ nat 2 ∷ []) , (add ∷ []))
  tex0 = tconfig [] (tnat ∷ tnat ∷ []) (to:-i' tadd ∷ [])
  -- ex1 = ([] , (bool true ∷ nat 1 ∷ nat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
  tex1 : ex1 :- nat ∷ []
  tex1 = tconfig [] (tbool ∷ tnat ∷ tnat ∷ []) (weaken:-i (nat ∷ nat ∷ []) tnot ∷ to:-i' p ∷ [])
    where p = tif-else (to:-i' tadd ∷ []) (weaken:-i (nat ∷ []) tdrop ∷ [])
  -- ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (nat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
  tex2 : ex2 :- nat ∷ []
  tex2 = tconfig [] [] (to:-i' (tblock (to:-i' (tconst tnat) ∷  to:-i' (tblock (to:-i' (tbrn {q = (nat ∷ []) ∷ []} {r = []} 1 refl refl) ∷ [])) ∷ [])) ∷ []) 
