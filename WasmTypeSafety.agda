module WasmTypeSafety where

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

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module _ where
  open import WasmTyping
  open import Wasm
  open Bool
  open Syntax
  open Typing
  open String hiding (_++_ ; length)
  open List
  open import Data.List.Properties
  open Product
  open Function
  open Interpreter

  data safe (st : config) {t : resulttype} (p : st :- t) : Set where
    prog-trap : (s : String) → (estep st ≡ trap') → safe st p
    prog-done : (m : mem) → (vs : vals) → (estep st ≡ done' m vs) → (vs :-vs t) → safe st p
    prog-ok : (st' : config) → (estep st ≡ ok' st') → (st' :- t) → safe st p

  open import Relation.Nullary.Decidable
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



  safety (record { limit = limit ; assign = assign } , fs , nat v ∷ nat ea ∷ vs , store ∷ is) (tconfig tfs (tnam ∷ (tnat ∷ tvs)) ((t , tstore , refl) ∷ tis)) with inspect (ea Nat.<ᵇ_) limit | ea Nat.<ᵇ limit
  ... | Relation.Binary.PropositionalEquality.[ refl ] | false = prog-trap "access to outside memory" {! refl  !}
  ... | Relation.Binary.PropositionalEquality.[ refl ] | true = prog-ok ((Memory.reassign ea v record { limit = limit ; assign = assign } , fs , vs , is)) {! refl  !} (tconfig tfs tvs tis)
  safety (record { limit = limit ; assign = assign } , fs , nat a ∷ vs , load ∷ is) (tconfig tfs (tnat ∷ tvs) ((_ , tload , refl) ∷ tis)) with inspect (a Nat.<ᵇ_) limit | (a Nat.<ᵇ limit)
  ... | Relation.Binary.PropositionalEquality.[ refl ] | false = prog-trap "access to outside memory" {! refl  !}
  ... | Relation.Binary.PropositionalEquality.[ refl ] | true = prog-ok ((record { limit = limit ; assign = assign } , fs , nat (assign a) ∷ vs , is)) {! refl  !} ((tconfig tfs (tnat ∷ tvs) tis))
  safety (record { limit = limit ; assign = assign } , fs , nat n ∷ vs , grow ∷ is) (tconfig tfs (tnat ∷ tvs) ((_ , tgrow , refl) ∷ tis)) = prog-ok (record { limit = limit Nat.+ n ; assign = assign } , fs , nat limit ∷ vs , is) refl ((tconfig tfs (tnat ∷ tvs) tis))

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
  open import WasmTyping
  open Typing
  open Example
  open List using ([] ; _∷_)
  open import Relation.Binary.PropositionalEquality
  -- ex0 = ([] , (nat 1 ∷ nat 2 ∷ []) , (add ∷ []))
  tex0 : ex0 :- nat ∷ []
  tex0 = tconfig [] (tnat ∷ tnat ∷ []) (to:-i' tadd ∷ [])
  -- ex1 = ([] , (bool true ∷ nat 1 ∷ nat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
  tex1 : ex1 :- nat ∷ []
  tex1 = tconfig [] (tbool ∷ tnat ∷ tnat ∷ []) (weaken:-i (nat ∷ nat ∷ []) tnot ∷ to:-i' p ∷ [])
    where p = tif-else (to:-i' tadd ∷ []) (weaken:-i (nat ∷ []) tdrop ∷ [])
  -- ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (nat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
  tex2 : ex2 :- nat ∷ []
  tex2 = tconfig [] [] (to:-i' (tblock (to:-i' (tconst tnat) ∷  to:-i' (tblock (to:-i' (tbrn {q = (nat ∷ []) ∷ []} {r = []} 1 refl refl) ∷ [])) ∷ [])) ∷ []) 
