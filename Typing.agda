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
  lemma ab a b c ab=a++b = sym proof
    where
      ab++c=[a++b]++c = cong (List._++ c) ab=a++b
      [a++b]++c=a++b++c = ++-assoc a b c
      proof = trans ab++c=[a++b]++c [a++b]++c=a++b++c 
  lemma2 : ∀ {X : Set} → (a : List X) → a ++ [] ≡ a
  lemma2 a = ++-identityʳ a

  lemma3' : ∀ {X : Set} → (b c : List X) → b ≡ take (length b) (b ++ c)
  lemma3' [] ys = refl
  lemma3' (x ∷ xs) ys = let p = cong (x ∷_) (lemma3' xs ys)
                         in trans p (t2 (length xs))
                         where t2 : ∀ n → x ∷ take n (xs ++ ys) ≡ take (suc n) (x ∷ xs ++ ys)
                               t2 n = refl

  lemma3 : ∀ {X : Set} → (a b c : List X) → a ≡ b ++ c → b ≡ take (length b) a
  lemma3 a b c p = let p' = cong (λ x → take (length b) x) p in
                   let d = (sym (lemma3' b c)) in
                   let e = trans p' d in sym e

  lemma4' : ∀ {X : Set} → (b c : List X) → c ≡ drop (length b) (b ++ c)
  lemma4' [] ys = refl
  lemma4' (x ∷ xs) ys = let p = lemma4' xs ys
                         in trans p (t2 (length xs))
                         where t2 : ∀ n → drop n (xs ++ ys) ≡ drop (suc n) (x ∷ xs ++ ys)
                               t2 n = refl

  lemma4 : ∀ {X : Set} → (a b c : List X) → a ≡ b ++ c → c ≡ drop (length b) a
  lemma4 a b c p = let p' = cong (λ x → drop (length b) x) p in
                   let d = (sym (lemma4' b c)) in
                   let e = trans p' d in sym e

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

  {-
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
  -} 
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
    i :-i' t = ∃ {A = lfunctype × resulttype} λ (a ⇒ b / p , c) → (i :-i a ⇒ b / p) × (t ≡ a ++ c ⇒ b ++ c / p)

  weaken:-i : ∀{a b p i} → (c : resulttype) → (i :-i a ⇒ b / p) → i :-i' a ++ c ⇒ b ++ c / p
  weaken:-i {a} {b} {p} {i} c pi = (a ⇒ b / p , c) , (pi , refl)

  data _:-f_ : frame → lctxtype → Set where
    tframe : ∀ {a b p c d vs lis n cis}
             → lis :-is a ⇒ b / p
             → vs :-vs c
             → cis :-is b ++ c ⇒ d / p
             → n ≡ length a
             → (vs , n , lis , cis) :-f b / a ∷ p ⇒ d / p

  data _:-fs_ : frames → ctxtype → Set where
    []  : ∀ {a} → [] :-fs a / [] ⇒ a
    _∷_ : ∀ {f fs a b c}
          → f :-f (a ⇒ b)
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
  safety ((vs , _ , _ , cis) ∷ fs , vs' , []) (tstate (_∷_ {a = a / p'} {b = c / p} pf pfs) pvs' []) with pf
  ... | tframe {a = l} {b = a'} {c = b} {d = c'}  _ pvs pcis _ =
    (fs , vs' ++ vs , cis) , (refl , tstate pfs (pvs' tv++ pvs) pcis)
  safety ([] , vs , const x ∷ is) (tstate {b = b} pfs pvs (pi' ∷ pis)) with pi'
  ... | (_ , _) , (tconst {t = t} pv , eq) =
    let (b≡c' , a≡t∷c' , _) = eq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) a≡t∷c' |>
                subst (λ x → is :-is t ∷ x ⇒ b) (sym b≡c') in
    ([] , x ∷ vs , is) , (refl , tstate pfs (pv ∷ pvs) proof)
  safety ([] , vs , nop ∷ is) (tstate {b = b} pfs pvs (pi' ∷ pis)) with pi'
  ... | _ , (tnop , eq) =
    let (a'≡b , a≡b , _) = eq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) (trans a≡b (sym a'≡b)) in
    ([] , vs , is) , (refl , tstate pfs pvs proof)
  safety ([] , v ∷ vs , dup ∷ is) (tstate {b = b} pfs (pv ∷ pvs) (pi' ∷ pis)) with pi'
  ... | _ , (tdup , eq) =
    let (a≡b , b≡ttd , _) = eq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) (trans b≡ttd (sym (cong dup'' a≡b))) in
    ([] , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv ∷ pv ∷ pvs) proof)
    where dup'' : resulttype → resulttype
          dup'' (x ∷ xs) = x ∷ x ∷ xs
          dup'' [] = []
  safety ([] , v ∷ vs , drop ∷ is) (tstate {b = b} pfs (pv ∷ pvs) (pi' ∷ pis)) with pi'
  ... | _ , (tdrop , eq) =
    let (a≡b , b≡d , _) = eq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) (trans b≡d (sym (cong (List.drop 1) a≡b))) in
    ([] , vs , is) , (refl , tstate pfs pvs proof)

  safety ([] , vs , block (a ⇒ b) is ∷ cis) (tstate {a = a'} {b = b' / p'} {c'} pfs pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = p'} pi' pcis)) with pi'
  ... | (a ⇒ b / p , c) , (tblock {a} {b} {p} pis , a'⇒b''/p'≡a++c⇒b++c/p++r) =
    let (a'≡a++c , b''≡b++c , p'≡p) = eq-lfunctype a'⇒b''/p'≡a++c⇒b++c/p++r in
    let pis' = subst (λ x → is :-is x ⇒ b / b ∷ p) (lemma3 a' a c a'≡a++c) pis in
    let pis'' = subst (λ x → is :-is List.take (length a) a' ⇒ b / b ∷ x) (sym p'≡p) pis' in
    let pcis' = subst (λ x → cis :-is x ⇒ b' / p') (b''≡b++c) pcis in
    let pcis'' = subst (λ x → cis :-is b ++ x ⇒ b' / p') (lemma4 a' a c a'≡a++c) pcis' in
    ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is) ,
    (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis'' refl) ∷ pfs) (tvtake (length a) pvs) pis'')

  safety ([] , bool bb ∷ vs , if-else (a ⇒ b) is-t is-f ∷ cis) (tstate {a = bool ∷ a'} {b = b' / p'} {c'} pfs (tbool ∷ pvs) (_∷_ {a = bool ∷ a'} {b = b''} {c = b'} {p = p''} pi' pcis)) with pi'
  ... | ((bool ∷ a) ⇒ b / p , c) , (tif-else {a} {b} {p} pis-t pis-f , eq) with bb
  ...   | true =
    let (bool∷a'≡bool∷a++c , b''≡b++c , p'≡p) = eq-lfunctype eq in
    let a'≡a++c : a' ≡ a ++ c
        a'≡a++c = cong (List.drop 1) bool∷a'≡bool∷a++c in
    let pis-t' = subst (λ x → is-t :-is x ⇒ b / b ∷ p) (lemma3 a' a c a'≡a++c) pis-t in
    let pis-t'' = subst (λ x → is-t :-is List.take (length a) a' ⇒ b / b ∷ x) (sym p'≡p) pis-t' in
    let pcis' = subst (λ x → cis :-is x ⇒ b' / p') (b''≡b++c) pcis in
    let pcis'' = subst (λ x → cis :-is b ++ x ⇒ b' / p') (lemma4 a' a c a'≡a++c) pcis' in
    ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is-t) ,
    (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis'' refl) ∷ pfs) (tvtake (length a) pvs) pis-t'')
  ...   | false =
    let (bool∷a'≡bool∷a++c , b''≡b++c , p'≡p) = eq-lfunctype eq in
    let a'≡a++c : a' ≡ a ++ c
        a'≡a++c = cong (List.drop 1) bool∷a'≡bool∷a++c in
    let pis-f' = subst (λ x → is-f :-is x ⇒ b / b ∷ p) (lemma3 a' a c a'≡a++c) pis-f in
    let pis-f'' = subst (λ x → is-f :-is List.take (length a) a' ⇒ b / b ∷ x) (sym p'≡p) pis-f' in
    let pcis' = subst (λ x → cis :-is x ⇒ b' / p') (b''≡b++c) pcis in
    let pcis'' = subst (λ x → cis :-is b ++ x ⇒ b' / p') (lemma4 a' a c a'≡a++c) pcis' in
    ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is-f) ,
    (refl , tstate ((tframe [] (tvdrop (length a) pvs) pcis'' refl) ∷ pfs) (tvtake (length a) pvs) pis-f'')

  safety ([] , vs , loop (a ⇒ b) is ∷ cis) (tstate {a = a'} {b = b' / p'} {c'} pfs pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = p'} pi' pcis)) with pi'
  ... | (a ⇒ b / p , c) , (tloop {a} {b} {p} pis' , eq) =
    let (a'≡a++c , b'≡b++c , p≡p') = eq-lfunctype eq in
    let pis'' = subst (λ x → is :-is x ⇒ b / a ∷ p) (lemma3 a' a c a'≡a++c) pis' in
    let pis''' = subst (λ x → is :-is List.take (length a) a' ⇒ x / a ∷ p) (sym (++-identityʳ b)) pis'' in
    let pis'''' = subst (λ x → is :-is List.take (length a) a' ⇒ b ++ [] / x ∷ p) (sym (++-identityʳ a)) pis''' in
    let pcis' = subst (λ x → cis :-is x ⇒ b' / p') (b'≡b++c) pcis in
    let pcis'' = subst (λ x → cis :-is b ++ x ⇒ b' / p') (lemma4 a' a c a'≡a++c) pcis' in
    let pcis''' = subst (λ x → cis :-is b ++ List.drop (length a) a' ⇒ b' / x) p≡p' pcis'' in
    let pcis'''' = subst (λ x → cis :-is x ++ List.drop (length a) a' ⇒ b' / p) (sym (++-identityʳ b)) pcis''' in
    let pfs' = subst (λ x → [] :-fs b' / x ⇒ c') p≡p' pfs in
    ((List.drop (length a) vs , length a , loop (a ⇒ b) is ∷ [] , cis) ∷ [] , List.take (length a) vs , is) ,
    (refl , tstate ((tframe (weaken:-i [] (tloop pis') ∷ []) (tvdrop (length a) pvs) pcis'''' (cong length (sym (++-identityʳ a)))) ∷ pfs') (tvtake (length a) pvs) pis'''')

  safety ((vs' , m , lis , cis) ∷ fs , vs , br 0 ∷ is) (tstate {a = a'} {b = b' / a'' ∷ p'} {c'} ((tframe {c = c''} plis pvs' pcis meq) ∷ pfs) pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = a'' ∷ p'} pi' pis)) with pi'
  ... | (a ⇒ b / p , c) , (tbrn n fn p1 p2 , eq) =
    let (g , h , q ) = eq-lfunctype eq in
    let t = cong (λ x → lis :-is List.take x a' ⇒ b' / p') meq in
    let s = subst (λ x → a ≡ lookup x {!!}) q p2 in
    (fs , List.take m vs ++ vs' , lis ++ cis) ,
    (refl , tstate pfs (tvtake m pvs tv++ pvs') {!!}) -- ((weaken:-is c'' plis) ti++ pcis))
