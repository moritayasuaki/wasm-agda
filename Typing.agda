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
      tconst : ∀{t v} → v :-v t → const v :-i [] ⇒ t ∷ [] / []
      tnop : nop :-i [] ⇒ [] / []
      tnot : not :-i bool ∷ [] ⇒ bool ∷ [] / []
      tand : and :-i bool ∷ bool ∷ [] ⇒ bool ∷ [] / []
      tadd : add :-i nat ∷ nat ∷ [] ⇒ nat ∷ [] / []
      tsub : sub :-i nat ∷ nat ∷ [] ⇒ nat ∷ [] / []
      teqz : eqz :-i nat ∷ [] ⇒ bool ∷ [] / []
      tdup : ∀{t} → dup :-i t ∷ [] ⇒ t ∷ t ∷ [] / []
      tdrop : ∀{t} → drop :-i t ∷ [] ⇒ [] / []
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

  weaken:-i : ∀{a b p i} → (c : resulttype) → (q : labelstype) → (i :-i a ⇒ b / p) → i :-i' a ++ c ⇒ b ++ c / p ++ q
  weaken:-i {a} {b} {p} {i} c q pi = (a ⇒ b / p , c , q) , (pi , refl)

  data _:-f_ : frame → lctxtype → Set where
    tframe : ∀ {a b p c d vs lis n cis}
             → lis :-is a ⇒ b / p
             → vs :-vs c
             → cis :-is b ++ c ⇒ d / p
             → (vs , n , lis , cis) :-f b / a ∷ p ⇒ d / p

  _:-f'_ : frame → lctxtype → Set
  f :-f' t = ∃ {A = lctxtype × labelstype} λ (a / p ⇒ b / q , r) → (f :-f a / p ⇒ b / q) × (t ≡ a / p ++ r ⇒ b / q ++ r)

  weaken:-f : ∀{a p b q f} → (r : labelstype) → (f :-f a / p ⇒ b / q) → f :-f' a / p ++ r ⇒ b / q ++ r
  weaken:-f {a} {p} {b} {q} {f} r pf = (a / p ⇒  b / q , r) , (pf , refl)

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

  exeq-lfunctype : ∀{a a' b b' : resulttype} → ∀{p p' : labelstype} → a ⇒ b / p ≡ a' ⇒ b' / p' → a ≡ a' × b ≡ b' × p ≡ p' 
  exeq-lfunctype refl = refl , refl , refl

  exeq-lctxtype : ∀{a a' b b' : resulttype} → ∀{p p' q q' : labelstype} → a / p ⇒ b / q ≡ a' / p' ⇒ b' / q' → a ≡ a' × p ≡ p' × b ≡ b' × q ≡ q'
  exeq-lctxtype refl = refl , refl , refl , refl

  weaken:-is : ∀{is a b p} → (c : resulttype) → (q : labelstype) → is :-is a ⇒ b / p → is :-is a ++ c ⇒ b ++ c / p ++ q
  weaken:-is c q [] = []
  weaken:-is {i ∷ is} {a} {b} {p} c q (_∷_ {b = d} pi' pis) with pi'
  ... | (a' ⇒ d' / p' , c' , q') , (pi , eq) =
    let (a≡a'++c' , d≡d'++c' , p≡p'++q') = exeq-lfunctype eq in
    let pi-w = weaken:-i (c' ++ c) (q' ++ q) pi |>
               subst (λ x → i :-i' x ⇒ d' ++ c' ++ c / p' ++ q' ++ q) (lemma a a' c' c a≡a'++c') |>
               subst (λ x → i :-i' a ++ c ⇒ x / p' ++ q' ++ q) (lemma d d' c' c d≡d'++c') |>
               subst (λ x → i :-i' a ++ c ⇒ d ++ c / x) (lemma p p' q' q p≡p'++q') in
    let pis-w = weaken:-is c q pis in pi-w ∷ pis-w


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
  safety ((vs , _ , _ , cis) ∷ fs , vs' , []) (tstate (_∷_ {a = a / p'} {b = c / p} pf' pfs) pvs' []) with pf'
  ... | (a' / l ∷ q ⇒ c' / _ , r) , (pf  , eq) with pf
  ...   | tframe {a = l} {b = a'} {c = b} {d = c'}  _ pvs pcis =
    let (a≡a' , p'≡l∷q++r , c≡c' , p≡q++r) = exeq-lctxtype eq in
    let cis:a++b⇒c/p = pcis |>
                       subst (λ x → cis :-is x ++ b ⇒ c' / q) (sym a≡a') |>
                       subst (λ x → cis :-is a ++ b ⇒ x / q) (sym c≡c') |>
                       weaken:-is [] r |>
                       subst (λ x → cis :-is (a ++ b) ++ [] ⇒ c ++ [] / x) (sym p≡q++r) |>
                       subst (λ x → cis :-is x ⇒ c ++ [] / p) (lemma2 (a ++ b)) |>
                       subst (λ x → cis :-is a ++ b ⇒ x / p) (lemma2 c) in 
    (fs , vs' ++ vs , cis) , (refl , tstate pfs (pvs' tv++ pvs) cis:a++b⇒c/p)
  safety ([] , vs , const x ∷ is) (tstate {b = b} pfs pvs (pi' ∷ pis)) with pi'
  ... | (_ , _ , r) , (tconst {t = t} pv , eq) =
    let (b≡c' , a≡t∷c' , _) = exeq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) a≡t∷c' |>
                subst (λ x → is :-is t ∷ x ⇒ b) (sym b≡c') in
    ([] , x ∷ vs , is) , (refl , tstate pfs (pv ∷ pvs) proof)
  safety ([] , vs , nop ∷ is) (tstate {b = b} pfs pvs (pi' ∷ pis)) with pi'
  ... | _ , (tnop , eq) =
    let (a'≡b , a≡b , _) = exeq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) (trans a≡b (sym a'≡b)) in
    ([] , vs , is) , (refl , tstate pfs pvs proof)
  safety ([] , v ∷ vs , dup ∷ is) (tstate {b = b} pfs (pv ∷ pvs) (pi' ∷ pis)) with pi'
  ... | _ , (tdup , eq) =
    let (a≡b , b≡ttd , _) = exeq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) (trans b≡ttd (sym (cong dup'' a≡b))) in
    ([] , v ∷ v ∷ vs , is) , (refl , tstate pfs (pv ∷ pv ∷ pvs) proof)
    where dup'' : resulttype → resulttype
          dup'' (x ∷ xs) = x ∷ x ∷ xs
          dup'' [] = []
  safety ([] , v ∷ vs , drop ∷ is) (tstate {b = b} pfs (pv ∷ pvs) (pi' ∷ pis)) with pi'
  ... | _ , (tdrop , eq) =
    let (a≡b , b≡d , _) = exeq-lfunctype eq in
    let proof = pis |>
                subst (λ x → is :-is x ⇒ b) (trans b≡d (sym (cong drop'' a≡b))) in
    ([] , vs , is) , (refl , tstate pfs pvs proof)
    where drop'' : resulttype → resulttype
          drop'' (x ∷ xs) = xs
          drop'' [] = []
  safety ([] , vs , block (a ⇒ b) is ∷ cis) (tstate {a = a'} {b = b' / p''} {c} pfs pvs (_∷_ {a = a'} {b = b''} {c = b'} {p = p''} pi' pcis)) with pi'
  ... | (a ⇒ b / p , q , r) , (tblock {a} {b} {p} pis' , a'⇒b''/p''≡a++q⇒b++q/p++r) =
    let (a'≡a++q , b''≡b++q , p≡f++r) = exeq-lfunctype a'⇒b''/p''≡a++q⇒b++q/p++r in
    let pr' = lemma3 a' a q a'≡a++q in
    let pr'' = subst (λ x → is :-is x ⇒ b / b ∷ p) pr' pis' in
    ((List.drop (length a) vs , length b , [] , cis) ∷ [] , List.take (length a) vs , is) ,
    (refl , tstate (((b'' / b'' ∷ [] ⇒ {!!} / {!!} , []) , tframe [] (tvdrop (length a) pvs) {!!} , {!!}) ∷ pfs) (tvtake (length a) pvs) pr'')
      where pcis' = pcis
