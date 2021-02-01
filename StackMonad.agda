module StackMonad where

open import Data.Fin
open import Category.Monad.Indexed
open import Category.Monad
open import Category.Applicative.Indexed
import Data.List as L
open import Function
open import Level
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding(_>>=_)
open import Data.Nat
open import Data.Empty
open import Category.Monad.State using (IStateT ; StateTIMonad)
open import Category.Monad.Continuation using (DContT ; DContIMonad)

open L using (List ; [] ; _∷_)

module IList where
  data IList {I : Set} (S : I → Set) : List I → Set where
    []  : IList S []
    _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

  split : ∀ {I} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is L.++ js) → IList S is × IList S js
  split [] ws = ([] , ws)
  split (i ∷ is) (v ∷ vs) = let vs , ws = split is vs
                             in v ∷ vs , ws

  take : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is L.++ js) → IList S is
  take is ws = proj₁ (split is ws)

  drop : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is L.++ js) → IList S js
  drop is ws = proj₂ (split is ws)

  dropn : ∀ {I : Set} {S : I → Set} → ∀ (n : ℕ) → ∀ {is} → IList S is → IList S (L.drop n is)
  dropn zero ws = ws
  dropn (suc n) (w ∷ ws) = dropn n ws
  dropn (suc n) [] = []

  _++_ : ∀ {I : Set} {S : I → Set} → ∀ {is js} → IList S is → IList S js → IList S (is L.++ js)
  [] ++ ws = ws
  (v ∷ vs) ++ ws = v ∷ (vs ++ ws)

  [_] : ∀ {I : Set} {S : I → Set} → ∀ {i} → S i → IList S L.[ i ]
  [_] v = v ∷ []

  lookup : ∀ {I : Set} {S : I → Set} → ∀ {is} → IList S is → (n : Fin (L.length is)) → S (L.lookup is n)
  lookup (v ∷ vs) zero = v
  lookup (v ∷ vs) (suc i) = lookup vs i

module I = IList
open I using (IList ; [] ; _∷_)


StackT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
StackT S = IStateT (IList S)


record RawIMonadStack {I : Set} (S : I → Set)
                      (M : List I → List I → Set → Set) : Set₁ where
  field
    monad : RawIMonad M
    pop1   : ∀ {i} → M (i ∷ []) [] (S i)
    push1  : ∀ {i} → S i → M [] (i ∷ []) ⊤
    up    : ∀ {X is js} → M is js X → ∀ {ks} → M (is L.++ ks) (js L.++ ks) X
  open RawIMonad monad public

  pop : ∀ {i is} → M (i ∷ is) is (S i)
  pop = up pop1

  push : ∀ {i is} → S i → M is (i ∷ is) ⊤
  push = λ v → up (push1 v)

  pop-list : ∀ is → ∀ {is'} → M (is L.++ is') is' (IList S is) 
  pop-list [] = return []
  pop-list (i ∷ is) = do v ← pop
                         vs ← pop-list is
                         return (v ∷ vs)

  push-list : ∀ {is is'} → IList S is →  M is' (is L.++ is') ⊤
  push-list [] = return tt
  push-list (v ∷ vs) = do push-list vs
                          push v

  drop : ∀ {is} → (n : Fin (L.length is)) → M is (L.drop (toℕ n) is) ⊤
  drop {i ∷ is} zero = return tt
  drop {i ∷ is} (suc n) = do pop
                             drop {is} n

  pop-nth : ∀ {is} → (n : Fin (L.length is)) → M is (L.drop (ℕ.suc (toℕ n)) is) (S (L.lookup is n))
  pop-nth {i ∷ is} zero = pop
  pop-nth {i ∷ is} (suc n) = do pop
                                pop-nth {is} n

StackTIMonadStack : {I : Set} (S : I → Set) {M : Set → Set}
                    → RawMonad M → RawIMonadStack S (StackT S M)
StackTIMonadStack S Mon = record
  { monad = StateTIMonad (IList S) Mon
  ; pop1 = λ where (s ∷ []) → return (s , []) -- pop1 >> push1 x  ~ set1 x  / pop1 = get1 delete
  ; push1 = λ s [] → return (_ , s ∷ [])      -- pop1 >>= push1   ~ get1    / push1 = set1 ignore
  ; up = λ {_} {is} {_} f ss →
           do let vs , us = I.split is ss
              x , ws ← f vs
              return (x , ws I.++ us)
  } where open RawIMonad Mon


-- const c = λ k0 ... kn v0 . k0 ... kn c v1
-- add = λ k0 ... kn (v0, v1) . k0 ... kn (v0 + v1)
-- br l = k0 k1 k2 k3 ... kn v. kl k_{l+1} ... k{n} v

BlockCont : {I : Set} (K : I → Set) → List I → Set → Set
BlockCont S [] R = R
BlockCont S (i ∷ is) R = (S i → BlockCont S is R) → BlockCont S is R

branch0 : {I : Set} → {S : I → Set} → ∀{R i is}
          → S i → BlockCont S (i ∷ is) R
branch0 v k = k v

block : {I : Set} → {S : I → Set} → ∀{R i is}
        → BlockCont S (i ∷ is) R → (S i → BlockCont S is R) → BlockCont S is R
block a = a

module Example where

open import Data.Bool using (Bool ; _∧_) renaming (not to bool-not)
open import Data.Nat
open import Function.Identity.Categorical as Id using (Identity)

data valtype : Set where
  bool : valtype
  nat : valtype
  unit : valtype

val : valtype -> Set
val bool = Bool
val nat = ℕ
val unit = ⊤

resulttype : Set
resulttype = List valtype 

result : resulttype → Set
result = IList val

OpdStack = StackT val Identity
