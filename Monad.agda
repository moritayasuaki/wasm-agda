module Monad where

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

module _ where
  open List
  open Product

  data List' (X Y : Set) : Set where
    [_]' : X → List' X Y
    _∷'_ : X × Y → List' X Y → List' X Y

  record List'' (X Y : Set) : Set where
    constructor _∷''_
    field
      head'' : X
      tail'' : List (Y × X)

module IList where
  open List using (List ; [] ; _∷_)
  open Product
  open Nat
  open Fin
  data IList {I : Set} (S : I → Set) : List I → Set where
    []  : IList S []
    _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

  split : ∀ {I} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is List.++ js) → IList S is × IList S js
  split [] ws = ([] , ws)
  split (i ∷ is) (v ∷ vs) = let vs , ws = split is vs
                             in v ∷ vs , ws

  take : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is List.++ js) → IList S is
  take is ws = proj₁ (split is ws)

  drop : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is List.++ js) → IList S js
  drop is ws = proj₂ (split is ws)

  dropn : ∀ {I : Set} {S : I → Set} → ∀ (n : ℕ) → ∀ {is} → IList S is → IList S (List.drop n is)
  dropn zero ws = ws
  dropn (suc n) (w ∷ ws) = dropn n ws
  dropn (suc n) [] = []

  _++_ : ∀ {I : Set} {S : I → Set} → ∀ {is js} → IList S is → IList S js → IList S (is List.++ js)
  [] ++ ws = ws
  (v ∷ vs) ++ ws = v ∷ (vs ++ ws)

  [_] : ∀ {I : Set} {S : I → Set} → ∀ {i} → S i → IList S List.[ i ]
  [_] v = v ∷ []

  lookup : ∀ {I : Set} {S : I → Set} → ∀ {is} → IList S is → (n : Fin (List.length is)) → S (List.lookup is n)
  lookup (v ∷ vs) zero = v
  lookup (v ∷ vs) (suc i) = lookup vs i

module IExc where
  open Fin
  open List
  data IExc {I : Set} (S : I → Set) : I → List I → Set where
    ret : ∀ {r rs} → S r → IExc S r rs
    exc : ∀ {r r' rs} → IExc S r' rs → IExc S r (r' ∷ rs)

  excn : {I : Set} {S : I → Set} {r : I} {rs : List I} → (n : Fin (length rs)) → S (lookup rs n) → IExc S r rs
  excn {_} {_} {_} {r ∷ rs} zero v = exc (ret v)
  excn {_} {_} {_} {r ∷ rs} (suc n) v = exc (excn n v)

module _ where
  open IList using (IList ; [] ; _∷_)
  open Category.Monad.State
  open Category.Monad.Indexed
  open Category.Monad
  open Product
  open Unit
  open Fin
  open Nat
  open List using (List ; [] ; _∷_)

  StackT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
  StackT S = IStateT (IList S)


  record RawIMonadStack {I : Set} (S : I → Set)
                        (M : List I → List I → Set → Set) : Set₁ where
    field
      monad : RawIMonad M
      pop1   : ∀ {i} → M (i ∷ []) [] (S i)
      push1  : ∀ {i} → S i → M [] (i ∷ []) ⊤
      up    : ∀ {X is js} → M is js X → ∀ {ks} → M (is List.++ ks) (js List.++ ks) X
    open RawIMonad monad public
  
    pop : ∀ {i is} → M (i ∷ is) is (S i)
    pop = up pop1
  
    push : ∀ {i is} → S i → M is (i ∷ is) ⊤
    push = λ v → up (push1 v)
  
    pop-list : ∀ is → ∀ {is'} → M (is List.++ is') is' (IList S is) 
    pop-list [] = return []
    pop-list (i ∷ is) = do v ← pop
                           vs ← pop-list is
                           return (v ∷ vs)
  
    push-list : ∀ {is is'} → IList S is →  M is' (is List.++ is') ⊤
    push-list [] = return tt
    push-list (v ∷ vs) = do push-list vs
                            push v
  
    drop : ∀ {is} → (n : Fin (List.length is)) → M is (List.drop (toℕ n) is) ⊤
    drop {i ∷ is} zero = return tt
    drop {i ∷ is} (suc n) = do pop
                               drop {is} n
  
    pop-nth : ∀ {is} → (n : Fin (List.length is)) → M is (List.drop (ℕ.suc (toℕ n)) is) (S (List.lookup is n))
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
             do let vs , us = IList.split is ss
                x , ws ← f vs
                return (x , ws IList.++ us)
    } where open RawIMonad Mon
 
