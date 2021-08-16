{-# OPTIONS --safe --guardedness #-}
module Monad where

import Category.Monad.Indexed
import Category.Monad
import Category.Monad.Predicate
import Category.Applicative.Indexed
import Category.Functor
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
import Relation.Binary.PropositionalEquality
import Relation.Binary
import Relation.Unary

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
 

open Category.Monad
open Category.Monad.Indexed

record ∞Delay (A : Set) : Set
data Delay (A : Set) : Set

data Delay A where
  now : A → Delay A
  later : ∞Delay A → Delay A

record ∞Delay A where
  constructor thunk
  coinductive
  field
    force : Delay A

module _ where 
  open Category.Monad.Indexed.RawIMonad
  
  monadDelay : RawMonad Delay
  monad∞Delay : RawMonad ∞Delay

  return monadDelay x = now x
  _>>=_ monadDelay x f = later (_>>=_ monad∞Delay (thunk x)  λ x → thunk (f x)) 

  return monad∞Delay x = record { force = now x }
  ∞Delay.force ((monad∞Delay >>= x) f) = _>>=_ monadDelay (later x) λ x → later (f x)



module _ where 

open Level
open Relation.Binary.PropositionalEquality
open Product
open Sum
open Unit
open Category.Functor using (RawFunctor)

record RawGApplicative {i j : Level} (F : Set i → Set j) : Set (suc i ⊔ suc j) where
  field
    pure : {A : Set i} → A → F A
    _⊛_ : {A B : Set i} → F (A → B) → F A → F B

  rawFunctor : RawFunctor F
  rawFunctor = record
    { _<$>_ = λ g x → pure g ⊛ x
    }

  private
    open module RF = RawFunctor rawFunctor public

record RawGMonad {i j : Level} (M : Set i → Set j) : Set (suc i ⊔ suc j) where
  field
    return : {A : Set i} → A → M A
    _>>=_ : {A B : Set i} → M A → (A → M B) → M B

  rawGApplicative : RawGApplicative M
  rawGApplicative = record
    { pure = return
    ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
    }

  open RawGApplicative rawGApplicative public

open Relation.Binary

record RawGPomonad {i j k} (M : Set i → Set j) (_≈_ : ∀{A} → Rel (M A) k) (_≲_ : ∀{A} → Rel (M A) k) : Set (suc i ⊔ suc j ⊔ k) where
  field
    rawGMonad : RawGMonad M
    isPartialOrder : ∀{A} → IsPartialOrder (_≈_ {A}) (_≲_ {A})
  open IsPartialOrder public

open Relation.Unary renaming (Pred to Pred')

Pred : ∀{a b} → Set a → Set (a ⊔ suc b)
Pred {_} {b} A = Pred' A b -- A -> P

Forward : ∀{a b} → Set a → Set (a ⊔ suc b)
Forward {a} {b} A = Pred {a ⊔ suc b} {b} (Set b × A) -- (P × A) → P

Backward : ∀{a b} → Set a → Set (a ⊔ suc b)
Backward {a} {b} A = Pred {a ⊔ suc b} {b} (Pred {a} {b} A) -- (A → P) → P

Bidirectional : ∀{a b} → Set a → Set (a ⊔ suc b)
Bidirectional {a} {b} A = Pred {a ⊔ suc b} {b} (Set b × (Pred {a} {b} A)) -- (P × (A → P)) → P

-- bind x f = join (f <$>_) (return x)
-- U ( ) ({x})



module _ where

  open Relation.Unary renaming (Pred to Pred')
  open Relation.Binary.PropositionalEquality
  open Function
  _≐_ : ∀{a b A} → Pred {a} {b} A → Pred {a} {b} A → Set _
  P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

  ≐-isEquivalence : ∀{a b A} →  IsEquivalence {A = Pred {a} {b} A} _≐_
  ≐-isEquivalence = record
    { refl =  (id , id)
    ; sym = Product.swap
    ; trans = λ (p , q) (r , s) → (r ∘ p , q ∘ s)
    }

  ⊆-isPartialOrder : ∀{a b A} → IsPartialOrder {A = Pred {a} {b} A}_≐_ _⊆_
  ⊆-isPartialOrder = record
    { isPreorder = record
        { isEquivalence = ≐-isEquivalence
        ; reflexive = proj₁
        ; trans = λ p q → q ∘ p
        }
    ; antisym = (_,_) 
    }

  powersetMonad : ∀{i} → RawGPomonad (Pred {i} {i}) _≐_ _⊆_
  powersetMonad = record
    { rawGMonad = record
        { return = _≡_
        ; _>>=_ = λ m f b → ∃ λ a → m a × f a b
        }
    ; isPartialOrder = ⊆-isPartialOrder
    }

  contraPowersetMonad : ∀{i} → RawGPomonad (Pred {i} {i}) _≐_ _⊆_
  contraPowersetMonad = record
    { rawGMonad = record
        { return = _≡_
        ; _>>=_ = λ m f b → ∀ a → m a → f a b
        }
    ; isPartialOrder = ⊆-isPartialOrder
    }

  forwardMonad : ∀{i} → RawGPomonad (Forward {i} {i}) _≐_ _⊆_
  forwardMonad {i} = record
    { rawGMonad = record -- a -> (pre × a)
        { return = λ a → λ {(p , a') → p × a' ≡ a}
        ; _>>=_ = λ m f → λ {(p , b) → ∀ a → m (p , a) → f a (p , b)}
        }
    ; isPartialOrder = ⊆-isPartialOrder
    }

  backwardMonad : ∀{i} → RawGPomonad (Backward {i} {i}) _≐_ _⊆_
  backwardMonad {i} = record
    { rawGMonad = record
        { return = λ a k → k a
        ; _>>=_ = λ c f k → c (flip f k)
        }
    ; isPartialOrder = ⊆-isPartialOrder
    }

  bidirectionalMonad : ∀{i} → RawGPomonad (Bidirectional {i} {i}) _≐_ _⊆_
  bidirectionalMonad = record
    { rawGMonad = record
        { return = λ a → λ{ (p , k) → k a × p}
        ; _>>=_ = λ c f → λ{ (p , k) → c (p , flip f ((p , k)))}
        }
    ; isPartialOrder = ⊆-isPartialOrder
    }