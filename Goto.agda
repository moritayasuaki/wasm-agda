{-# OPTIONS --guardedness #-}

module Goto where

import Category.Monad.Indexed
import Category.Monad
import Category.Applicative.Indexed
import Function
import Level
import Data.Fin as Fin

import Data.Unit as Unit
import Data.Product as Product
import Data.Sum as Sum


import Data.Nat as Nat
import Data.Vec as Vec
import Data.List as List
import Data.Bool as Bool
import Data.Empty as Empty
import Data.String as String
import Data.Maybe as Maybe
import Data.Integer as Integer
import Category.Monad.State using (IStateT ; StateTIMonad)
import Category.Monad.Continuation using (DContT ; DContIMonad)

import Relation.Binary
import Relation.Binary.PropositionalEquality as PropositionalEquality
import Relation.Nullary.Decidable as Decidable



module Syntax where
  open Product
  open Integer using (ℤ)
  open Nat using (ℕ)
  data Ops (Var : Set) : Set where
    const : Integer.ℤ → Ops Var
    load : Var → Ops Var
    add : Var → Var → Ops Var
    mul : Var → Var → Ops Var
    and : Var → Var → Ops Var
    not : Var → Ops Var
  data Stmt (Var : Set) : Set where
    nop : Stmt Var
    assign : Var → Ops Var → Stmt Var

  data Label (n : ℕ) : Set where
    label : (m : ℕ) → (m Nat.≤ n) → Label n

  start : (n : ℕ) → Label n
  start n = label 0 Nat.z≤n

  data Stmts (Label : Set) (Var : Set) : Set where
    _∷_ : Stmt Var → Stmts Label Var → Stmts Label Var
    goto : Label → Stmts Label Var
    gotoif : Var → Label → Label → Stmts Label Var
    ret : Var → Stmts Label Var

  Store : Set → Set
  Store Var = Var → ℤ

  Code : Set → Set → Set
  Code Label Var = Label → Stmts Label Var

  Config : Set → Set → Set
  Config Label Var = Code Label Var × Stmts Label Var × Store Var

  open import DelayMonad
  open import Category.Monad.State
  open import Data.Sum
  open import Function

  small-step : {Label : Set} → {Var : Set} → Config Label Var → (Config Label Var) ⊎ (ℤ × Store Var)
  small-step (c , i ∷ is , s) = inj₁ (c , is , s) -- TODO define net effects for each i
  small-step (c , goto ℓ , s) = inj₁ (c , c ℓ , s)
  small-step (c , gotoif x ℓ ℓ' , s) = s x |> λ where
    Integer.+0 → inj₁ (c , goto ℓ , s)
    _ → inj₁ (c , goto ℓ' , s)
  small-step (c , ret x , s) = inj₂ (s x , s)

  open import Category.Monad.Partiality
  open import Codata.Musical.Notation

  ⟦_⟧ : (n : ℕ) → (Var : Set) → Code (Label n) Var → StateT (Store Var) _⊥ ℤ 
  ⟦_⟧ n Var c s = go (inj₁ (c , (c (start n)) , s)) where
    go : (Config (Label n) Var) ⊎ (ℤ × Store Var) → (ℤ × Store Var) ⊥
    go (inj₁ x) =  later (♯ go (small-step x))
    go (inj₂ x) = now x
