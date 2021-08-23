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

  data Stmts (Label : Set) (Var : Set) : Set where
    _∷_ : Stmt Var → Stmts Label Var → Stmts Label Var
    goto : Label → Stmts Label Var
    gotoif : Var → Label → Label → Stmts Label Var
    ret : Var → Stmts Label Var

  Store : Set → Set
  Store Var = Integer.ℤ

  Code : Set → Set → Set
  Code Label Var = Label → Stmts Label Var

  Config : Set → Set → Set
  Config Label Var = Code Label Var × Stmts Label Var × Store Var

  open import Monad