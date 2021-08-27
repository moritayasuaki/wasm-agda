module WasmDenotes (W : Set) (Store : Set) (Code : Set) where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Data.Maybe
open import Wasm
open import WasmTyping
open Syntax

OpeStk = List W
Cont = Store × OpeStk → Maybe (Store × OpeStk)
CtrlStk = List Cont

-- unsafe because it can contain stack underflow and branch to outside
Semantics = Code → CtrlStk → (Cont → Cont)

-- refinement on operand stack type by stack hegiht
OpeStkR : ℕ → Set
OpeStkR zero = ⊤
OpeStkR (suc n) = W × OpeStkR n

ContR : ℕ → ℕ → Set
ContR n r = Store × OpeStkR n → Maybe (Store × OpeStkR r) -- n states for number of operand stack the computation requires, r states for number of operand stack will be returned
CtrlStkR : List ℕ → ℕ → Set
CtrlStkR [] r = ContR r r -- r states for size of operands stack finally returns. ContR r r is for id continuation
CtrlStkR (n ∷ ls) r = ContR n r × CtrlStkR ls r

-- unsafe because it can contain branch to outside
SemanticsR : ℕ → ℕ → Set
SemanticsR a r = Code → CtrlStkR [] r  → (ContR r r → ContR a r) -- syntactically correct code must start with empty control stack

ContRR : ℕ → ℕ → ℕ → Set
ContRR n r l = Store × OpeStkR n → Maybe (Store × OpeStkR r) -- natural number l states there are no jump outside l
CtrlStkRR : (l : ℕ) → Vec ℕ l → ℕ → Set
CtrlStkRR zero [] r = ContR r r
CtrlStkRR (suc l) (n ∷ ls) r = ContR n r × CtrlStkRR l ls r

-- safe
SemanticsRR : ℕ → ℕ → Set
SemanticsRR a r = Code → CtrlStkRR zero [] r → (ContRR r r zero → ContRR a r zero)

SemanticsRR = (is : insns) (arg res : valuetype) → (is :~ arg ⇒ res) → CtrlStkRR zero [] r → (ContRR r r zero → ContRR a r zero)
