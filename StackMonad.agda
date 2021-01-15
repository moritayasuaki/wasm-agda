module StackMonad where

open import Data.Fin
open import Category.Monad.Indexed
open import Category.Monad
open import Category.Applicative.Indexed
open import Data.List
open import Function
open import Level
open import Data.Unit
open import Data.Product

data IList {I : Set} (S : I → Set) : List I → Set where
  []  : IList S []
  _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

StackT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
StackT S M i j A = IList S i → M (A × IList S j)

-- ∀ {x} → ∀ {xs}
record RawIMonadStack {I : Set} (S : I → Set)
                      (M : List I → List I → Set → Set) : Set₁ where
  field
    monad : RawIMonad M
    pop : ∀ {i is} → M (i ∷ is) is (S i)
    push : ∀ {i is} → S i → M is (i ∷ is) ⊤
  open RawIMonad monad public

  drop-i : ∀ {is'} → ∀ is → M (is ++ is') is' ⊤
  drop-i [] = return tt
  drop-i (i ∷ is) = pop >> drop-i is

  open import Data.Nat
  open import Data.List.Properties
  open import Relation.Binary.PropositionalEquality
  drop-n : ∀ {is} → ∀ n → M (take n is ++ drop n is) (drop n is) ⊤
  drop-n {is} n = drop-i {drop n is} (take n is)

StackTIMonad : {I : Set} → ∀ (S : I → Set) {M} → RawMonad M → RawIMonad (StackT S M)
StackTIMonad S Mon  = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  } where open RawMonad Mon

StackTIMonadStack : {I : Set} (S : I → Set) {M : Set → Set} →
                    RawMonad M → RawIMonadStack S (StackT S M)
StackTIMonadStack S Mon = record
  { monad = StackTIMonad S Mon
  ; pop = λ where (s ∷ ss) → return (s , ss)
  ; push = λ s ss → return (_ , s ∷ ss)
  } where open RawIMonad Mon

open import Data.Bool
open import Data.Nat

data valtype : Set where
  bool : valtype
  nat : valtype
  unit : valtype

val : valtype -> Set
val bool = Bool
val nat = ℕ
val unit = ⊤

opds = IList val

resulttype = List valtype 

blkctxtype = resulttype × resulttype

blkctx : blkctxtype → Set
blkctx (t₁ , t₂) = opds t₁ → opds t₂

ctrlstacktype = List blkctxtype

open import Function.Identity.Categorical as Id using (Identity)
OpdStack = StackT val Identity
module OpdM = RawIMonadStack (StackTIMonadStack val Id.monad)

CtrlStack = StackT blkctx Identity
module CtrlM = RawIMonadStack (StackTIMonadStack blkctx Id.monad)

andb : OpdStack (bool ∷ bool ∷ []) [ bool ] ⊤
andb = do b ← pop
          b ← pop
          push (b ∧ b)
          where open OpdM

popb : OpdStack (bool ∷ bool ∷ []) [ bool ] ⊤
popb = do b ← pop
          return tt
          where open OpdM

br0 : {s e : resulttype} → CtrlStack ((s , e) ∷ []) [] (opds s → opds e)
br0 = pop
      where open CtrlM

