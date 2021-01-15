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

data IList {a b} {I : Set a} (S : I → Set b) : List I → Set b where
  []  : IList S []
  _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

StackT : ∀ {a b} {I : Set a} → (I → Set b) → (Set b → Set b) → IFun (List I) b
StackT S M i j A = IList S i → M (A × IList S j)

-- ∀ {x} → ∀ {xs}
record RawIMonadStack {a b} {I : Set a} (S : I → Set b)
                      (M : IFun (List I) b) : Set (a ⊔ Level.suc b) where
  field
    monad : RawIMonad M
    pop : ∀ {i is} → M (i ∷ is) is (S i)
    push : ∀ {i is} → S i → M is (i ∷ is) (Lift b ⊤)
  open RawIMonad monad public

  drop-i : ∀ {is'} → ∀ is → M (is ++ is') is' (Lift b ⊤)
  drop-i [] = return (Level.lift tt)
  drop-i (i ∷ is) = pop >> drop-i is

  open import Data.Nat
  open import Data.List.Properties
  open import Relation.Binary.PropositionalEquality
  drop-n : ∀ {is} → ∀ n → M (take n is ++ drop n is) (drop n is) (Lift b ⊤)
  drop-n {is} n = drop-i {drop n is} (take n is)

StackTIMonad : ∀ {a b} {I : Set a} → ∀ (S : I → Set b) {M} → RawMonad M → RawIMonad (StackT S M)
StackTIMonad S Mon  = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  } where open RawMonad Mon

StackTIMonadStack : ∀ {a b} {I : Set a} (S : I → Set b) {M} →
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

val : valtype -> Set
val bool = Bool
val nat = ℕ

opds = IList val

[_*] : ∀ {a} → Set a → Set a
[_*] = List

resulttype = [ valtype *]
blkctxtype = resulttype × resulttype

blkctx : blkctxtype → Set
blkctx (t₁ , t₂) = opds t₁ → opds t₂

open import Function.Identity.Categorical as Id using (Identity)
OpdStack = StackT val Identity
open RawIMonadStack (StackTIMonadStack val Id.monad)

t : OpdStack [] [ bool ] (Lift Level.zero ⊤)
t = push true
