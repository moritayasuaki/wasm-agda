module Trace where

open import Data.Nat
open import Relation.Binary
open import Data.Product 
open import Level
open import Function
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.Morphism
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (cong to ≡-cong)
open import Category.Monad
open import Category.Monad.Indexed
open import Category.Applicative.Indexed

private
  variable
    a b c i f g h : Level
    A : Set a
    B : Set b
    C : Set c
    I : Set i

open import HetroPomonad
open import Category.Monad.Reader

-- TraceT M A = ℕ → M A, where a parameter of natural number states transition counter 
TraceT : (Set f → Set f) → Set f → Set f
TraceT {f = f} = ReaderT ℕ f

-- ChainTraceT M A = {f : ℕ → M A | f is a isotonic function } 
ChainTraceT : ∀{g h} → (M : Set f → Set f) → FRel {f} M g → FRel {f} M h → Set f → Set _
ChainTraceT M E O A = ∃ (IsOrderHomomorphism _≡_ (E A) _≤_ (O A))

TraceTMonad : ∀{f M} → RawMonad M → RawMonad (TraceT M)
TraceTMonad {f = f} Mon = ReaderTMonad ℕ f Mon

module _ where
  open RawOIMonad
  open IsOrderHomomorphism
  TraceTOMonad : ∀{M E O} → RawOMonad {g = g} {h = h} M E O
   → RawOMonad (TraceT M) (ObjectwiseRelFunExt ℕ E) (ObjectwiseRelFunExt ℕ O) -- the order relation is extended by objectwise (Types) and pointwise (on natural number ℕ).
  TraceTOMonad record
    { monad = monad
    ; isPreorder = isPreorder
    ; isOrderHomomorphismL = isOrderHomomorphismL
    ; isOrderHomomorphismR = isOrderHomomorphismR
    } = record
    { monad = TraceTMonad monad
    ; isPreorder = λ i j A → RelFunExt-preservePreorder (isPreorder i j A)
    ; isOrderHomomorphismL = λ i j k A B m → record 
      { cong = λ f n → cong (isOrderHomomorphismL i j k A B (flip m n)) (f n)
      ; mono = λ f n → mono (isOrderHomomorphismL i j k A B (flip m n)) (f n)
      }
    ; isOrderHomomorphismR = λ i j k A B m → record 
      { cong = λ f n → cong (isOrderHomomorphismR i j k A B (m n)) (flip f n)
      ; mono = λ f n → mono (isOrderHomomorphismR i j k A B (m n)) (flip f n)
      }
    }


iter : {A : Set f} → (A → A) → ℕ → A → A
iter f ℕ.zero a = a 
iter f (ℕ.suc n) a = f (iter f n a)

transitionToOTrace : ∀{f g h} {M : Set f → Set f} {E : FRel M h} {O : FRel M g} {A : Set f}
  → RawOMonad M E O
  → (t : M A → M A) → IsExterierOperator (O A) t → M A -- We require small-step transition functions t satisfies m ≤ t m and m ≤ m' ⇒ t m ≤ t m'
  → OTraceT M E O A
transitionToOTrace {M = M} {E = E} {O = O} {A = A} Mon t Ext ma = (trace , record {cong = pcong ; mono = pmono}) where
  open RawOMonad Mon
  module O-Pre = IsPreorder (isPreorder _ _ A)
  module E-Eqv = IsEquivalence (O-Pre.isEquivalence)
  module t-Ext = IsExterierOperator Ext
  trace = flip (iter t) ma
  pmono : Homomorphic₂ ℕ (M A) _≤_ (O A) trace
  pmono {y = ℕ.zero} z≤n = O-Pre.refl
  pmono {y = ℕ.suc n} z≤n = O-Pre.trans (pmono {y = n} z≤n) (t-Ext.isExtensive (iter t n ma))
  pmono (s≤s r) = t-Ext.cong (pmono r)
  pcong : Homomorphic₂ ℕ (M A) _≡_ (E A) trace
  pcong _≡_.refl = E-Eqv.refl
