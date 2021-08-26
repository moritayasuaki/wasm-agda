module HPomonad where

open import HMonad
open import Order

private
  variable
    i j k : Level
    A B C : Set i

PointwiseOrder : {i a : Level} {I : Set i} → IFun I a → (ℓ ℓ' : Level) → Set _
PointwiseOrder {a = a} {I = I} M ℓ ℓ' = (i j : I) → (A : Set a) → Poset (M i j A) ℓ ℓ'

record HPomonad (M : Set i → Set j) : Set (suc (i ⊔ j)) where
  field
    hMonad : HMonad M
    PwRawPoset : PwRawPoset M ℓ ℓ'
  open RawIMonad rawIMonad

  fwRawPoset : (i j : I) → (A B : Set a) → RawPoset (A → (M i j B)) (a ⊔ ℓ) (a ⊔ ℓ')
  fwRawPoset i j A B = funextPoset A (pwRawPoset i j B)

  field
    pwBimonotone : ∀{i j k} {A B C : Set a} → IsBimonotone (fwRawPoset i j A B) (fwRawPoset j k B C) (fwRawPoset i k A C) _>=>_

