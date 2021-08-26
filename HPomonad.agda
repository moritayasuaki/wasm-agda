module HPomonad where

open import Level
open import HMonad
open import Order

-- j is level of space of logic. it is used for relation (order and equivalence) and predicate
record HPomonad {i j : Level} (M : Set i → Set j) : Set (suc (i ⊔ j)) where
  field
    hMonad : HMonad M
    hasPointwiseOrder : HasPointwiseOrder M j
  open HMonad.HMonad hMonad

  F : Set i → Set i → Set (i ⊔ j)
  F A B = A → M B

  hasPairwiseOrder : HasPairwiseOrder F (i ⊔ j)
  hasPairwiseOrder A B = funextOrder A (hasPointwiseOrder B)

  field
    isBimonotone : {A B C : Set i} → IsBimonotone (hasPairwiseOrder A B) (hasPairwiseOrder B C) (hasPairwiseOrder A C) _>=>_

private
  variable
    i j k l : Level

HPomonadT : ((Set i → Set j) → (Set k → Set l)) → Set (suc (i ⊔ j ⊔ k ⊔ l))
HPomonadT T = ∀{M} → HPomonad M → HPomonad (T M)

open import Category.Monad

lift2 : (T : (Set i → Set i) → (Set i → Set i)) → RawMonadT T → HPomonadT T
lift2 T MT record 
  { hMonad = record
    { return = return
    ; _>>=_ = _>>=_
    }
  ; hasPointwiseOrder = hasPointwiseOrder
  ; isBimonotone = isBimonotone
  } with MT (record { return = return ; _>>=_ = _>>=_})
... | record { return = return' ; _>>=_ = _>>='_ } = record
  { hMonad = record 
    { return = return'
    ; _>>=_ = _>>='_
    }
  ; hasPointwiseOrder = λ A → {!  hasPointwiseOrder A  !}
  ; isBimonotone = {!   !}
  }