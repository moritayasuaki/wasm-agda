module HPomonad where

open import Level
open import HeteroMonad
open import BiRel
private
  variable
    i j k l : Level

-- j is level of space of logic. it is used for relation (order and equivalence) and predicate
record HPomonad (M : Set i → Set j) : Set (suc (i ⊔ j)) where
  field
    hMonad : HMonad M
    hasPointwiseOrder : HasPointwiseOrder M j
  open HMonad hMonad

  F : Set i → Set i → Set (i ⊔ j)
  F A B = A → M B

  hasPairwiseOrder : HasPairwiseOrder F (i ⊔ j)
  hasPairwiseOrder A B = (FunExt.hasOrderT A j (M B)) (hasPointwiseOrder B)

  field
    >=>-isBimonotone : {A B C : Set i} → IsBimonotone (hasPairwiseOrder A B) (hasPairwiseOrder B C) (hasPairwiseOrder A C) _>=>_

HPomonadT : ((Set i → Set j) → (Set k → Set l)) → Set (suc (i ⊔ j ⊔ k ⊔ l))
HPomonadT T = ∀{M} → HPomonad M → HPomonad (T M)

enrichTriv : {M : Set i → Set j} → HMonad M → HPomonad M
enrichTriv HMon = let open HMonad HMon in record 
  { hMonad = HMon
  ; hasPointwiseOrder = λ A → record
    { E = _≡_
    ; O = _≡_
    }
  ; >=>-isBimonotone = record
    { cong₂ = λ {f} {f'} {g} {g'} f'' g'' x → {!   !}
    ; mono₂ = λ {f} {f'} {g} {g'} f'' g'' x → {!   !}
    }
  } where open import Relation.Binary.PropositionalEquality using (_≡_) renaming  (cong to ≡-cong ; cong₂ to ≡-cong₂ ; refl to ≡-refl)
          open import Function

