open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Morphism
-- open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Category.Functor using (RawFunctor)
open import Function

private
  variable
    i j k : Level
    A : Set i

open import Relation.Unary hiding (∅ ; U)

record True (j : Level): Set j where
  constructor tt

data False (j : Level): Set j where

∅ : {j : Level} → Pred A j
∅ {j = j} = λ _ → False j
U : {j : Level} → Pred A j
U {j = j} = λ _ → True j

-- Logical equivalence
_≐_ : Pred A j → Pred A k → Set _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)


≐-isEquivalence : IsEquivalence {A = Pred A j} _≐_
≐-isEquivalence = record
  { refl =  (id , id)
  ; sym = Data.Product.swap
  ; trans = λ (p , q) (r , s) → (r ∘ p , q ∘ s)
  }



⊆-isPreorder : IsPreorder {A = Pred A j} _≐_ _⊆_
⊆-isPreorder = record
  { isEquivalence = ≐-isEquivalence
  ; reflexive = proj₁
  ; trans = λ p q → q ∘ p
  }

⊆-isPartialOrder : IsPartialOrder {A = Pred A j} _≐_ _⊆_
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym = (_,_) 
  }

open import Relation.Binary.Lattice
∪-isJoinSemilattice : IsJoinSemilattice {A = Pred A j} _≐_ _⊆_ _∪_
∪-isJoinSemilattice = record
  { isPartialOrder = ⊆-isPartialOrder
  ; supremum = λ _ _ → ( inj₁ , inj₂ , λ R PinR QinR → (λ {(inj₁ Px) → PinR Px ; (inj₂ Qx) → QinR Qx }))
  }


∩-isMeetSemilattice : IsMeetSemilattice {A = Pred A j} _≐_ _⊆_ _∩_
∩-isMeetSemilattice = record
  { isPartialOrder = ⊆-isPartialOrder
  ; infimum = λ _ _ → (  proj₁ ,  proj₂ , λ _ RinP RinQ Rx → ( RinP Rx , RinQ Rx ))
  }

PredIsLattice : IsLattice {A = Pred A j} _≐_ _⊆_ _∪_ _∩_
PredIsLattice = record
  { isPartialOrder = ⊆-isPartialOrder
  ; supremum = λ _ _ → ( inj₁ , inj₂ , λ R PinR QinR → (λ {(inj₁ Px) → PinR Px ; (inj₂ Qx) → QinR Qx }))
  ; infimum = λ _ _ → (  proj₁ ,  proj₂ , λ _ RinP RinQ Rx → ( RinP Rx , RinQ Rx ))
  }

PredIsBoundedLattice : IsBoundedLattice {A = Pred A j} _≐_ _⊆_ _∪_ _∩_ U ∅
PredIsBoundedLattice = record
  { isLattice = PredIsLattice
  ; maximum = λ _ _ → tt
  ; minimum = λ _ → λ ()
  }

PredIsHeytingAlgebra : IsHeytingAlgebra {A = Pred A j} _≐_ _⊆_ _∪_ _∩_ _⇒_ U ∅
PredIsHeytingAlgebra = record
  { isBoundedLattice = PredIsBoundedLattice
  ; exponential = λ _ _ _ → ( (λ W∧P<Q → λ Wx Px → W∧P<Q (Wx , Px)) , λ W<P^Q → λ (Wx , Px) → W<P^Q Wx Px )
  }

