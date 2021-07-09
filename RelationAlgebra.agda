module RelationAlgebra where

open import Level
open import Function
open import Data.Nat as Nat using (ℕ)
open import Data.Product
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import Relation.Binary.Lattice
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra



module _ where
  private
    variable
      a b ℓ₁ ℓ₂  : Level
      X : Set a
      Y : Set b
      _≈_ : Rel X ℓ₁
      _≲_ : Rel X ℓ₂

  IsOmegaChain : {X : Set a} → Rel X ℓ₁ → Rel X ℓ₂ → (ℕ → X) → Set (ℓ₁ ⊔ ℓ₂)
  IsOmegaChain _≈_ _≲_ c = IsOrderHomomorphism (_≡_ {A = ℕ}) _≈_ Nat._≤_ _≲_ c

  record IsNoetherian {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (c : ℕ → X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isOmegaChain : IsOmegaChain _≈_ _≲_ c 
      height : ℕ
      stabilize : (i : ℕ) → (height Nat.≤ i) → c i ≈ c (ℕ.suc i)

  record IsOmegaChainCompletePartialOrder {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isPartialOrder : IsPartialOrder _≈_ _≲_
      isOmegaChainComplete : (c : ℕ → X) → IsNoetherian _≈_ _≲_ c
    open IsPartialOrder isPartialOrder public

  record IsOmegaChainCompletePointedPartialOrder {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (⊥ : X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isOmegaChainCompletePartialOrder : IsOmegaChainCompletePartialOrder _≈_ _≲_ 
      minimum : (x : X) → ⊥ ≲ x
    open IsOmegaChainCompletePartialOrder isOmegaChainCompletePartialOrder public

  record IsOmegaChainCompleteBoundedJoinSemilattice {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (_∨_ : X → X → X) (⊥ : X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isOmegaChainComplete : (c : ℕ → X) → IsNoetherian _≈_ _≲_ c
      isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≲_ _∨_ ⊥
    open IsBoundedJoinSemilattice isBoundedJoinSemilattice public

  IsFixedPoint : Rel X ℓ₁ → (X → X) → X → Set _
  IsFixedPoint _≈_ f x = f x ≈ x

  record IsLeastFixedPoint {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (f : X → X) (p : X) : Set (Level.suc (a ⊔ ℓ₁ ⊔ ℓ₂))  where
    field
      isFixedPoint : IsFixedPoint _≈_ f p
      least : (x : X) → IsFixedPoint _≈_ f x → p ≲ x

  iter : (X → X) → ℕ → X → X
  iter f Nat.zero = id
  iter f (Nat.suc n) = f ∘ iter f n

  iter-mono : (f : X → X) → (IsOrderHomomorphism _≈_ _≈_ _≲_ _≲_ f) →
    (n : ℕ) → (x y : X) → (x ≲ y) → iter f n x ≲ iter f n y
  iter-mono f fIsMonotone (Nat.zero) x y p = p
  iter-mono f fIsMonotone (Nat.suc n) x y p = fIsMonotone .mono (iter-mono f fIsMonotone n x y p) where
    open IsOrderHomomorphism
  iter-fixed : (f : X → X) → (IsEquivalence _≈_) → (IsRelHomomorphism _≈_ _≈_ f) →
    (n : ℕ) → (x : X) → IsFixedPoint _≈_ f x → iter f n x ≈ x
  iter-fixed f ≈-is-equiv _ Nat.zero _ _ = refl where
    open IsEquivalence ≈-is-equiv
  iter-fixed f ≈-is-equiv ≈-is-closed-under-f (Nat.suc n) x fx≈x = trans (cong fⁿx≈x) fx≈x where
    open IsRelHomomorphism ≈-is-closed-under-f
    open IsEquivalence ≈-is-equiv
    fⁿx≈x = iter-fixed f ≈-is-equiv ≈-is-closed-under-f n x fx≈x

record OmegaChainCompletePartialOrder c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    isOmegaChainCompletePartialOrder : IsOmegaChainCompletePartialOrder _≈_ _≲_

  infix 4 _≈_ _≲_

  open IsOmegaChainCompletePartialOrder isOmegaChainCompletePartialOrder public

record OmegaChainCompletePointedPartialOrder c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    ⊥       : Carrier
    isOmegaChainCompletePointedPartialOrder : IsOmegaChainCompletePointedPartialOrder _≈_ _≲_ ⊥

  infix 4 _≈_ _≲_

  open IsOmegaChainCompletePointedPartialOrder isOmegaChainCompletePointedPartialOrder public

record OmegaChainCompleteBoundedJoinSemilattice c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    _∨_     : Op₂ Carrier
    ⊥       : Carrier
    isOmegaChainCompleteBoundedJoinSemilattice : IsOmegaChainCompleteBoundedJoinSemilattice _≈_ _≲_ _∨_ ⊥

  infix 4 _≈_ _≲_
  infixr 7 _∨_

  open IsOmegaChainCompleteBoundedJoinSemilattice isOmegaChainCompleteBoundedJoinSemilattice public

 
module _ where
  private
    variable
      a ℓ₁ ℓ₂ : Level
      X : Set a
      _≈_ : Rel X ℓ₁ 
      _≲_ : Rel X ℓ₂
      ⊥ : X

  open IsLeastFixedPoint
  open IsNoetherian
  open IsOrderHomomorphism
  open IsOmegaChainCompletePointedPartialOrder
  lfp : IsOmegaChainCompletePointedPartialOrder _≈_ _≲_ ⊥ → (f : X → X) → IsOrderHomomorphism _≈_ _≈_ _≲_ _≲_ f → Σ X (IsLeastFixedPoint _≈_ _≲_ f)
  lfp {_≈_ = _≈_} {_≲_ = _≲_} {⊥ = ⊥} isCPPO f fIsMonotone = (p , isLFP) where
    s = flip (iter f) ⊥
    sIsNoetherian : IsNoetherian _≈_ _≲_ s
    sIsNoetherian .isOmegaChain = sIsOmegaChain where
      sIsOmegaChain : IsOmegaChain _≈_ _≲_ s
      sIsOmegaChain .mono {y = m} Nat.z≤n = isCPPO .minimum (s m)
      sIsOmegaChain .mono (Nat.s≤s r) = fIsMonotone .mono (sIsOmegaChain .mono r)
      sIsOmegaChain .cong _≡_.refl =  isCPPO .isEquivalence .IsEquivalence.refl

    sIsNoetherian .height =  (isCPPO .isOmegaChainComplete s) .height 
    sIsNoetherian .stabilize =  (isCPPO .isOmegaChainComplete s) .stabilize 
    p = s (sIsNoetherian . height)
    isLFP : IsLeastFixedPoint _≈_ _≲_ f p
    isLFP .isFixedPoint =  isCPPO .isEquivalence .IsEquivalence.sym ((sIsNoetherian .stabilize) (sIsNoetherian .height) ≤-refl) where
      open import Data.Nat.Properties
    isLFP .least x fx≈x = fⁿ⊥≲x where
      fⁿ⊥≲fⁿx = iter-mono f fIsMonotone (sIsNoetherian .height) ⊥ x (isCPPO .minimum x)
      fⁿx≈x = iter-fixed f (isCPPO .isEquivalence) (Eq.isRelHomomorphism fIsMonotone) (sIsNoetherian .height) x fx≈x
      fⁿ⊥≲x = isCPPO .trans  fⁿ⊥≲fⁿx (isCPPO .reflexive fⁿx≈x) 

module _ where
  private
    variable
      a b ℓ₁ ℓ₂ : Level
      A : Set a
      B : Set b

  _×ᴿ_ : Rel A ℓ₁ → Rel B ℓ₂ → Rel (A × B) (ℓ₁ ⊔ ℓ₂)
  (R ×ᴿ Q) (a , b) (a' , b') = R a a' × Q b b'

  _→ᴿ_ : {a : Level} → {A : Set a} → Rel A ℓ₁ → Rel B ℓ₂ → Rel (A → B) (a ⊔ ℓ₁ ⊔ ℓ₂)
  _→ᴿ_ {a = a} {A = A} R Q f f' = (x x' : A) → R x x' → Q (f x) (f' x')

