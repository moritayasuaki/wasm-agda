module CPPO where
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
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; [_]) renaming (subst₂ to ≡-subst₂ ; cong₂ to ≡-cong₂ ; cong to ≡-cong ; refl to ≡-refl ; subst to ≡-subst ; sym to ≡-sym)
open import Algebra

module _ where
  private
    variable
      a b ℓ₁ ℓ₂  : Level
      X : Set a
      Y : Set b
      _≈_ : Rel X ℓ₁
      _≲_ : Rel X ℓ₂

  IsEndoOrderHomomorphism : {X : Set a} → Rel X ℓ₁ → Rel X ℓ₂ → (X → X) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsEndoOrderHomomorphism _≈_ _≲_ step = IsOrderHomomorphism _≈_ _≈_ _≲_ _≲_ step

  Bihomomorphic : ∀{a b c ar br cr} → {A : Set a} → {B : Set b} → {C : Set c} → Rel A ar → Rel B br → Rel C cr → (A → B → C) → Set _
  Bihomomorphic {A = A} {B = B} {C = C} RA RB RC f = (a1 a2 : A) → (b1 b2 : B) → (RA a1 a2) → (RB b1 b2) → (RC (f a1 b1) (f a2 b2))

  IsIncreasing : {X : Set a} → Rel X ℓ₂ → (X → X) → Set (a ⊔ ℓ₂)
  IsIncreasing {X = X} _≲_ step = (x : X) → x ≲ step x

  IsωChain : {X : Set a} → Rel X ℓ₁ → Rel X ℓ₂ → (ℕ → X) → Set (ℓ₁ ⊔ ℓ₂)
  IsωChain _≈_ _≲_ c = IsOrderHomomorphism (_≡_ {A = ℕ}) _≈_ Nat._≤_ _≲_ c

  record IsNoetherian {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (c : ℕ → X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isωChain : IsωChain _≈_ _≲_ c 
      height : ℕ
      stabilize : (i : ℕ) → (height Nat.≤ i) → c i ≈ c (ℕ.suc i)

  record IsωChainCompletePartialOrder {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isPartialOrder : IsPartialOrder _≈_ _≲_
      isωChainComplete : (c : ℕ → X) → IsNoetherian _≈_ _≲_ c
    open IsPartialOrder isPartialOrder public

  record IsωChainCompletePointedPartialOrder {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (⊥ : X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isωChainCompletePartialOrder : IsωChainCompletePartialOrder _≈_ _≲_ 
      minimum : (x : X) → ⊥ ≲ x
    open IsωChainCompletePartialOrder isωChainCompletePartialOrder public

  record IsωChainCompleteBoundedJoinSemilattice {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (_∨_ : X → X → X) (⊥ : X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isωChainComplete : (c : ℕ → X) → IsNoetherian _≈_ _≲_ c
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

  iter-monotone : (f : X → X) → (IsEndoOrderHomomorphism _≈_ _≲_ f) →
    (n : ℕ) → (x y : X) → (x ≲ y) → iter f n x ≲ iter f n y
  iter-monotone f f-isMonotone (Nat.zero) x y p = p
  iter-monotone f f-isMonotone (Nat.suc n) x y p = f-isMonotone .mono (iter-monotone f f-isMonotone n x y p) where
    open IsOrderHomomorphism
  iter-fixed : (f : X → X) → (IsEquivalence _≈_) → (IsRelHomomorphism _≈_ _≈_ f) →
    (n : ℕ) → (x : X) → IsFixedPoint _≈_ f x → iter f n x ≈ x
  iter-fixed f ≈-is-equiv _ Nat.zero _ _ = refl where
    open IsEquivalence ≈-is-equiv
  iter-fixed f ≈-is-equiv ≈-is-closed-under-f (Nat.suc n) x fx≈x = trans (cong fⁿx≈x) fx≈x where
    open IsRelHomomorphism ≈-is-closed-under-f
    open IsEquivalence ≈-is-equiv
    fⁿx≈x = iter-fixed f ≈-is-equiv ≈-is-closed-under-f n x fx≈x

  iter-bimonotone  : (f : X → X) → (IsEndoOrderHomomorphism _≈_ _≲_ f) → (IsIncreasing _≲_ f) → (IsPreorder _≈_ _≲_) →
    ((iter f) Preserves₂ Nat._≤_ ⟶ _≲_ ⟶ _≲_)
  iter-bimonotone f monotone increasing preorder {y = Nat.zero} Nat.z≤n u≲v = u≲v
  iter-bimonotone f monotone increasing preorder {y = Nat.suc y} {v = v} Nat.z≤n u≲v =
    let t = iter-bimonotone f monotone increasing preorder {y = y} Nat.z≤n u≲v in
    let t' = increasing (iter f y v) in IsPreorder.trans preorder t t'
  iter-bimonotone f monotone increasing preorder (Nat.s≤s n≤m) u≲v =
    let t = iter-bimonotone f monotone increasing preorder n≤m u≲v in IsOrderHomomorphism.mono monotone t

  iter-bihomomorphic  : (f : X → X) → (IsEndoOrderHomomorphism _≈_ _≲_ f) → (IsIncreasing _≲_ f) → (IsPreorder _≈_ _≲_) → Bihomomorphic Nat._≤_ _≲_ _≲_ (iter f)
  iter-bihomomorphic f monotone increasing preorder .0 Nat.zero x y Nat.z≤n x≲y = x≲y
  iter-bihomomorphic f monotone increasing preorder .0 (Nat.suc n) x y Nat.z≤n x≲y =
    let t = iter-bihomomorphic f monotone increasing preorder 0 n x y Nat.z≤n x≲y in
    let t' = increasing (iter f n y) in IsPreorder.trans preorder t t' 
  iter-bihomomorphic f monotone increasing preorder (Nat.suc n) (Nat.suc m) x y (Nat.s≤s n≤m) x≲y =
    let t = iter-bihomomorphic f monotone increasing preorder n m x y n≤m x≲y in IsOrderHomomorphism.mono monotone t

  module _ {a b c a' b' c' : Level} {A : Set a} {B : Set b} {C : Set c}
           (RA : Rel A a') (RB : Rel B b') (RC : Rel C c')
           (tRA : Transitive RA) (tRB : Transitive RB) (tRC : Transitive RC)
           (f : A → B → C) (f-bi : Bihomomorphic RA RB RC f) where

record ωChainCompletePartialOrder c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    isωChainCompletePartialOrder : IsωChainCompletePartialOrder _≈_ _≲_

  infix 4 _≈_ _≲_

  open IsωChainCompletePartialOrder isωChainCompletePartialOrder public

record ωChainCompletePointedPartialOrder c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    ⊥       : Carrier
    isωChainCompletePointedPartialOrder : IsωChainCompletePointedPartialOrder _≈_ _≲_ ⊥

  infix 4 _≈_ _≲_

  open IsωChainCompletePointedPartialOrder isωChainCompletePointedPartialOrder public

record ωChainCompleteBoundedJoinSemilattice c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    _∨_     : Op₂ Carrier
    ⊥       : Carrier
    isωChainCompleteBoundedJoinSemilattice : IsωChainCompleteBoundedJoinSemilattice _≈_ _≲_ _∨_ ⊥

  infix 4 _≈_ _≲_
  infixr 7 _∨_

  open IsωChainCompleteBoundedJoinSemilattice isωChainCompleteBoundedJoinSemilattice public

 
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
  open IsωChainCompletePointedPartialOrder
  lfp : IsωChainCompletePointedPartialOrder _≈_ _≲_ ⊥ → (f : X → X) → IsEndoOrderHomomorphism _≈_ _≲_ f → Σ X (IsLeastFixedPoint _≈_ _≲_ f)
  lfp {_≈_ = _≈_} {_≲_ = _≲_} {⊥ = ⊥} isCPPO f fIsMonotone = (p , isLFP) where
    s = flip (iter f) ⊥
    sIsNoetherian : IsNoetherian _≈_ _≲_ s
    sIsNoetherian .isωChain = sIsωChain where
      sIsωChain : IsωChain _≈_ _≲_ s
      sIsωChain .mono {y = m} Nat.z≤n = isCPPO .minimum (s m)
      sIsωChain .mono (Nat.s≤s r) = fIsMonotone .mono (sIsωChain .mono r)
      sIsωChain .cong _≡_.refl =  isCPPO .isEquivalence .IsEquivalence.refl

    sIsNoetherian .height =  (isCPPO .isωChainComplete s) .height 
    sIsNoetherian .stabilize =  (isCPPO .isωChainComplete s) .stabilize 
    p = s (sIsNoetherian . height)
    isLFP : IsLeastFixedPoint _≈_ _≲_ f p
    isLFP .isFixedPoint =  isCPPO .isEquivalence .IsEquivalence.sym ((sIsNoetherian .stabilize) (sIsNoetherian .height) ≤-refl) where
      open import Data.Nat.Properties
    isLFP .least x fx≈x = fⁿ⊥≲x where
      fⁿ⊥≲fⁿx = iter-monotone f fIsMonotone (sIsNoetherian .height) ⊥ x (isCPPO .minimum x)
      fⁿx≈x = iter-fixed f (isCPPO .isEquivalence) (Eq.isRelHomomorphism fIsMonotone) (sIsNoetherian .height) x fx≈x
      fⁿ⊥≲x = isCPPO .trans  fⁿ⊥≲fⁿx (isCPPO .reflexive fⁿx≈x) 

