module RelationAlgebra where

open import Level
open import Function
open import Data.Nat as Nat using (ℕ)
open import Data.Product
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.Morphism.Structures
open import Algebra

module _ where
  private
    variable
      a b ℓ₁ ℓ₂  : Level
      X : Set a
      Y : Set b
      _≈_ : Rel X ℓ₁
      _≲_ : Rel X ℓ₂

  IsOmegaChain : (ℕ → X) → Rel X ℓ₁ → Set ℓ₁
  IsOmegaChain c _≲_ = (i : ℕ) → c i ≲ c (ℕ.suc i)

  record IsNoetherian (c : ℕ → X) (_≈_ : Rel X ℓ₂) : Set ℓ₂ where
    field
      height : ℕ
      stabilize : (i : ℕ) → (height Nat.≤ i) → c i ≈ c (ℕ.suc i)

  record IsEffectiveBoundedJoinSemilattice {X : Set a} (_≈_ : Rel X ℓ₁) (_≲_ : Rel X ℓ₂) (_∨_ : X → X → X) (⊥ : X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      omega-chain-is-noetherian : (c : ℕ → X) → IsOmegaChain c _≲_ → IsNoetherian c _≈_
      isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≲_ _∨_ ⊥
    open IsBoundedJoinSemilattice isBoundedJoinSemilattice public


  IsFixedPoint : Rel X ℓ₁ → (X → X) → X → Set _
  IsFixedPoint _≈_ f x = f x ≈ x


  iter : (X → X) → ℕ → X → X
  iter f Nat.zero = id
  iter f (Nat.suc n) = f ∘ iter f n

  iter-mono : (f : X → X) → (IsOrderHomomorphism _≈_ _≈_ _≲_ _≲_ f) →
    (n : ℕ) → (x y : X) → (x ≲ y) → iter f n x ≲ iter f n y
  iter-mono f f-is-monotone (Nat.zero) x y p = p
  iter-mono f f-is-monotone (Nat.suc n) x y p = mono (iter-mono f f-is-monotone n x y p) where
    open IsOrderHomomorphism f-is-monotone
  iter-fixed : (f : X → X) → (IsEquivalence _≈_) → (IsRelHomomorphism _≈_ _≈_ f) →
    (n : ℕ) → (x : X) → IsFixedPoint _≈_ f x → iter f n x ≈ x
  iter-fixed f ≈-is-equiv _ Nat.zero _ _ = refl where
    open IsEquivalence ≈-is-equiv
  iter-fixed f ≈-is-equiv f-is-closed-under-≈ (Nat.suc n) x fx≈x = trans (cong fⁿx≈x) fx≈x where
    open IsRelHomomorphism f-is-closed-under-≈
    open IsEquivalence ≈-is-equiv
    fⁿx≈x = iter-fixed f ≈-is-equiv f-is-closed-under-≈ n x fx≈x

record EffectiveBoundedJoinSemilattice c ℓ₁ ℓ₂ : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≲_
  infixr 7 _∨_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≲_     : Rel Carrier ℓ₂
    _∨_     : Op₂ Carrier
    ⊥       : Carrier
    isEffectiveBoundedJoinSemilattice : IsEffectiveBoundedJoinSemilattice _≈_ _≲_ _∨_ ⊥

  open IsEffectiveBoundedJoinSemilattice isEffectiveBoundedJoinSemilattice public

  private
    C = Carrier
    record IsLeastFixedPoint (f : C → C) (p : C) : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂))  where
      field
        fixed : IsFixedPoint _≈_ f p
        least : (x : C) → IsFixedPoint _≈_ f x → p ≲ x
    IsMonotone = IsOrderHomomorphism _≈_ _≈_ _≲_ _≲_

  lfp : (f : C → C) → IsMonotone f → Σ C (IsLeastFixedPoint f)
  lfp f f-is-monotone = (p , record
      { fixed = fixed -- fixed
      ; least = least
      }) where
    chain = flip (iter f) ⊥
    open IsOrderHomomorphism f-is-monotone
    chain-is-omega-chain : IsOmegaChain chain _≲_
    chain-is-omega-chain Nat.zero = minimum (f ⊥)  
    chain-is-omega-chain (Nat.suc n) = mono (chain-is-omega-chain n)
    chain-is-noeth : IsNoetherian chain _≈_
    chain-is-noeth = omega-chain-is-noetherian chain chain-is-omega-chain
    open IsNoetherian chain-is-noeth
    p = chain height
    fixed = sym (stabilize height ≤-refl) where
      open import Data.Nat.Properties
      open IsEquivalence isEquivalence
    least : (x : C) → IsFixedPoint _≈_ f x → p ≲ x
    least x fx≈x =  ≤-respʳ-≈ fⁿx≈x fⁿ⊥≲fⁿx  where
      fⁿ⊥≲fⁿx = iter-mono f f-is-monotone height ⊥ x (minimum x)
      fⁿx≈x = iter-fixed f isEquivalence Eq.isRelHomomorphism height x fx≈x

