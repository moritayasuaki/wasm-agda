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

variable
  a b ℓ₁ ℓ₂  : Level
  X : Set a
  Y : Set b

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
    IsFp : (C → C) → C → Set _
    IsFp f x = x ≈ f x 
    record IsLfp (f : C → C) (p : C) : Set (Level.suc (c ⊔ ℓ₁ ⊔ ℓ₂))  where
      field
        fixed : IsFp f p
        least : (x : C) → IsFp f x → p ≲ x
    IsMonotone = IsOrderHomomorphism _≈_ _≈_ _≲_ _≲_

  lfp : (f : C → C) → IsMonotone f → Σ C (IsLfp f)
  lfp f f-is-monotone = (p , record
      { fixed = fixed
      ; least = ≤-iter height
      }) where
    iter : (C → C) → ℕ → C → C
    iter f Nat.zero = id
    iter f (Nat.suc n) = f ∘ (iter f n)
    chain = flip (iter f) ⊥
    open IsOrderHomomorphism f-is-monotone
    chain-is-omega-chain : IsOmegaChain chain _≲_
    chain-is-omega-chain Nat.zero = minimum (f ⊥)  
    chain-is-omega-chain (Nat.suc n) = mono (chain-is-omega-chain n)
    chain-is-noeth : IsNoetherian chain _≈_
    chain-is-noeth = omega-chain-is-noetherian chain chain-is-omega-chain
    open IsNoetherian chain-is-noeth
    p = chain height
    fixed = stabilize height ≤-refl where
      open import Data.Nat.Properties
    ≤-iter : (n : ℕ) → (x : C) → IsFp f x → iter f n ⊥ ≲ x
    ≤-iter Nat.zero 
    ≤-iter (Nat.suc n) x x-is-fp =  ≤-respʳ-≈ (sym x-is-fp) (mono (≤-iter n x x-is-fp)) where
      open IsEquivalence isEquivalence
      

