module Order where

open import Level
open import Relation.Binary
open import Relation.Binary.Morphism

private
  variable
    a b c ℓ ℓ' : Level

record IsOrder {a ℓ ℓ₂ : Level} {A : Set a} (_≈_ : Rel A ℓ) (_~_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPartialEquivalence : IsPartialEquivalence _≈_
    trans : Transitive _~_
    refl : _≈_ ⇒ _~_
    antisym : Antisymmetric _≈_ _~_ 

record HasPartialEquivalence (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    P : Rel A ℓ
    isPartialEquivalence : IsPartialEquivalence P

module _{a : Level} (A : Set a) (ℓ : Level) where
  record HasOrder : Set (a ⊔ suc ℓ) where
    field
      E : Rel A ℓ
      O : Rel A ℓ

  record HasPreorder : Set (a ⊔ suc ℓ) where
    field
      hasOrder : HasOrder
    open HasOrder hasOrder
    field
      isPreorder : IsPreorder E O
    open HasOrder hasOrder public

  record HasPartialOrder : Set (a ⊔ suc ℓ) where
    field
      hasOrder : HasOrder
    open HasOrder hasOrder
    field
      isPartialOrder : IsPartialOrder E O
    open HasOrder hasOrder public

RelT : (T : Set a → Set b) → (ℓ ℓ' : Level) → Set (suc (a ⊔ ℓ ⊔ ℓ') ⊔ b)
RelT T ℓ ℓ' = ∀{A} → Rel A ℓ → Rel (T A) ℓ'

module FunExt
  {a : Level} -- level of base type
  (A : Set a) -- a type to be used to extend
  (ℓ : Level) -- lower bound of the level of relation
  where

  funext : Set b → Set (a ⊔ b)
  funext B = A → B

  relT : {b : Level} → RelT (funext {b = b}) ℓ (a ⊔ ℓ)
  relT R f g = (x : A) → R (f x) (g x)

  module _ (R : Rel A ℓ) where

    reflT : Reflexive R → Reflexive (relT R)
    reflT refl a = refl

    symT : Symmetric R → Symmetric (relT R)
    symT sym aij a = sym (aij a)

    transT : Transitive R → Transitive (relT R)
    transT trans aij ajk a = trans (aij a) (ajk a)

  module _ (R R' : Rel A ℓ) where
    antisymT : Antisymmetric R R' → Antisymmetric (relT R) (relT R')
    antisymT antisym aij aji a = antisym (aij a) (aji a)

    oreflT : R ⇒ R' → (relT R) ⇒ (relT R')
    oreflT orefl aij a = orefl (aij a)

    pequivT : IsPartialEquivalence R → IsPartialEquivalence (relT R)
    pequivT pe = record { sym = symT R sym ; trans = transT R trans} where open IsPartialEquivalence pe

    equivT : IsEquivalence R → IsEquivalence (relT R)
    equivT e = record { refl = reflT R refl ; sym = symT R sym ; trans = transT R trans} where open IsEquivalence e

    preorderT : IsPreorder R R' → IsPreorder (relT R) (relT R')
    preorderT pre = record { isEquivalence = equivT isEquivalence ; reflexive = oreflT reflexive ; trans = transT R' trans} where open IsPreorder pre

    partialorderT : IsPartialOrder R R' → IsPartialOrder  (relT R) (relT R')
    partialorderT po = record { isPreorder = preorderT isPreorder ; antisym = antisymT antisym} where open IsPartialOrder po

  hasOrderT : HasOrder A ℓ → HasOrder (funext A) _
  hasOrderT record 
    { E = E
    ; O = O
    } = record 
    { E = relT E
    ; O = relT O
    }

  hasPreorderT : HasPreorder A ℓ → HasPreorder (funext A) _
  hasPreorderT record
    { hasOrder = hasOrder
    ; isPreorder = isPreorder
    } = record 
    { hasOrder = hasOrderT hasOrder
    ; isPreorder = preorderT E O isPreorder
    } where open HasOrder hasOrder

  hasPartialOrderT : HasPartialOrder A ℓ → HasPartialOrder (funext A) _
  hasPartialOrderT record
    { hasOrder = hasOrder
    ; isPartialOrder = isPartialOrder
    } = record
    { hasOrder = hasOrderT hasOrder
    ; isPartialOrder = partialorderT E O isPartialOrder
    } where open HasOrder hasOrder

-- monotone function
record IsMonotone {A : Set a} {B : Set b} (RA : HasOrder A ℓ) (RB : HasOrder B ℓ)
    (f : A → B) : Set (a ⊔ b ⊔ ℓ) where
  open HasOrder
  field
    cong : ∀{a a'} → RA .E a a' → RB .E (f a) (f a')
    mono : ∀{a a'} → RA .O a a' → RB .O (f a) (f a')

-- monotone with respect to 2 arguments
record IsBimonotone {A : Set a} {B : Set b} {C : Set c}
    (RA : HasOrder A ℓ) (RB : HasOrder B ℓ) (RC : HasOrder C ℓ)
    (f : A → B → C) : Set (a ⊔ b ⊔ c ⊔ ℓ) where
  open HasOrder
  field
    cong₂ : ∀{a a' b b'} → RA .E a a' → RB .E b b' → RC .E (f a b) (f a' b')
    mono₂ : ∀{a a' b b'} → RA .O a a' → RB .O b b' → RC .O (f a b) (f a' b')

IsExtensive : {A : Set a} → Rel A ℓ → (A → A) → Set (a ⊔ ℓ)
IsExtensive _≲_ f = ∀ a → a ≲ f a

record IsExterierOperator {A : Set a} (O : Rel A ℓ) (ext : A → A) : Set (a ⊔ ℓ) where
  field
    isExtensive : IsExtensive O ext
    isRelHomomorphism : IsRelHomomorphism O O ext
  open IsRelHomomorphism isRelHomomorphism public

-- objectwise order
HasPointwiseOrder : (Set a → Set b) → (ℓ : Level) → Set _
HasPointwiseOrder M ℓ = ∀ A → HasOrder (M A) ℓ

HasPointwisePreorder : (Set a → Set b) → (ℓ : Level) → Set _
HasPointwisePreorder M ℓ = ∀ A → HasPreorder (M A) ℓ

HasPointwisePartialOrder : (Set a → Set b) → (ℓ : Level) → Set _
HasPointwisePartialOrder M ℓ = ∀ A → HasPartialOrder (M A) ℓ

HasPairwiseOrder : (Set a → Set a → Set b) → (ℓ : Level) → Set _
HasPairwiseOrder F ℓ = ∀ A B → HasOrder (F A B) ℓ

HasPairwisePreorder : (Set a → Set a → Set b) → (ℓ : Level) → Set _
HasPairwisePreorder F ℓ = ∀ A B → HasPreorder (F A B) ℓ

HasPairwisePartialOrder : (Set a → Set a → Set b) → (ℓ : Level) → Set _
HasPairwisePartialOrder F ℓ = ∀ A B → HasPartialOrder (F A B) ℓ
