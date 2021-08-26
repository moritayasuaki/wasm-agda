module BiRel where

open import Level
open import Relation.Binary
open import Relation.Binary.Morphism

private
  variable
    a b c ℓ ℓ' : Level

record IsOrder {A : Set a} (_≈_ : Rel A ℓ) (_~_ : Rel A ℓ') : Set (a ⊔ ℓ ⊔ ℓ') where
  field
    isPartialEquivalence : IsPartialEquivalence _≈_
    trans : Transitive _~_
    refl : _≈_ ⇒ _~_
    antisym : Antisymmetric _≈_ _~_ 

record HasPartialEquivalence (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    P : Rel A ℓ
    isPartialEquivalence : IsPartialEquivalence P

module _ (A : Set a) (ℓ : Level) where
  record HasOrder : Set (a ⊔ suc ℓ) where
    field
      E : Rel A ℓ
      O : Rel A ℓ

  record HasPreorder : Set (a ⊔ suc ℓ) where
    field
      E : Rel A ℓ
      O : Rel A ℓ
      isPreorder : IsPreorder E O
    open IsPreorder isPreorder public

  record HasPartialOrder : Set (a ⊔ suc ℓ) where
    field
      E : Rel A ℓ
      O : Rel A ℓ
      isPartialOrder : IsPartialOrder E O
    open IsPartialOrder isPartialOrder public

RelT : (T : Set a → Set b) → (ℓ ℓ' : Level) → Set (suc (a ⊔ ℓ ⊔ ℓ') ⊔ b)
RelT T ℓ ℓ' = ∀{A} → Rel A ℓ → Rel (T A) ℓ'

module FunExt
  (A : Set a) -- a type to be used to extend
  (ℓ : Level) -- lower bound of the level of relation
  where

  funext : Set b → Set (a ⊔ b)
  funext B = A → B

  relT : RelT {a = b} funext ℓ (a ⊔ ℓ)
  relT R f g = (x : A) → R (f x) (g x)

  module _ (B : Set b) (R : Rel B ℓ) where

    reflT : Reflexive R → Reflexive (relT R)
    reflT refl a = refl

    symT : Symmetric R → Symmetric (relT R)
    symT sym aij a = sym (aij a)

    transT : Transitive R → Transitive (relT R)
    transT trans aij ajk a = trans (aij a) (ajk a)

  module _ (B : Set b) (R R' : Rel B ℓ) where
    antisymT : Antisymmetric R R' → Antisymmetric (relT R) (relT R')
    antisymT antisym aij aji a = antisym (aij a) (aji a)

    oreflT : R ⇒ R' → (relT R) ⇒ (relT R')
    oreflT orefl aij a = orefl (aij a)

    pequivT : IsPartialEquivalence R → IsPartialEquivalence (relT R)
    pequivT pe = record { sym = symT B R sym ; trans = transT B R trans} where open IsPartialEquivalence pe

    equivT : IsEquivalence R → IsEquivalence (relT R)
    equivT e = record { refl = reflT B R refl ; sym = symT B R sym ; trans = transT B R trans} where open IsEquivalence e

    preorderT : IsPreorder R R' → IsPreorder (relT R) (relT R')
    preorderT pre = record { isEquivalence = equivT isEquivalence ; reflexive = oreflT reflexive ; trans = transT B R' trans} where open IsPreorder pre

    partialorderT : IsPartialOrder R R' → IsPartialOrder  (relT R) (relT R')
    partialorderT po = record { isPreorder = preorderT isPreorder ; antisym = antisymT antisym} where open IsPartialOrder po


  module _ (B : Set b) where
    hasOrderT : HasOrder B ℓ → HasOrder (funext B) _
    hasOrderT o = record { E = relT E; O = relT O} where open HasOrder o

    hasPreorderT : HasPreorder B ℓ → HasPreorder (funext B) _
    hasPreorderT o = record { E = relT E; O = relT O; isPreorder = preorderT B E O isPreorder } where open HasPreorder o

    hasPartialOrderT : HasPartialOrder B ℓ → HasPartialOrder (funext B) _
    hasPartialOrderT o = record { E = relT E; O = relT O; isPartialOrder = partialorderT B E O isPartialOrder} where open HasPartialOrder o

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
