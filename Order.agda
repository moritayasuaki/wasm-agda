module Order where

open import Level
open import Relation.Binary
open import Relation.Binary.Morphism

private
  variable
    a b c ℓ : Level

record HasOrder (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    E : Rel A ℓ
    O : Rel A ℓ

record HasPreorder (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    hasOrder : HasOrder A ℓ
  open HasOrder hasOrder
  field
    isPreorder : IsPreorder E O
  open HasOrder hasOrder public

record HasPartialOrder (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    hasOrder : HasOrder A ℓ
  open HasOrder hasOrder
  field
    isPartialOrder : IsPartialOrder E O
  open HasOrder hasOrder public

open import Relation.Unary


funextRel : {P : Set ℓ} → (A : Set a) → Rel P ℓ → Rel (A → P) (a ⊔ ℓ)
funextRel A R f g = (x : A) → R (f x) (g x)

module FunextProperties {P : Set ℓ} (A : Set a) {R : Rel P ℓ} {R' : Rel P ℓ} where
  ext : Rel P ℓ → Rel (A → P) (a ⊔ ℓ)
  ext = funextRel A

  prefl : Reflexive R → Reflexive (ext R)
  prefl refl a = refl

  psym : Symmetric R → Symmetric (ext R)
  psym sym aij a = sym (aij a)

  ptrans : Transitive R → Transitive (ext R)
  ptrans trans aij ajk a = trans (aij a) (ajk a)

  potrans : Transitive R' → Transitive (ext R')
  potrans trans aij ajk a = trans (aij a) (ajk a)

  pantisym : Antisymmetric R R' → Antisymmetric (ext R) (ext R')
  pantisym antisym aij aji a = antisym (aij a) (aji a)

  pequiv : IsEquivalence R → IsEquivalence (ext R)
  IsEquivalence.refl (pequiv record { refl = refl ; sym = sym ; trans = trans }) = prefl refl
  IsEquivalence.sym (pequiv record { refl = refl ; sym = sym ; trans = trans }) = psym sym
  IsEquivalence.trans (pequiv record { refl = refl ; sym = sym ; trans = trans }) = ptrans trans

  ppreorder : IsPreorder R R' → IsPreorder (ext R) (ext R')
  IsPreorder.isEquivalence (ppreorder record { isEquivalence = isEquivalence ; reflexive = reflexive ; trans = trans }) = pequiv isEquivalence
  IsPreorder.reflexive (ppreorder record { isEquivalence = isEquivalence ; reflexive = reflexive ; trans = trans }) = λ f a → reflexive (f a)
  IsPreorder.trans (ppreorder record { isEquivalence = isEquivalence ; reflexive = reflexive ; trans = trans }) = potrans trans

  ppartialorder : IsPartialOrder R R' → IsPartialOrder  (ext R) (ext R')
  IsPartialOrder.isPreorder (ppartialorder record { isPreorder = isPreorder ; antisym = antisym }) = ppreorder isPreorder
  IsPartialOrder.antisym (ppartialorder record { isPreorder = isPreorder ; antisym = antisym }) = pantisym antisym

funextOrder : {P : Set ℓ} → (A : Set a) → HasOrder P ℓ → HasOrder (A → P) (a ⊔ ℓ)
funextOrder A record { E = E ; O = O } = record { E = funextRel A E ; O = funextRel A O }

funextPreorder : {P : Set ℓ} → (A : Set a) → HasPreorder P ℓ → HasPreorder (A → P) (a ⊔ ℓ)
funextPreorder A record
  { hasOrder = hasOrder
  ; isPreorder = isPreorder
  } = record 
  { hasOrder = funextOrder A hasOrder
  ; isPreorder = FunextProperties.ppreorder A isPreorder
  }

funextPartialOrder : {P : Set ℓ} → (A : Set a) → HasPartialOrder P ℓ → HasPartialOrder (A → P) (a ⊔ ℓ)
funextPartialOrder A record
  { hasOrder = hasOrder
  ; isPartialOrder = isPartialOrder
  } = record
  { hasOrder = funextOrder A hasOrder
  ; isPartialOrder = FunextProperties.ppartialorder A isPartialOrder
  }

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



{-
open import Category.Monad.Indexed

PwRawPoset : {i a : Level} {I : Set i} → IFun I a → (ℓ ℓ' : Level) → Set _
PwRawPoset {a = a} {I = I} M ℓ ℓ' = (i j : I) → (A : Set a) → RawPoset (M i j A) ℓ ℓ'

record RawIPomonad {i a : Level} {I : Set i} (M :  IFun I a) (ℓ ℓ' : Level) : Set (i ⊔ suc a ⊔ suc ℓ ⊔ suc ℓ') where
  field
    rawIMonad : RawIMonad M
    pwRawPoset : PwRawPoset M ℓ ℓ'
  open RawIMonad rawIMonad

  fwRawPoset : (i j : I) → (A B : Set a) → RawPoset (A → (M i j B)) (a ⊔ ℓ) (a ⊔ ℓ')
  fwRawPoset i j A B = funextPoset A (pwRawPoset i j B)

  field
    pwBimonotone : ∀{i j k} {A B C : Set a} → IsBimonotone (fwRawPoset i j A B) (fwRawPoset j k B C) (fwRawPoset i k A C) _>=>_


RawIPomonadT : {i a : Level} {I : Set i} → (IFun I a → IFun I a) → (ℓ ℓ' ℓ'' ℓ''' : Level) → Set _
RawIPomonadT T ℓ ℓ' ℓ'' ℓ''' = ∀ {M} → RawIPomonad M ℓ ℓ' → RawIPomonad (T M) ℓ'' ℓ'''
-}