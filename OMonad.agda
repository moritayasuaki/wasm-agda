module OMonad where 

open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.Morphism
open import Data.Unit

private
  variable
    a b c i f g h : Level
    A : Set a
    B : Set b
    C : Set c
    I : Set i

RelFunExt : (A : Set a) → Rel B g → Rel (A → B) (a ⊔ g)
RelFunExt A R f g = (a : A) → R (f a) (g a)

module _ where
    open IsPreorder
    open IsEquivalence
    RelFunExt-preservePreorder : ∀{a b l l'} {A : Set a} {B : Set b} {E : Rel B l} {O : Rel B l'} → IsPreorder E O → IsPreorder (RelFunExt A E) (RelFunExt A O)
    RelFunExt-preservePreorder record
      { isEquivalence = record
        { refl = eq-refl
        ; sym = eq-sym
        ; trans = eq-trans
        }
      ; reflexive = ord-reflexive
      ; trans = ord-trans } = record
      { isEquivalence = record
        { refl = λ _ → eq-refl
        ; sym = λ s n → eq-sym (s n)
        ; trans = λ t t' n → eq-trans (t n) (t' n)
        }
      ; reflexive = λ r n → ord-reflexive (r n)
      ; trans = λ t t' n → ord-trans (t n) (t' n)
      }

IRel : {I : Set i} → IFun I f → (g : Level) → Set (i ⊔ suc f ⊔ suc g)
IRel {I = I} M g = (i j : I) → (A : Set _) → Rel (M i j A) g

IRel : {I : Set i} → I → I → (M : IFun I f) → (A : Set f) → Rel A g → Rel A g


record RawRIMonad {I : Set i} (M : IFun I f)

record RawOIMonad {I : Set i} (M : IFun I f) (E : IRel M g) (O : IRel M h) : Set (i ⊔ suc g ⊔ suc h ⊔ suc f) where
  field
    monad : RawIMonad M
  open RawIMonad monad public

  field
    isPreorder : (i j : I) → (A : Set _) → IsPreorder (E i j A) (O i j A)
    isOrderHomomorphismL : (i j k : I) → (A B : Set _) → (f : A → M j k B)
        → IsOrderHomomorphism (E i j A) (E i k B) (O i j A) (O i k B) (_>>= f)
    isOrderHomomorphismR : (i j k : I) → (A B : Set _) → (m : M i j A)
        → IsOrderHomomorphism (RelFunExt A (E j k B)) (E i k B) (RelFunExt A (O j k B)) (O i k B) (m >>=_)

FRel : ∀{f} → (Set f → Set f) → (g : Level) → Set (suc f ⊔ suc g)
FRel {f} M g = (A : Set f) → Rel (M A) g

ObjectwiseRelFunExt : ∀{f M} → (N : Set f) → FRel M g → FRel {f = f} (λ A → (N → M A)) (f ⊔ g)
ObjectwiseRelFunExt N R A = RelFunExt N (R A)

RawOMonad : (M : Set f → Set f) → (E : FRel M g) → (O : FRel M h) → Set _
RawOMonad M E O = RawOIMonad {I = ⊤} (λ _ _ → M) (λ _ _ → E) (λ _ _ → O)

module RawOMonad {M : Set f → Set f} {E : FRel M g} {O : FRel M h} (Mon : RawOMonad M E O) where
  open RawOIMonad Mon public

IsExtensive : ∀{g f} {A : Set f} → Rel A g → (A → A) → Set (f ⊔ g)
IsExtensive _≲_ f = ∀ a → a ≲ f a

record IsExterierOperator {g f : Level} {A : Set f} (O : Rel A g) (ext : A → A) : Set (g ⊔ f) where
  field
    isExtensive : IsExtensive {g = g} O ext
    isRelHomomorphism : IsRelHomomorphism O O ext
  open IsRelHomomorphism isRelHomomorphism public