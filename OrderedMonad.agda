module OrderedMonad where 

open import Level
open import Relation.Binary
open import Relation.Binary.Morphism
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Category.Functor using (RawFunctor)
open import Function

record RawGApplicative {i j : Level} (F : Set i → Set j) : Set (suc i ⊔ suc j) where
  field
    pure : {A : Set i} → A → F A
    _⊛_ : {A B : Set i} → F (A → B) → F A → F B

  rawFunctor : RawFunctor F
  rawFunctor = record
    { _<$>_ = λ g x → pure g ⊛ x
    }

  private
    open module RF = RawFunctor rawFunctor public

record RawGMonad {i j : Level} (M : Set i → Set j) : Set (suc i ⊔ suc j) where
  field
    return : {A : Set i} → A → M A
    _>>=_ : {A B : Set i} → M A → (A → M B) → M B

  rawGApplicative : RawGApplicative M
  rawGApplicative = record
    { pure = return
    ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
    }

  open RawGApplicative rawGApplicative public


join : ∀{i} → {A : Set i} → {M : Set i → Set i} → {RawGMonad M} → M (M A) → M A
join {_} {_} {_} {mo} mma =  let open RawGMonad mo in mma >>= Function.id

open Relation.Binary
open Relation.Binary.Morphism

record RawGPomonad {i j k} (M : Set i → Set j) (_≈_ : ∀{A} → Rel (M A) k) (_≲_ : ∀{A} → Rel (M A) k) : Set (suc i ⊔ suc j ⊔ k) where
  field
    rawGMonad : RawGMonad M
    isPartialOrder : ∀{A} → IsPartialOrder (_≈_ {A}) (_≲_ {A})

  open RawGMonad rawGMonad public
  open IsPartialOrder public

  field
    isOrderHomomorphismL : ∀{A B} → ∀ (w : A → M B) → IsOrderHomomorphism (_≈_ {A}) (_≈_ {B}) (_≲_ {A}) (_≲_ {B}) (_>>= w)
    isOrderHomomorphismR : ∀{A B} → ∀ (w : M A) → IsOrderHomomorphism (λ f f' → (a : A) → f a ≈ f' a) (_≈_ {B}) (λ f f' → (a : A) → f a ≲ f' a) (_≲_ {B}) (w >>=_)

open import Relation.Unary renaming (Pred to Pred')

Pred : ∀{a b} → Set a → Set (a ⊔ suc b)
Pred {_} {b} A = Pred' A b -- A -> P

Forward : ∀{a b} → Set a → Set (a ⊔ suc b)
Forward {a} {b} A = Pred {a ⊔ suc b} {b} (Set b × A) -- (P × A) → P

Backward : ∀{a b} → Set a → Set (a ⊔ suc b)
Backward {a} {b} A = Pred {a ⊔ suc b} {b} (Pred {a} {b} A) -- (A → P) → P

Bidirectional : ∀{a b} → Set a → Set (a ⊔ suc b)
Bidirectional {a} {b} A = Pred {a ⊔ suc b} {b} (Set b × (Pred {a} {b} A)) -- (P × (A → P)) → P

-- bind x f = join (f <$>_) (return x)
-- U ( ) ({x})



module _ where

  open import Relation.Unary renaming (Pred to Pred')
  _≐_ : ∀{a b A} → Pred {a} {b} A → Pred {a} {b} A → Set _
  P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

  ≐-isEquivalence : ∀{a b A} → IsEquivalence {A = Pred {a} {b} A} _≐_
  ≐-isEquivalence = record
    { refl =  (id , id)
    ; sym = Data.Product.swap
    ; trans = λ (p , q) (r , s) → (r ∘ p , q ∘ s)
    }

  ⊆-isPartialOrder : ∀{a b A} → IsPartialOrder {A = Pred {a} {b} A}_≐_ _⊆_
  ⊆-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = ≐-isEquivalence
      ; reflexive = proj₁
      ; trans = λ p q → q ∘ p
      }
    ; antisym = (_,_) 
    }

  powersetMonad : ∀{i} → RawGPomonad (Pred {i} {i}) _≐_ _⊆_
  powersetMonad = record
    { rawGMonad = record
      { return = _≡_
      ; _>>=_ = λ m f b → ∃ λ a → m a × f a b
      }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = λ w → record
      { cong = λ eq → ((λ ( a , pa , qab ) → ( a , proj₁ eq pa , qab )) , (λ( a , pa , qab ) → ( a , proj₂ eq pa , qab ))) 
      ; mono = λ imp →  λ ( a , pa , qab ) → ( a  , imp pa , qab )
      }
    ; isOrderHomomorphismR = λ w → record
      { cong = λ aeq → (((λ ( a , pa , qab) → (a ,  pa , proj₁ (aeq a) qab))) , (λ ( a , pa , qab) → (a ,  pa ,  proj₂ (aeq a) qab )))
      ; mono = λ imp → λ (a , pa , qab ) → ( a , pa , imp a qab ) 
      }
    }

  contraPowersetMonad : ∀{i} → RawGPomonad (Pred {i} {i}) _≐_ _⊆_
  contraPowersetMonad = record
    { rawGMonad = record
        { return = _≡_
        ; _>>=_ = λ m f b → ∀ a → m a → f a b
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = {!!}
    ; isOrderHomomorphismR = {!!}
    }

  forwardMonad : ∀{i} → RawGPomonad (Forward {i} {i}) _≐_ _⊆_
  forwardMonad {i} = record
    { rawGMonad = record -- a -> (pre × a)
        { return = λ a → λ {(p , a') → p × a' ≡ a}
        ; _>>=_ = λ m f → λ {(p , b) → ∀ a → m (p , a) → f a (p , b)}
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = {!!}
    ; isOrderHomomorphismR = {!!}
    }

  backwardMonad : ∀{i} → RawGPomonad (Backward {i} {i}) _≐_ _⊆_
  backwardMonad {i} = record
    { rawGMonad = record
        { return = λ a k → k a
        ; _>>=_ = λ c f k → c (flip f k)
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = {!!}
    ; isOrderHomomorphismR = {!!}
    }

  bidirectionalMonad : ∀{i} → RawGPomonad (Bidirectional {i} {i}) _≐_ _⊆_
  bidirectionalMonad = record
    { rawGMonad = record
        { return = λ a → λ{ (p , k) → k a × p}
        ; _>>=_ = λ c f → λ{ (p , k) → c (p , flip f ((p , k)))}
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = {!!}
    ; isOrderHomomorphismR = {!!}
    }
