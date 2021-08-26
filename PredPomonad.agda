module PredPomonad where 

-- predicate monad

open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Morphism
-- open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Category.Functor using (RawFunctor)
open import Function
open import HMonad
open import PredLattice

private
  variable
    i j k : Level
    A B C : Set i
    P : Set j
    M F : Set i → Set j


open import Relation.Unary hiding (∅ ; U)

Forward : Set i → (j : Level) → Set (i ⊔ suc j)
Forward A j = Pred (Set j × A) j -- (P × A) → P

Backward : Set i → (j : Level) → Set (i ⊔ suc j)
Backward A j = Pred (Pred A j) j -- (A → P) → P

Bidirectional : Set i → (j : Level) → Set (i ⊔ suc j)
Bidirectional A j = Pred (Set j × (Pred A j)) j -- (P × (A → P)) → P



{-
  powersetMonad : ∀{i} → RawHPomonad (Pred {i} {i}) _≐_ _⊆_
  powersetMonad = record
    { rawHMonad = record
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

  contraPowersetMonad : ∀{i} → RawHPomonad (Pred {i} {i}) _≐_ _⊆_
  contraPowersetMonad = record
    { rawHMonad = record
        { return = _≡_
        ; _>>=_ = λ m f b → ∀ a → m a → f a b
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL =  λ w → record
      { cong =  λ aeq →  ( ( λ b a ya → {! !}) ,  λ b a ya → {!!} )
      ; mono =  λ imp → λ p a ya → {! imp (p a)!}
      }
    ; isOrderHomomorphismR = {!!}
    }

  forwardMonad : ∀{i} → RawHPomonad (Forward {i} {i}) _≐_ _⊆_
  forwardMonad {i} = record
    { rawHMonad = record -- a -> (pre × a)
        { return = λ a → λ {(p , a') → p × a' ≡ a}
        ; _>>=_ = λ m f → λ {(p , b) → ∀ a → m (p , a) → f a (p , b)}
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL =  λ w → record {cong =  λ (p , q) →  ( ( λ d d' y → d d' (q y )) ,  λ d d' y →  d d' (p y) )  ; mono =  λ imp → {!!} }
    ; isOrderHomomorphismR = {!!}
    }

  backwardMonad : ∀{i} → RawHPomonad (Backward {i} {i}) _≐_ _⊆_
  backwardMonad {i} = record
    { rawHMonad = record
        { return = λ a k → k a
        ; _>>=_ = λ c f k → c (flip f k)
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = {!!}
    ; isOrderHomomorphismR = {!!}
    }

  bidirectionalMonad : ∀{i} → RawHPomonad (Bidirectional {i} {i}) _≐_ _⊆_
  bidirectionalMonad = record
    { rawHMonad = record
        { return = λ a → λ{ (p , k) → k a × p}
        ; _>>=_ = λ c f → λ{ (p , k) → c (p , flip f ((p , k)))}
        }
    ; isPartialOrder = ⊆-isPartialOrder
    ; isOrderHomomorphismL = {!!}
    ; isOrderHomomorphismR = {!!}
    }
-}