module HeteroMonad where
open import Level
open import Relation.Binary
open import Relation.Binary.Morphism
-- open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Category.Functor renaming (RawFunctor to HFunctor)
open import Function

private
  variable
    i j k l : Level
    A B C : Set i

-- heterogeneous applicative functor
record HApplicative (F : Set i → Set j) : Set (suc (i ⊔ j)) where
  field
    pure : A → F A
    _⊛_ : F (A → B) → F A → F B

  hFunctor : HFunctor F
  hFunctor = record
    { _<$>_ = λ g x → pure g ⊛ x
    }

  private
    open module RF = HFunctor hFunctor public

-- heterogeneous monad (this actually is not monad because we can not define join) but still several operations are definable
record HMonad (M : Set i → Set j) : Set (suc (i ⊔ j)) where
  field
    return : A → M A
    _>>=_ : M A → (A → M B) → M B

  hApplicative : HApplicative M
  hApplicative = record
    { pure = return
    ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
    }

  _>>_ : M A → M B → M B
  m >> m' = m >>= const m'

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  open HApplicative hApplicative public

HMonadT : ((Set i → Set j) → (Set k → Set l)) → Set (suc (i ⊔ j ⊔ k ⊔ l))
HMonadT T = ∀{M} → HMonad M → HMonad (T M)

open import Category.Monad
H2Raw : {M : Set i → Set i} → HMonad M → RawMonad M
H2Raw HM = let open HMonad HM in record
  { return = return
  ; _>>=_ = _>>=_
  }

Raw2H : {M : Set i → Set i} → RawMonad M → HMonad M
Raw2H RM = let open RawMonad RM in record
  { return = return
  ; _>>=_ = _>>=_
  }