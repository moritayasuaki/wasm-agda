module RelationAlgebra where

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

  Rel₀ : Set₀ → Set₁
  Rel₀ T = Rel T Level.zero

  private
    variable
 --     a b c ℓ₁ ℓ₂ : Level
      A : Set₀
      B : Set₀

  _:ᴿ_ : (A × A) → Rel₀ A → Set
  (a , a') :ᴿ R = R a a'

  _×ᴿ_ : Rel₀ A → Rel₀ B → Rel₀ (A × B)
  R ×ᴿ Q = λ (a , b) (a' , b') → ((a , a') :ᴿ R) × ((b , b') :ᴿ Q)

  _→ᴿ_ : Rel₀ A → Rel₀ B → Rel₀ (A → B)
  _→ᴿ_ {A = A} R Q = λ f f' → (x x' : A) → (x , x') :ᴿ R → (f x , f' x') :ᴿ Q

  _⊆ᴿ_ : Rel₀ A → Rel₀ A → Set
  _⊆ᴿ_ {A = A} R R' = (x x' : A) → (x , x') :ᴿ R → (x , x') :ᴿ R'

  F2R : (A → A) → Rel₀ A
  F2R f a a' = f a ≡ a'

  open import Data.Bool
  open import Data.Integer
  open import Data.Unit
  open import Data.Sum
  -- open import Relation.Unary

  Δ : ∀{X : Set₀} → Rel₀ X
  Δ x x' = _≡_ x x'
  𝔹 = Bool

  𝕋 : ∀{X} → Rel₀ X
  𝕋 x x' = ⊤

  singletonᴿ : ∀{X} → X → X → Rel₀ X
  singletonᴿ x₀ x₀' = λ x x' → (x ≡ x₀) × (x' ≡ x₀')

  ∪ᴿ : ∀{X} → Rel₀ X → Rel₀ X → Rel₀ X 
  ∪ᴿ r r' = λ x y → _⊎_ (r x y)  (r' x y)

  diag : ∀{X : Set} → X → X × X
  diag a = (a , a)

  diag₂ : ∀{X} → (Δ {X = X}) ⊆ᴿ (Δ {X = X})
  diag₂ x x' p = p

  𝕋-weakest : ∀{X : Set} → (R : Rel₀ X) → R ⊆ᴿ 𝕋
  𝕋-weakest R = λ x x' p → tt

  isNotObservablyReadingX : ((ℤ × ℤ) → (ℤ × ℤ)) → Set
  isNotObservablyReadingX f = Σ ((ℤ → 𝔹) × (ℤ → ℤ) × (ℤ → ℤ)) λ (f₁ , f₂ , f₃) → ∀ (X Y : ℤ) → f (X , Y) ≡ (( if (f₁ Y) then X else f₂ Y ) , f₃ Y)

  isNotObservablyReadingXR : ((ℤ × ℤ) → (ℤ × ℤ)) → Set₁
  isNotObservablyReadingXR f = (R : Rel₀ ℤ) → (Δ ⊆ᴿ R) → (diag f :ᴿ ((R ×ᴿ Δ) →ᴿ (R ×ᴿ Δ)))

  equiv⇒ : (f : (ℤ × ℤ) → (ℤ × ℤ)) → isNotObservablyReadingX f → isNotObservablyReadingXR f
  equiv⇒ f ((f₁ , f₂ , f₃) , nReadX) R pΔ⊆ᴿR (X , Y) (X' , .Y) (XR , _≡_.refl) with f₁ Y | inspect f₁ Y
  ... | false | [ eq ] =
    let eqPost = λ x d → ≡-sym $ ≡-cong d $ ≡-subst (λ cond → f (x , Y) ≡ ((if cond then x else f₂ Y) , f₃ Y)) eq (nReadX x Y)
        eq = eqPost X proj₁
        eq' = eqPost X' proj₁
        eq'' = eqPost X proj₂
        eq''' = eqPost X' proj₂
        Rfy = pΔ⊆ᴿR (f₂ Y) (f₂ Y) ≡-refl
        P = ≡-subst₂ (λ x x' → R x x') eq eq' Rfy
        Δfy' = ≡-refl {x = f₃ Y}
        Q = ≡-subst₂ (λ y y' → y ≡ y') eq'' eq''' Δfy'
    in ( P , Q ) 
  ... | true | [ eq ] =
    let eqPost = λ x d → ≡-sym $ ≡-cong d $ ≡-subst (λ cond → f (x , Y) ≡ ((if cond then x else f₂ Y) , f₃ Y)) eq (nReadX x Y)
        eq = eqPost X proj₁
        eq' = eqPost X' proj₁
        eq'' = eqPost X proj₂
        eq''' = eqPost X' proj₂
        P = ≡-subst₂ (λ x x' → R x x') eq eq' XR
        Δfy' = ≡-refl {x = f₃ Y}
        Q = ≡-subst₂ (λ y y' → y ≡ y') eq'' eq''' Δfy'
    in ( P , Q )
  
  equiv⇐ : (f : (ℤ × ℤ) → (ℤ × ℤ)) → isNotObservablyReadingXR f → isNotObservablyReadingX f
  equiv⇐ f nReadXR =
    let f0 = λ Y → f (0ℤ , Y)
        f1 = λ Y → f (0ℤ , Y)
        _==_ = λ z z' → does (Data.Integer._≟_ z z')
        fb = {!   !}
        R = (λ x x' → Δ x x' ⊎ (singletonᴿ 0ℤ 1ℤ) x x')
        f-is-YΔ-preserving = nReadXR 𝕋 (𝕋-weakest Δ)
        f-is-XR-preserving = nReadXR R (λ _ _ → inj₁)
        feq = λ X Y → f-is-YΔ-preserving (X , Y) (X , Y) (tt , ≡-refl {x = Y})
    in (( fb , proj₁ ∘ f0 , proj₂ ∘ f0) , {! f !})
