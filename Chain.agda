module Chain where

open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Relation.Binary
open import Data.Product 
open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

data _≲_ {A : Set} : Maybe A → Maybe A → Set where
  ⊥≲ma : (ma : Maybe A) → nothing ≲ ma
  ma≲ma : (ma : Maybe A) → ma ≲ ma

≲-isPartialOrder : {A : Set} → IsPartialOrder _≡_ (_≲_ {A})
IsEquivalence.refl (IsPreorder.isEquivalence (IsPartialOrder.isPreorder ≲-isPartialOrder)) = refl
IsEquivalence.sym (IsPreorder.isEquivalence (IsPartialOrder.isPreorder ≲-isPartialOrder)) = sym
IsEquivalence.trans (IsPreorder.isEquivalence (IsPartialOrder.isPreorder ≲-isPartialOrder)) = trans
IsPreorder.reflexive (IsPartialOrder.isPreorder ≲-isPartialOrder) {x = ma} refl = ma≲ma ma
IsPreorder.trans (IsPartialOrder.isPreorder ≲-isPartialOrder) {k = ma} (⊥≲ma _) _ = ⊥≲ma ma
IsPreorder.trans (IsPartialOrder.isPreorder ≲-isPartialOrder) (ma≲ma .nothing) (⊥≲ma ma) = ⊥≲ma ma
IsPreorder.trans (IsPartialOrder.isPreorder ≲-isPartialOrder) (ma≲ma .ma) (ma≲ma ma) = ma≲ma ma
IsPartialOrder.antisym ≲-isPartialOrder (⊥≲ma _) (⊥≲ma _) = refl 
IsPartialOrder.antisym ≲-isPartialOrder (⊥≲ma _) (ma≲ma _) = refl
IsPartialOrder.antisym ≲-isPartialOrder (ma≲ma _) (⊥≲ma _) = refl
IsPartialOrder.antisym ≲-isPartialOrder (ma≲ma _) (ma≲ma _) = refl

lemma1 : ∀{A} → {a : A} → {ma : Maybe A} → just a ≲ ma → just a ≡ ma
lemma1 (ma≲ma .(just _)) = refl

Seq : Set → Set
Seq A = ℕ → Maybe A

IsMonotone : ∀{A} → Seq A → Set
IsMonotone {A} s = (n : ℕ) → (a : A) → s n ≲ s (ℕ.suc n)

IsStable : ∀{A} → Seq A → Set
IsStable {A} s = (n : ℕ) → (a : A) → (just a ≡ s n) → (s n ≡ s (ℕ.suc n))

_≐_ : ∀{ℓ ℓ' a} → {A : Set a} → Pred A ℓ → Pred A ℓ' → Set _
p ≐ q = (p ⊆ q) × (q ⊆ p)

monotone⇔stable : ∀{A} → IsMonotone {A} ≐ IsStable {A}
proj₁ monotone⇔stable {x = c} c-is-monotone n a p with c-is-monotone n a
... | p' with subst (_≲ c (ℕ.suc n)) (sym p) p'
... | p'' = trans (sym p) (lemma1 p'')

proj₂ monotone⇔stable {x = s} s-is-stable n a with s n | inspect s n
... | nothing | _ = ⊥≲ma (s (ℕ.suc n))
... | just x | [ eq ] with  s-is-stable n x (sym eq)
... | e with trans (sym eq) e 
... | e' = IsPreorder.reflexive (IsPartialOrder.isPreorder ≲-isPartialOrder) e'

Stable : Set → Set
Stable A = ∃ (IsStable {A})

never : ∀{A} → Stable A
never = ((λ _ → nothing) , λ _ _ _ → refl)

return : ∀{A} → A → Stable A
return a = ((λ _ → just a) , λ _ _ _ → refl)

_>>=_ : ∀{A B} → Stable A → (A → Stable B) → Stable B
_>>=_ {A} {B} (ca , acca) f = (cb , accb) where
  g : Maybe A → Stable B
  g (just a) = f a
  g nothing = never
  g' : ℕ → Stable B
  g' = g ∘ ca
  cb : Seq B
  cb n = proj₁ (g' n) n
  accb : IsStable cb
  accb n b p with ca n | inspect ca n | inspect g' n
  ... | just a | [ eq ] | [ eq2 ] =
    let d = (sym (cong (λ p → proj₁ p n) eq2 )) in
    let d' = trans p d in
    let p' = acca n a (sym eq) in
    let p'' : g (ca n) ≡ g (ca (ℕ.suc n))
        p'' = cong g p' in
    let p''' : proj₁ (g (ca n)) n ≡ proj₁ (g (ca n)) (ℕ.suc n)
        p''' = proj₂ (g' n) n b (trans p d) in
    let p'''' : proj₁ (g (ca n)) (ℕ.suc n) ≡ proj₁ (g (ca (ℕ.suc n))) (ℕ.suc n)
        p'''' =  cong (λ p → proj₁ p (ℕ.suc n)) p''  in
    let p''''' =  trans p''' p'''' in  trans d p'''''  
