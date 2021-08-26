module MaybeChain where

open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Relation.Binary
open import Data.Product 
open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Category.Monad
open import Category.Monad.Indexed

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

IsMaybeChain : ∀{A} → Seq A → Set
IsMaybeChain {A} s = (n : ℕ) → (a : A) → s n ≲ s (ℕ.suc n)

IsStable : ∀{A} → Seq A → Set
IsStable {A} s = (n : ℕ) → (a : A) → (just a ≡ s n) → (s n ≡ s (ℕ.suc n))

record _≐_ {ℓ ℓ' a} {A : Set a} (p : Pred A ℓ) (q : Pred A ℓ') : Set (a Level.⊔ ℓ Level.⊔ ℓ') where
  field
    ⇒ : p ⊆ q
    ⇐ : q ⊆ p

≐-swap : ∀{p q a} {A : Set a} {P : Pred A p} {Q : Pred A q} → P ≐ Q → Q ≐ P
≐-swap record { ⇒ = ⇒ ; ⇐ = ⇐ } = record { ⇒ = ⇐ ; ⇐ = ⇒ }
{-
_≐_ : ∀{ℓ ℓ' a} → {A : Set a} → Pred A ℓ → Pred A ℓ' → Set _
p ≐ q = (p ⊆ q) × (q ⊆ p)
-}

mchain⇔stable : ∀{A} → IsMaybeChain {A} ≐ IsStable {A}
_≐_.⇒ mchain⇔stable {x = c} c-is-monotone n a p with c-is-monotone n a
... | p' with subst (_≲ c (ℕ.suc n)) (sym p) p'
... | p'' = trans (sym p) (lemma1 p'')

_≐_.⇐ mchain⇔stable {x = s} s-is-stable n a with s n | inspect s n
... | nothing | _ = ⊥≲ma (s (ℕ.suc n))
... | just x | [ eq ] with  s-is-stable n x (sym eq)
... | e with trans (sym eq) e 
... | e' = IsPreorder.reflexive (IsPartialOrder.isPreorder ≲-isPartialOrder) e'

Stable : Set → Set
Stable A = ∃ (IsStable {A})


MaybeChain : Set → Set
MaybeChain A = ∃ (IsMaybeChain {A})

coerce : ∀{p q a} {A : Set a} → {P : Pred A p} {Q : Pred A q} → P ≐ Q → ∃ P → ∃ Q
coerce P⇔Q (a , p) = (a , _≐_.⇒ P⇔Q p)

toStable : ∀{A} → MaybeChain A → Stable A
toStable = coerce mchain⇔stable

toMaybeChain : ∀{A} → Stable A → MaybeChain A 
toMaybeChain = coerce (≐-swap mchain⇔stable)

never : ∀{A} → Stable A
never = ((λ _ → nothing) , λ _ _ _ → refl)

ret-stable : ∀{A} → A → Stable A
ret-stable a = ((λ _ → just a) , λ _ _ _ → refl)

bind-stable : ∀{A B} → Stable A → (A → Stable B) → Stable B
bind-stable {A} {B} (ca , acca) f = (cb , accb) where
  f'' : Maybe A → Stable B
  f'' (just a) = f a
  f'' nothing = never
  f' : ℕ → Stable B
  f' = f'' ∘ ca
  cb : Seq B
  cb n = proj₁ ((f'' ∘ ca) n) n
  accb : IsStable cb
  accb n b justb≡fan with ca n | inspect ca n | inspect f' n
  ... | just a | [ can≡justa ] | [ f'n≡fa ] =
    let fan≡f'nn : proj₁ (f a) n ≡ proj₁ (f' n) n
        fan≡f'nn = (sym (cong (λ p → proj₁ p n) f'n≡fa)) in
    let f'n≡f'n+1 : f' n ≡ f' (ℕ.suc n)
        f'n≡f'n+1 = cong f'' (acca n a (sym can≡justa)) in
    let f'nn≡f'nn+1 : proj₁ (f' n) n ≡ proj₁ (f' n) (ℕ.suc n)
        f'nn≡f'nn+1 = proj₂ (f' n) n b (trans justb≡fan fan≡f'nn) in
    let f'nn+1≡f'n+1n+1 : proj₁ (f' n) (ℕ.suc n) ≡ proj₁ (f' (ℕ.suc n)) (ℕ.suc n)
        f'nn+1≡f'n+1n+1 =  cong (λ p → proj₁ p (ℕ.suc n)) f'n≡f'n+1 in
    let fan≡f'n+1n+1 : proj₁ (f a) n ≡ proj₁ (f' (ℕ.suc n)) (ℕ.suc n)
        fan≡f'n+1n+1 = trans fan≡f'nn (trans f'nn≡f'nn+1 f'nn+1≡f'n+1n+1) in fan≡f'n+1n+1


maybeChainMonad : RawMonad MaybeChain
RawIMonad.return maybeChainMonad a = toMaybeChain (ret-stable a)
RawIMonad._>>=_ maybeChainMonad m f = toMaybeChain (bind-stable (toStable m) (λ a → toStable (f a)))
