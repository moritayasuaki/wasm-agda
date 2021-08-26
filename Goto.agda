module Goto where

module Syntax where
  open import Data.Integer using (ℤ)
  data Ops (Var : Set) : Set where
    const : ℤ → Ops Var
    load : Var → Ops Var
    add : Var → Var → Ops Var
    mul : Var → Var → Ops Var
    and : Var → Var → Ops Var
    not : Var → Ops Var

  data Stmt (Var : Set) : Set where
    nop : Stmt Var
    _:=_ : Var → Ops Var → Stmt Var


  data Stmts (Label : Set) (Var : Set) : Set where
    _∷_ : Stmt Var → Stmts Label Var → Stmts Label Var
    goto : Label → Stmts Label Var
    gotoif : Var → Label → Label → Stmts Label Var
    ret : Stmts Label Var


  Code : Set → Set → Set
  Code Label Var = Label → Stmts Label Var

module Semantics where
  open import Data.Integer using (ℤ ; +0 ; _+_ ; _*_ ; 1ℤ)
  open import Function using (_∘_ ; _|>_)
  open import Level using (Level)
  open import Data.Product using (_,_ ; _×_)
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat using (suc ; zero ; ℕ)
  open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_) renaming (not to bnot)

  open Syntax

  cast : ℤ → Bool
  cast +0 = false
  cast _ = true

  cast' : Bool → ℤ
  cast' false = +0
  cast' true = 1ℤ

  Store : Set → Set
  Store Var = Var → ℤ

  Config : Set → Set → Set
  Config Label Var = Code Label Var × Stmts Label Var × Store Var

  evalops : ∀{Var} → Ops Var → Store Var → ℤ
  evalops (Ops.const z) s = z
  evalops (load x) s = s x
  evalops (add x y) s = s x + s y
  evalops (mul x y) s = s x * s y
  evalops (and x y) s = cast' (cast (s x) ∧ cast (s y))
  evalops (not x) s = cast' (bnot (cast (s x)))

--  open import DelayMonad
  open import Category.Monad.State
  open import Data.Sum
  open import Function
  open import Relation.Binary
  open import Relation.Nullary.Decidable

  open Level
  module _ {ℓ : Level} {Var : Set} {_==_ : Rel Var ℓ} (isDeq : IsDecEquivalence _==_) where

    _≈_ : Rel (Store Var) _ 
    s ≈ s' = (x : Var) → s x ≡ s' x

    _[_↦_] : Store Var → Var → ℤ → Store Var
    _[_↦_] s x z x' = if isYes (x ≟ x') then z else s x' where open IsDecEquivalence isDeq

    transition : ∀{Label} → Config Label Var → Config Label Var
    transition (c , nop ∷ is , s) = (c , is , s) -- TODO define net effects for each i
    transition (c , (x := ops) ∷ is , s) = (c , is , _[_↦_] s x (evalops ops s))
    transition (c , goto ℓ , s) = (c , c ℓ , s)
    transition (c , gotoif x ℓ ℓ' , s) = cast (s x) |> λ where
      true → (c , goto ℓ , s)
      false → (c , goto ℓ' , s)
    transition (c , ret , s) = (c , ret , s)

    small-step : ∀{Label} → Config Label Var → Config Label Var ⊎ Store Var
    small-step (c , nop ∷ is , s) = inj₁ (c , is , s)
    small-step (c , (x := ops) ∷ is , s) = inj₁ (c , is , _[_↦_] s x (evalops ops s))
    small-step (c , goto ℓ , s) = inj₁ (c , c ℓ , s)
    small-step (c , gotoif x ℓ ℓ' , s) = cast (s x) |> λ where
      true → inj₁ (c , goto ℓ , s)
      false → inj₁ (c , goto ℓ' , s)
    small-step (c , ret , s) = inj₂ s

    open import CPPO

    open import Data.Unit
    open import Data.Product

    -- monadic semantics by TraceT 
    module TraceT {Label : Set} (start : Label) where
      open import Trace
      open import Data.Empty
      open import Data.Maybe
      open import Data.Sum.Relation.Binary.LeftOrder
      open import Relation.Binary.Morphism
      import Data.Maybe.Categorical as MaybeC
      import Data.Sum.Categorical.Left as LeftC
      import Function.Identity.Categorical as IdC
      module Left = LeftC (Store Var → Config Label Var) Level.zero

      T = (StateT (Store Var) ∘ (_∘′ Maybe) ∘ OTraceT) IdC.Identity
      _ = {! T  !}

      -- ⟦_⟧ : Code Label Var → TraceT (ℕ → Store Var → (ℕ →Store Var)

    -- monadic semantics by partiality monad
    module Partiality {Label : Set} (start : Label) where
      open import Codata.Musical.Notation
      open import Category.Monad.Partiality
      ⟦_⟧ :  Code Label Var → StateT (Store Var) _⊥ ⊤
      ⟦ c ⟧ s = go (c , c start , s) where
        go : (Config Label Var) → (⊤ × Store Var) ⊥
        go a = (small-step a) |> λ where
          (inj₁ a) → later (♯ (go a))
          (inj₂ x) → now (tt , x)
