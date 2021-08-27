module MiniWasm where

open import Data.Integer as Int using (ℤ)
open import Data.Nat as Nat
open import Data.Bool as Bo hiding (not)
open import Data.Unit
open import Data.Product
open import Data.List hiding (and)
module Syntax (Var : Set) where
  data InsnGroup : Set where
    arith : InsnGroup
    logic : InsnGroup
    store : InsnGroup
    control : InsnGroup

  Code : Set

  data Insn : Set where
    const : ℤ → Insn
    load : Var → Insn
    store : Var → Insn
    add : Insn
    mul : Insn
    and : Insn
    not : Insn
    nop : Insn
    br : (l : ℕ) → Insn
    brif : (l : ℕ) → Insn
    block : (a r : ℕ) → (is : Code) → Insn
    loop : (a r : ℕ) → (is : Code) → Insn

  Code = List Insn

module Typing (Var : Set) where
    open Syntax Var
    open import Relation.Binary.PropositionalEquality
    private
      variable
        e e' : List ℕ -- type for block context
        l : ℕ -- block height
        v : Var -- varibale name
        z : ℤ -- integer value
        a r a' r' : ℕ -- operand type argument and result
        i : Insn -- an instruction
        is : Code -- sequence of instructions
    infixl 1 _hasType_
    infixr 1 _hasMinType_
    record Type : Set where
      constructor Ty
      field
        arg : ℕ
        res : ℕ
        blk : List ℕ
    data _hasType_ : Code → Type → Set
    data _hasMinType_ : Insn → Type → Set where
      tconst : const z hasMinType Ty 0 1 []
      tload  :  load v hasMinType Ty 1 1 []
      tstore : store v hasMinType Ty 2 0 []
      tnop   :     nop hasMinType Ty 0 0 []
      tnot   :     not hasMinType Ty 1 1 []
      tand   :     and hasMinType Ty 2 1 []
      tmul   :     mul hasMinType Ty 2 1 []
      tadd   :     add hasMinType Ty 2 1 []
      tbr    :
        (l ≡ length e) →
        br l hasMinType Ty a r (e ++ (a ∷ []))
      tbrif  : 
        (l ≡ length e) →
        brif l hasMinType Ty a r (e ++ (a ∷ []))
      tblock :
        is hasType Ty a r (r ∷ e) →
        block a r is hasMinType Ty a r e
      tloop  : 
        is hasType Ty a r (a ∷ e) →
        loop a r is hasMinType Ty a r e

    data _hasType_ where
      [] : [] hasType Ty r r e
      _∷_ : (d : ℕ) → (f : List ℕ) →
        r + d ≡ a' → e ++ f ≡ e' →
        i hasMinType Ty a r e →
        is hasType Ty a' r' e' → 
        i ∷ is hasType Ty (a + d) (r' + d) e'

module Semantics (Var : Set) where
    open Syntax Var
    open Typing Var
    open import Data.Maybe
    cast : ℤ → Bool
    cast Int.+0 = false
    cast _ = true

    cast' : Bool → ℤ
    cast' false = Int.+0
    cast' true = Int.1ℤ

    module Unsafe where
      Store = Var → ℤ
      OpeStk = List ℤ
      Cont = Store × OpeStk → Maybe (Store × OpeStk)
      CtrlStk = List Cont
      SemanticDomain = CtrlStk → (Cont → Cont)

    module Safe where
      Store = Var → ℤ

      open import Data.Vec as VecM
      OpeStk : ℕ → Set
      OpeStk n = Vec ℕ n

      Cont : ℕ → ℕ → ℕ → Set
      Cont l n r = Store × OpeStk n → Maybe (Store × OpeStk r)

      open import Data.List as ListM hiding (and)

      CtrlStk : List ℕ → ℕ → Set
      CtrlStk [] r = ⊤
      CtrlStk (n ∷ ns) r = Cont (ListM.length ns) n r × CtrlStk ns r
      open import Data.Nat
      SemanticDomain : Type → Set
      SemanticDomain (Ty a r e) = CtrlStk e r → (Cont zero r r → Cont zero a r)
      open import Function hiding (const)
      [[_]] : (code : Code) → (type : Type) → (code hasType type) → SemanticDomain type
      [[ [] ]] (Ty arg .arg blk) [] ctrlstk = id
      [[ Syntax.const z ∷ is ]] (Typing.Ty .d .(_ + d) blk) ((d Typing.∷ f) r+d≡a' e++f≡blk Typing.tconst proof) ctrlstk cont (st , opestk) = cont (st , {!   !})
      [[ load x ∷ is ]] (Ty .(suc d) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tload proof) ctrlstk = {!   !}
      [[ store x ∷ is ]] (Ty .(suc (suc d)) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tstore proof) ctrlstk = {!   !}
      [[ .nop ∷ is ]] (Ty .d .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tnop proof) ctrlstk = {!   !}
      [[ .not ∷ is ]] (Ty .(suc d) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tnot proof) ctrlstk = {!   !}
      [[ .and ∷ is ]] (Ty .(suc (suc d)) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tand proof) ctrlstk = {!   !}
      [[ .mul ∷ is ]] (Ty .(suc (suc d)) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tmul proof) ctrlstk = {!   !}
      [[ .add ∷ is ]] (Ty .(suc (suc d)) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk tadd proof) ctrlstk = {!   !}
      [[ .(br _) ∷ is ]] (Ty .(_ + d) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk (tbr x) proof) ctrlstk = {!   !}
      [[ .(brif _) ∷ is ]] (Ty .(_ + d) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk (tbrif x) proof) ctrlstk = {!   !}
      [[ .(block _ _ _) ∷ is ]] (Ty .(_ + d) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk (tblock x) proof) ctrlstk = {!   !}
      [[ .(loop _ _ _) ∷ is ]] (Ty .(_ + d) .(_ + d) blk) ((d ∷ f) r+d≡a' e++f≡blk (tloop x) proof) ctrlstk = {!   !}