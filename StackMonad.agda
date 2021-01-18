module StackMonad where

open import Data.Fin
open import Category.Monad.Indexed
open import Category.Monad
open import Category.Applicative.Indexed
open import Data.List hiding(and)
open import Function
open import Level
open import Data.Unit
open import Data.Product
open import Data.Maybe hiding(_>>=_)
open import Data.Nat renaming (suc to nsuc)

module IList where
  data IList {I : Set} (S : I → Set) : List I → Set where
    []  : IList S []
    _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

  isplit : ∀ {I} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is ++ js) → IList S is × IList S js
  isplit [] ws = ([] , ws)
  isplit (i ∷ is) (v ∷ vs) = let vs , ws = isplit is vs
                             in v ∷ vs , ws

  itake : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is ++ js) → IList S is
  itake is ws = proj₁ (isplit is ws)

  idrop : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is ++ js) → IList S js
  idrop is ws = proj₂ (isplit is ws)

  _i++_ : ∀ {I : Set} {S : I → Set} → ∀ {is js} → IList S is → IList S js → IList S (is ++ js)
  [] i++ ws = ws
  (v ∷ vs) i++ ws = v ∷ (vs i++ ws)

open IList hiding (idrop ; itake)

StackT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
StackT S M i j A = IList S i → M (A × IList S j)

module ListFin where
  open import Relation.Binary.PropositionalEquality
  variable
    X : Set
    xs xs' xs'' : List X
    x : X
  lookup-split : (xs : List X) → (n : Fin (length xs)) → ∃ λ ((xs' , x , xs'') : List X × X × List X) → (x ≡ lookup xs n) × (x ∷ xs'' ≡ drop (toℕ n) xs) × (xs' ≡ take (toℕ n) xs) × (xs' ++ (x ∷ xs'') ≡ xs)
  lookup-split (x ∷ xs) zero = ([] , x , xs) , (refl , refl , refl , refl)
  lookup-split (x' ∷ xs) (suc n) with lookup-split xs n
  ...                               | (xs' , x , xs'') , (refl , p , q , r) = (x' ∷ xs' , x , xs'') , (refl , p , cong (x' ∷_ ) q , cong (x' ∷_ ) r)

open ListFin

record RawIMonadStack {I : Set} (S : I → Set)
                      (M : List I → List I → Set → Set) : Set₁ where
  field
    monad : RawIMonad M
    pop1   : ∀ {i} → M (i ∷ []) [] (S i)
    push1  : ∀ {i} → S i → M [] (i ∷ []) ⊤
    up    : ∀ {X is js} → M is js X → ∀ {ks} → M (is ++ ks) (js ++ ks) X
  open RawIMonad monad public

  pop : ∀ {i is} → M (i ∷ is) is (S i)
  pop = up pop1

  push : ∀ {i is} → S i → M is (i ∷ is) ⊤
  push = λ v → up (push1 v)

  pop-i : ∀ is' → ∀ {is''} → M (is' ++ is'') is'' (IList S is')
  pop-i [] = return []
  pop-i (i ∷ is) = do v ← pop
                      vs ← pop-i is
                      return (v ∷ vs)

  open import Relation.Binary.PropositionalEquality
  open import Data.List.Properties

  pop-n : ∀ n → ∀ {is} → M is (drop n is) (IList S (take n is))
  pop-n n {is} = subst (λ t → M t is'' (IList S is')) (take++drop n is) m
    where is'  = take n is
          is'' = drop n is
          m  = pop-i is' {is''}

  drop-n : ∀ n → ∀ {is} → M is (drop n is) ⊤
  drop-n n = pop-n n >> return tt

  drop-fin : ∀ {is} → (n : Fin (length is)) → M is (drop (toℕ n) is) ⊤
  drop-fin {i ∷ is} zero = return tt
  drop-fin {i ∷ is} (suc n) = pop >> drop-fin {is} n

  pop-fin : ∀ {is} → (n : Fin (length is)) → M is (drop (nsuc (toℕ n)) is) (S (lookup is n))
  pop-fin {i ∷ is} zero = pop
  pop-fin {i ∷ is} (suc n) = pop >> pop-fin {is} n

RawIMonadT' : ∀ {I J : Set} (T : (I → I → Set → Set) → (J → J → Set → Set)) → Set₁
RawIMonadT' T = ∀ {M} → RawIMonad M → RawIMonad (T M)

StackTIMonad : {I : Set} → ∀ (S : I → Set) {M} → RawMonad M → RawIMonad (StackT S M)
StackTIMonad S Mon  = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  } where open RawMonad Mon

StackTIMonadStack : {I : Set} (S : I → Set) {M : Set → Set}
                    → RawMonad M → RawIMonadStack S (StackT S M)
StackTIMonadStack S Mon = record
  { monad = StackTIMonad S Mon
  ; pop1 = λ where (s ∷ []) → return (s , [])
  ; push1 = λ s [] → return (_ , s ∷ [])
  ; up = λ {_} {is} {_} f ss →
           do let vs , us = isplit is ss
              x , ws ← f vs
              return (x , ws i++ us)
  } where open RawIMonad Mon

module Example where

open import Data.Bool using (Bool ; _∧_) renaming (not to bool-not)
open import Data.Nat

data valtype : Set where
  bool : valtype
  nat : valtype
  unit : valtype

val : valtype -> Set
val bool = Bool
val nat = ℕ
val unit = ⊤

opds = IList val

resulttype = List valtype 

open import Function.Identity.Categorical as Id using (Identity)
OpdStack = StackT val Identity

record blkctxtype : Set where
  field
    opt-inputtype : Maybe resulttype
    outputtype : resulttype
    frametype : resulttype
    ctx-outputtype : resulttype

  ctx-inputtype : resulttype
  ctx-inputtype = outputtype ++ frametype

  labeltype : resulttype
  labeltype with opt-inputtype
  ...          | just inputtype = inputtype
  ...          | nothing = outputtype

record blkctx (bt : blkctxtype) : Set where
  open blkctxtype bt
  field
    ctx-label : OpdStack labeltype outputtype ⊤
    ctx-end : OpdStack ctx-inputtype ctx-outputtype ⊤

ctrlstacktype = List blkctxtype

module OpdM = RawIMonadStack (StackTIMonadStack val Id.monad)
CtrlStack = StackT blkctx Identity

module CtrlM = RawIMonadStack (StackTIMonadStack blkctx Id.monad)

and : OpdStack (bool ∷ bool ∷ []) [ bool ] ⊤
and = do b₁ ← pop
         b₂ ← pop
         push (b₁ ∧ b₂)
         where open OpdM

not : OpdStack [ bool ] [ bool ] ⊤
not = do b ← pop
         push (bool-not b)
         where open OpdM

br : ∀ {cs} → (n : Fin (length cs)) → CtrlStack cs (drop (nsuc (toℕ n)) cs) (OpdStack (blkctxtype.labeltype (lookup cs n)) (blkctxtype.outputtype (lookup cs n)) ⊤)
br n = do ctx ← pop-fin n
          return (blkctx.ctx-label ctx)
       where open CtrlM

end : ∀ {c cs} → CtrlStack (c ∷ cs) cs (OpdStack (blkctxtype.ctx-inputtype c) (blkctxtype.ctx-outputtype c) ⊤)
end = do ctx ← pop
         return (blkctx.ctx-end ctx)
       where open CtrlM

to-loop-ctxtype : resulttype → resulttype → blkctxtype
blkctxtype.opt-inputtype (to-loop-ctxtype intyp _) = just intyp
blkctxtype.outputtype (to-loop-ctxtype _ outtyp) = outtyp
blkctxtype.frametype (to-loop-ctxtype _ _) = []
blkctxtype.ctx-outputtype (to-loop-ctxtype _ _) = []

to-blk-ctxtype : resulttype → resulttype → blkctxtype
blkctxtype.opt-inputtype (to-blk-ctxtype intyp _) = nothing
blkctxtype.outputtype (to-blk-ctxtype _ outtyp) = outtyp
blkctxtype.frametype (to-blk-ctxtype _ _) = []
blkctxtype.ctx-outputtype (to-blk-ctxtype _ _) = []

-- block : ∀ {cs} → (intyp outtyp : resulttype) → CtrlStack ((to-blk-ctxtype intyp outtyp) ∷ cs) ((to-blk-ctxtype intyp outtyp) ∷ cs) ⊤ → CtrlStack cs ((to-blk-ctxtype intyp outtyp) ∷ cs) ⊤
-- block intyp outyp m = _

