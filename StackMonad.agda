module StackMonad where

open import Data.Fin
open import Category.Monad.Indexed
open import Category.Monad
open import Category.Applicative.Indexed
import Data.List as L
open import Function
open import Level
open import Data.Unit
open import Data.Product
open import Data.Maybe hiding(_>>=_)
open import Data.Nat renaming (suc to nsuc)
open import Category.Monad.State using (IStateT ; StateTIMonad)
open import Category.Monad.Continuation using (DContT ; DContIMonad)

open L using (List ; [] ; _∷_ )

module IList where
  data IList {I : Set} (S : I → Set) : List I → Set where
    []  : IList S []
    _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

  split : ∀ {I} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is L.++ js) → IList S is × IList S js
  split [] ws = ([] , ws)
  split (i ∷ is) (v ∷ vs) = let vs , ws = split is vs
                             in v ∷ vs , ws

  take : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is L.++ js) → IList S is
  take is ws = proj₁ (split is ws)

  drop : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is L.++ js) → IList S js
  drop is ws = proj₂ (split is ws)

  _++_ : ∀ {I : Set} {S : I → Set} → ∀ {is js} → IList S is → IList S js → IList S (is L.++ js)
  [] ++ ws = ws
  (v ∷ vs) ++ ws = v ∷ (vs ++ ws)

  [_] = 

module I = IList
open I using (IList ; [] ; _∷_)

StackT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
StackT {I} S = IStateT (IList S)

record RawIMonadStack {I : Set} (S : I → Set)
                      (M : List I → List I → Set → Set) : Set₁ where
  field
    monad : RawIMonad M
    pop1   : ∀ {i} → M (i ∷ []) [] (S i)
    push1  : ∀ {i} → S i → M [] (i ∷ []) ⊤
    up    : ∀ {X is js} → M is js X → ∀ {ks} → M (is L.++ ks) (js L.++ ks) X
  open RawIMonad monad public

  pop : ∀ {i is} → M (i ∷ is) is (S i)
  pop = up pop1

  push : ∀ {i is} → S i → M is (i ∷ is) ⊤
  push = λ v → up (push1 v)


  drop : ∀ {is} → (n : Fin (L.length is)) → M is (L.drop (toℕ n) is) ⊤
  drop {i ∷ is} zero = return tt
  drop {i ∷ is} (suc n) = do pop
                             drop {is} n

  pop-nth : ∀ {is} → (n : Fin (L.length is)) → M is (L.drop (nsuc (toℕ n)) is) (S (L.lookup is n))
  pop-nth {i ∷ is} zero = pop
  pop-nth {i ∷ is} (suc n) = do drop
                                pop-nth {is} n

StackTIMonadStack : {I : Set} (S : I → Set) {M : Set → Set}
                    → RawMonad M → RawIMonadStack S (StackT S M)
StackTIMonadStack S Mon = record
  { monad = StateTIMonad (IList S) Mon
  ; pop1 = λ where (s ∷ []) → return (s , [])
  ; push1 = λ s [] → return (_ , s ∷ [])
  ; up = λ {_} {is} {_} f ss →
           do let vs , us = I.split is ss
              x , ws ← f vs
              return (x , ws I.++ us)
  } where open RawIMonad Mon

BlkCtxT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
BlkCtxT K = DContT (IList S)

record RawIMonadBlkCtx {I : Set} (K : I → Set)
                       (M : I → I → Set → Set) : Set₁ where
  field
    monad : RawIMonad M
    leave1 : ∀ {i j} → M (i ∷ []) (j ∷ []) (K (j ∷ [])) → M [] [] (K i) -- C[∘]   [block {... } ...] , E[ε] → E'[sdf ]
    enter1 : ∀ {a i j k} →
            ((a → M (j ∷ []) (j ∷ []) (K (i ∷ []))) → M (j ∷ []) (k ∷ []) (K (k ∷ []))) → M (j ∷ []) (i ∷ []) a

[ [ [ ]r2 ]r1 r1]

(((r2 -> r1) -> r1)) -> ((r4 -> r4) -> r3) -> r2 -> r3
block r2 r1   ...   (block r4 r3) ...  ->  

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
  ctx-inputtype = outputtype L.++ frametype

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

and : OpdStack (bool ∷ bool ∷ []) L.[ bool ] ⊤
and = do b₁ ← pop
         b₂ ← pop
         push (b₁ ∧ b₂)
         where open OpdM

not : OpdStack L.[ bool ] L.[ bool ] ⊤
not = do b ← pop
         push (bool-not b)
         where open OpdM

br : ∀ {cs} → (n : Fin (L.length cs)) → CtrlStack cs (L.drop (nsuc (toℕ n)) cs) (OpdStack (blkctxtype.labeltype (L.lookup cs n)) (blkctxtype.outputtype (L.lookup cs n)) ⊤)
br n = do ctx ← pop-nth n
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

