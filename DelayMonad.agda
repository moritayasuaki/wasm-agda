{-# OPTIONS --guardedness #-}
module DelayMonad where

open import Category.Monad
open import Category.Monad.Indexed

record ∞Delay (A : Set) : Set
data Delay (A : Set) : Set

data Delay A where
  now : A → Delay A
  later : ∞Delay A → Delay A

record ∞Delay A where
  constructor thunk
  coinductive
  field
    force : Delay A

module _ where 
  open Category.Monad.Indexed.RawIMonad
  
  monadDelay : RawMonad Delay
  monad∞Delay : RawMonad ∞Delay

  return monadDelay x = now x
  _>>=_ monadDelay x f = later (_>>=_ monad∞Delay (thunk x)  λ x → thunk (f x)) 

  return monad∞Delay x = record { force = now x }
  ∞Delay.force ((monad∞Delay >>= x) f) = _>>=_ monadDelay (later x) λ x → later (f x)
