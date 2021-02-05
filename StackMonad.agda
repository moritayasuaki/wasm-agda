module StackMonad where

import Category.Monad.Indexed
import Category.Monad
import Category.Applicative.Indexed
import Data.List as List
import Function
import Level
import Data.Fin as Fin
import Data.Unit as Unit
import Data.Product as Product
import Data.Sum as Sum



import Data.Nat as Nat
import Data.Bool as Bool
import Data.Empty as Empty
import Data.String as String
import Category.Monad.State using (IStateT ; StateTIMonad)
import Category.Monad.Continuation using (DContT ; DContIMonad)


module IList where
  open List using (List ; [] ; _∷_)
  open Product
  open Nat
  open Fin
  data IList {I : Set} (S : I → Set) : List I → Set where
    []  : IList S []
    _∷_ : ∀ {i is} → S i → IList S is → IList S (i ∷ is)

  split : ∀ {I} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is List.++ js) → IList S is × IList S js
  split [] ws = ([] , ws)
  split (i ∷ is) (v ∷ vs) = let vs , ws = split is vs
                             in v ∷ vs , ws

  take : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is List.++ js) → IList S is
  take is ws = proj₁ (split is ws)

  drop : ∀ {I : Set} {S : I → Set} → ∀ (is) → ∀ {js} → IList S (is List.++ js) → IList S js
  drop is ws = proj₂ (split is ws)

  dropn : ∀ {I : Set} {S : I → Set} → ∀ (n : ℕ) → ∀ {is} → IList S is → IList S (List.drop n is)
  dropn zero ws = ws
  dropn (suc n) (w ∷ ws) = dropn n ws
  dropn (suc n) [] = []

  _++_ : ∀ {I : Set} {S : I → Set} → ∀ {is js} → IList S is → IList S js → IList S (is List.++ js)
  [] ++ ws = ws
  (v ∷ vs) ++ ws = v ∷ (vs ++ ws)

  [_] : ∀ {I : Set} {S : I → Set} → ∀ {i} → S i → IList S List.[ i ]
  [_] v = v ∷ []

  lookup : ∀ {I : Set} {S : I → Set} → ∀ {is} → IList S is → (n : Fin (List.length is)) → S (List.lookup is n)
  lookup (v ∷ vs) zero = v
  lookup (v ∷ vs) (suc i) = lookup vs i

module IExc where
  open Fin
  open List
  data IExc {I : Set} (S : I → Set) : I → List I → Set where
    ret : ∀ {r rs} → S r → IExc S r rs
    exc : ∀ {r r' rs} → IExc S r' rs → IExc S r (r' ∷ rs)

  excn : {I : Set} {S : I → Set} {r : I} {rs : List I} → (n : Fin (length rs)) → S (lookup rs n) → IExc S r rs
  excn {_} {_} {_} {r ∷ rs} zero v = exc (ret v)
  excn {_} {_} {_} {r ∷ rs} (suc n) v = exc (excn n v)

module Monad where
  open IList using (IList ; [] ; _∷_)
  open Category.Monad.State
  open Category.Monad.Indexed
  open Category.Monad
  open Product
  open Unit
  open Fin
  open Nat
  open List using (List ; [] ; _∷_)

  StackT : {I : Set} → (I → Set) → (Set → Set) → (List I → List I → Set → Set)
  StackT S = IStateT (IList S)


  record RawIMonadStack {I : Set} (S : I → Set)
                        (M : List I → List I → Set → Set) : Set₁ where
    field
      monad : RawIMonad M
      pop1   : ∀ {i} → M (i ∷ []) [] (S i)
      push1  : ∀ {i} → S i → M [] (i ∷ []) ⊤
      up    : ∀ {X is js} → M is js X → ∀ {ks} → M (is List.++ ks) (js List.++ ks) X
    open RawIMonad monad public
  
    pop : ∀ {i is} → M (i ∷ is) is (S i)
    pop = up pop1
  
    push : ∀ {i is} → S i → M is (i ∷ is) ⊤
    push = λ v → up (push1 v)
  
    pop-list : ∀ is → ∀ {is'} → M (is List.++ is') is' (IList S is) 
    pop-list [] = return []
    pop-list (i ∷ is) = do v ← pop
                           vs ← pop-list is
                           return (v ∷ vs)
  
    push-list : ∀ {is is'} → IList S is →  M is' (is List.++ is') ⊤
    push-list [] = return tt
    push-list (v ∷ vs) = do push-list vs
                            push v
  
    drop : ∀ {is} → (n : Fin (List.length is)) → M is (List.drop (toℕ n) is) ⊤
    drop {i ∷ is} zero = return tt
    drop {i ∷ is} (suc n) = do pop
                               drop {is} n
  
    pop-nth : ∀ {is} → (n : Fin (List.length is)) → M is (List.drop (ℕ.suc (toℕ n)) is) (S (List.lookup is n))
    pop-nth {i ∷ is} zero = pop
    pop-nth {i ∷ is} (suc n) = do pop
                                  pop-nth {is} n
  
  StackTIMonadStack : {I : Set} (S : I → Set) {M : Set → Set}
                      → RawMonad M → RawIMonadStack S (StackT S M)
  StackTIMonadStack S Mon = record
    { monad = StateTIMonad (IList S) Mon
    ; pop1 = λ where (s ∷ []) → return (s , []) -- pop1 >> push1 x  ~ set1 x  / pop1 = get1 delete
    ; push1 = λ s [] → return (_ , s ∷ [])      -- pop1 >>= push1   ~ get1    / push1 = set1 ignore
    ; up = λ {_} {is} {_} f ss →
             do let vs , us = IList.split is ss
                x , ws ← f vs
                return (x , ws IList.++ us)
    } where open RawIMonad Mon
  
module Wasm where

  module Syntax where
    open Product
    open import Function.Identity.Categorical as Id using (Identity)
    
    module _ where
      open Bool hiding (not)
      open Nat
      open Unit
      open List hiding (and ; drop)
      open IList hiding (drop)
      open IExc

      data valtype : Set where
        bool : valtype
        nat : valtype
        unit : valtype
 
      resulttype : Set
      resulttype = List valtype

      data functype : Set where
        _⇒_ : resulttype → resulttype → functype

      data val : Set where
        cbool : Bool → val
        cnat : ℕ → val
        cunit : ⊤ → val

      vals : Set
      vals = List val

      data insn : Set where
        const : val → insn
        nop : insn
        not : insn
        and : insn
        add : insn
        sub : insn
        eqz : insn
        dup : insn
        drop : insn
        block : functype → List insn → insn
        if-else : functype → List insn → List insn → insn
        loop : functype → List insn → insn
        br : ℕ → insn
        br-if : ℕ → insn

      insns : Set
      insns = List insn

      infix 4 _%_
      data oresulttype : Set where
        _%_  : resulttype → List (resulttype × resulttype) → oresulttype

      infixr 3 _⇒_
      data ofunctype : Set where
        _⇒_ : resulttype → oresulttype → ofunctype

      -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
      data frame : Set where
        loopf : vals → resulttype → insn → resulttype → insns → frame
        blockf : vals → resulttype → insns → frame

      frames = List frame
      state = frames × vals × insns

    module _ where
      open String
      open List hiding (_++_)
      open import Data.Nat.Show as NS
      open import Data.Bool.Show as BS

      show-list-with-sep : ∀{X : Set} → (X → String) → String → List X → String
      show-list-with-sep show _ [] = ""
      show-list-with-sep show _ (x ∷ []) = show x
      show-list-with-sep show sep (x ∷ x' ∷ xs) = show x ++ sep ++ show-list-with-sep show sep (x' ∷ xs)

      concat-with-space : List String → String
      concat-with-space = show-list-with-sep (λ s → s) " "

      show-valtype : valtype → String
      show-valtype unit = "unit"
      show-valtype nat  = "int"
      show-valtype bool = "bool"

      show-val : val → String
      show-val (cunit tt) = "tt"
      show-val (cnat n) = NS.show n
      show-val (cbool b) = BS.show b
 
      show-resulttype : resulttype → String
      show-resulttype xs = "[" ++ (show-list-with-sep show-valtype " " xs) ++ "]"

      show-vals : vals → String
      show-vals vs = "[" ++ (show-list-with-sep show-val " " vs) ++ "]"

      show-functype : functype → String
      show-functype (a ⇒ b) = show-resulttype a ++ "⇒" ++ show-resulttype b

      mutual
        show-insns : insns → String
        show-insns [] = ""
        show-insns (i ∷ []) = show-insn i
        show-insns (i ∷ is) = show-insn i ++ " " ++ show-insns is
 
        show-insn : insn → String
        show-insn (const n) = concat-with-space ("const" ∷ show-val n ∷ [])
        show-insn nop = "nop"
        show-insn not = "not"
        show-insn and = "and"
        show-insn add = "add"
        show-insn sub = "sub"
        show-insn eqz = "eqz"
        show-insn dup = "dup"
        show-insn drop = "drop"
        show-insn (block ft is) = concat-with-space ("block" ∷ show-functype ft ∷ show-insns is ∷ "end" ∷ [])
        show-insn (if-else ft ist isf) = concat-with-space ("if" ∷ show-functype ft ∷ "then" ∷ show-insns ist ∷ "else" ∷ show-insns isf ∷ "end" ∷ [])
        show-insn (loop ft is) = concat-with-space ("loop" ∷ show-functype ft ∷ show-insns is ∷ "end" ∷ [])
        show-insn (br n) = concat-with-space ("br" ∷ NS.show n ∷ [])
        show-insn (br-if n) = concat-with-space ("br-if" ∷ NS.show n ∷ [])

      show-frame : frame → String
      show-frame (loopf vs a l b is) = show-vals vs ++ "ℓ" ++ show-functype (a ⇒ b) ++ "{" ++ show-insn l ++ "}" ++ "*" ++ show-insns is
      show-frame (blockf vs b is) = show-vals vs ++ "ℓ" ++ show-functype (b ⇒ b) ++ "{}" ++ "*" ++ show-insns is

      show-frames : frames → String
      show-frames fs = "[" ++ show-list-with-sep show-frame " " fs ++ "]"

      show-state : state → String
      show-state (fs , vs , is) = "(" ++ show-frames fs ++ ", " ++ show-vals vs ++ ", " ++ show-insns is ++ ")"


   
    

  module Interpreter where
    open Function 
    open String using (String)
    open Syntax 
    open Category.Monad
    open Sum
    open Product
    open Unit
    open List hiding (and)
    open Nat
    open Bool hiding (not)
    open Category.Monad.State

    import Data.Sum.Categorical.Left as Left
    module Error = Left (String × state) Level.zero
    error = Error.Sumₗ

    open Category.Monad.State
    E = IStateT (λ _ → state) error tt tt

    pattern ok a = inj₂ a
    pattern err a b = inj₁ (a , b)

    monad = StateTIMonad {_} {⊤} (λ _ → state) Error.monad 
    open RawMonad monad


    push : val → E ⊤
    push v (fs , vs , is) = ok (tt , fs , (v ∷ vs) , is)

    pop : E val
    pop (fs , v ∷ vs , is) = ok (v , fs , vs , is)
    pop st = err "value stack underflow" st

    typeof-val : val → valtype
    typeof-val (cbool _) = bool
    typeof-val (cnat _) = nat
    typeof-val (cunit _) = unit

    interp-valtype : valtype → Set
    interp-valtype bool = Bool
    interp-valtype nat = ℕ
    interp-valtype unit = ⊤

    interp-resulttype : resulttype → Set
    interp-resulttype ts = IList.IList interp-valtype ts

    encval : ∀{t} → interp-valtype t → val
    encval {bool} v = cbool v
    encval {unit} v = cunit v
    encval {nat} v = cnat v

    encvals : ∀{ts} → interp-resulttype ts → vals
    encvals IList.[] = []
    encvals (v IList.∷ vs) = encval v ∷ encvals vs

    _orelse_ : ∀ {X} → E X → E X → E X
    (ma orelse mb) st = ma st |> λ where
      (ok st') → ok st'
      (err _ _) → mb st 

    chkval : (t : valtype) → val → E (interp-valtype t)
    chkval bool (cbool b) = return b
    chkval nat (cnat n) = return n
    chkval unit (cunit tt) = return tt
    chkval t v st = err (concat-with-space $ show-val v ∷ "has type" ∷ show-valtype (typeof-val v) ∷ "instead of" ∷ show-valtype t ∷ []) st

    chkvals : (t : resulttype) → vals → E (interp-resulttype t × vals)
    chkvals (t ∷ ts) (v ∷ vs) = do
      v' ← chkval t v
      (vs' , rest) ← chkvals ts vs
      return (v' IList.∷ vs' , rest)
    chkvals [] vs = return (IList.[] , vs)
    chkvals (_ ∷ _) [] st = err "not enough elements in input" st

    popchk : (t : valtype) → E (interp-valtype t)
    popchk t = pop >>= chkval t

    popchks : (ts : resulttype) → E (interp-resulttype ts)
    popchks [] = return IList.[]
    popchks (t ∷ ts) = do
      v ← popchk t 
      vs ← popchks ts
      return $ v IList.∷ vs

    pushvs : vals → E ⊤
    pushvs [] = return tt
    pushvs (v ∷ vs) = push v >> pushvs vs

    fetch : E insn
    fetch (fs , vs , (i ∷ is)) = ok (i , fs , vs , is)
    fetch st = err "no instuction to fetch" st

    emit : insn → E ⊤
    emit i (fs , vs , is) = ok (tt , fs , vs , i ∷ is)

    enter : frame → E ⊤
    enter (blockf vs' b is') (fs , vs , is) = ok (tt , (blockf vs b is) ∷ fs , vs' , is')
    enter (loopf vs' a l b is') (fs , vs , is) = ok (tt , (loopf vs a l b is) ∷ fs , vs' , is')

    leave : E frame
    leave (((blockf vs b is) ∷ fs) , vs' , is') = ok ((blockf vs' b is') , fs , vs , is)
    leave (((loopf  vs a l b is) ∷ fs) , vs' , is') = ok ((loopf vs' a l b is') , fs , vs , is)
    leave st = err "control stack underflow" st

    br-helper : ℕ → E ⊤
    br-helper zero = do
      leave >>= λ where
        (blockf vs a _) → do
          vs' , _ ← chkvals a vs
          pushvs (encvals vs')
        (loopf vs a l _ _) → do
          vs' , _ ← chkvals a vs
          emit l
          pushvs (encvals vs')
    br-helper (suc n) = do
      vs ← leave >>= λ where
        (blockf vs _ _) → return vs
        (loopf vs _ _ _ _) → return vs
      pushvs vs
      br-helper n

    einsn : insn → E ⊤
    einsn (const v) = do push v
    einsn nop = return tt
    einsn and = do
      x ← popchk bool 
      y ← popchk bool
      push $ cbool $ x ∧ y
    einsn not = do
      x ← popchk bool
      push $ cbool $ Bool.not x
    einsn add = do
      x ← popchk nat
      y ← popchk nat
      push $ cnat $ x + y
    einsn sub = do
      x ← popchk nat
      y ← popchk nat
      push $ cnat $ x ∸ y
    einsn eqz = do
      zero ← popchk nat
        where suc _ → push $ cbool false
      push $ cbool true
    einsn dup = do
      v ← pop
      push v
      push v
    einsn drop = do
      pop
      return tt
    einsn (block (a ⇒ b) is) = do
      vs ← popchks a
      enter (blockf (encvals vs) b is)
    einsn (if-else (a ⇒ b) ist isf) = do
      p ← popchk bool
      vs ← popchks a
      if p then enter (blockf (encvals vs) b ist)
           else enter (blockf (encvals vs) b isf)
    einsn (loop (a ⇒ b) is) = do
      vs ← popchks a
      enter (loopf (encvals vs) a (loop (a ⇒ b) is) b is)

    einsn (br n) = br-helper n

    einsn (br-if n) = popchk bool >>= λ where
        false → return tt
        true → br-helper n

    eend : E ⊤
    eend = leave >>= λ where
        (blockf vs _ _) → do
          pushvs vs
        (loopf vs _ _ _ _) → do
          pushvs vs

    estep : E ⊤
    estep = (fetch >>= einsn) orelse eend

    terminated : E vals
    terminated ([] , vs , []) = ok (vs , [] , [] , [])
    terminated st = err "state is in evaluation" st

    estepn : ℕ → E vals
    estepn zero st = err "time out" st
    estepn (suc n) = terminated orelse (estep >> estepn n)

    show-result : error (vals × state) → String
    show-result (ok (vs , [] , [] , [])) = show-list-with-sep (λ x → x) ":" $ "success" ∷ show-vals vs ∷ []
    show-result (ok (_ , st)) = show-list-with-sep (λ x → x) ":" $ "cont" ∷ show-state st ∷ []
    show-result (err emesg st) = show-list-with-sep (λ x → x) ":" $ "error" ∷ emesg ∷  show-state st ∷ []

  module Example where
    open Product
    open List hiding (drop ; and ; _++_)
    open Syntax public
    open Interpreter
    open Bool hiding (not)
    open String

    ex0 ex1 ex2 ex3 ex4 : state
    ex0 = ([] , (cnat 1 ∷ cnat 2 ∷ []) , (add ∷ []))
    ex1 = ([] , (cbool true ∷ cnat 1 ∷ cnat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ nat ∷ []) [ add ] [ drop ]) ∷ []))
    ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (cnat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
    ex3 = ([] , [] , (drop ∷ []))
    ex4 = ([] , [] , (loop ([] ⇒ nat ∷ nat ∷ []) ([ br 0 ])) ∷ [])

    run-wasm : state → String
    run-wasm ex = show-state ex ++ " --> " ++ show-result (estepn 10 ex)

  module Typing where
    open String using (String)
    open Syntax 
    open Category.Monad
    open IExc
    open Sum
    open Product
    open List using (_∷_ ; [] ; [_] ; _++_)

    data tval : val → valtype → Set where
      tbool : ∀{b} → tval (cbool b) bool
      tnat : ∀{n} → tval (cnat n) nat
      tunit : tval (cunit Unit.tt) unit

    data tvals : vals → resulttype → Set where
      tbottom : tvals [] []
      tstack : ∀{v t vs ts} → tval v t → tvals vs ts → tvals (v ∷ vs) (t ∷ ts)

    mutual
      data tinsn : insn → ofunctype → Set where
        tconst : ∀{v t} → tval v t → tinsn (const v) ([] ⇒ [ t ] % [])
        tnop : tinsn nop ([] ⇒ [] % [])
        tnot : tinsn not ([ bool ] ⇒ [ bool ] % [])
        tand : tinsn and ((bool ∷ bool ∷ []) ⇒ [ bool ] % [])
        tadd : tinsn add ((nat ∷ nat ∷ []) ⇒ [ nat ] % [])
        tsub : tinsn sub ((nat ∷ nat ∷ []) ⇒ [ nat ] % [])
        teqz : tinsn eqz ([ nat ] ⇒ [ bool ] % [])
        tdup  : ∀{t} → tinsn dup ([ t ] ⇒ (t ∷ t ∷ []) % [])
        tdrop : ∀{t} → tinsn drop ([ t ] ⇒ [] % [])
        tblock : ∀{is a b} → tinsns is (a ⇒ b % [(b , b)])
                → tinsn (block (a ⇒ b) is) (a ⇒ b % [])
        tif-else : ∀{ist isf a b} → tinsns ist (a ⇒ b % [(b , b)]) → tinsns isf (a ⇒ b % [(b , b)])
                  → tinsn (if-else (a ⇒ b) ist isf) (a ⇒ b % [])
        tloop : ∀{is a b} → tinsns is (a ⇒ b % [(a , b)])
               → tinsn (loop (a ⇒ b) is) (a ⇒ b % [])
        tbr0 : ∀{a b c} → tinsn (br Nat.zero) (a ⇒ b % [(a , c)])
        tbrn : ∀{a x xs b c n} → tinsn (br n) (a ⇒ c % xs) → tinsn (br (Nat.suc n)) (a ⇒ b % (x ∷ xs))

        tup : ∀ {is a b d ls ls'} → tinsn is (a ⇒ b % ls ++ ls') → tinsn is (a ++ d ⇒ b ++ d % ls ++ ls') -- I'm not sure this is correct

      data tinsns : insns → ofunctype → Set where
        tempty : tinsns [] ([] ⇒ [] % [])
        tseq : ∀ {i is a b c ls} → tinsn i (a ⇒ b % ls) → tinsns is (b ⇒ c % ls) → tinsns (i ∷ is) (a ⇒ c % ls)

    data closed-tinsns : insns → functype → Set where
      closed : ∀{is a b} → tinsns is (a ⇒ b % []) → closed-tinsns is (a ⇒ b)

    
 
