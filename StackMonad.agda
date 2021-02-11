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

      infix 4.5 _⇒_
      record functype {X : Set} : Set where
        constructor _⇒_
        field
          input : resulttype
          output : X

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
        block : functype {resulttype} → List insn → insn
        if-else : functype {resulttype} → List insn → List insn → insn
        loop : functype {resulttype} → List insn → insn
        br : ℕ → insn
        br-if : ℕ → insn

      insns : Set
      insns = List insn

      -- we take resulttype as value stack instead of taking sequence of const instruction (so innermost block context does not include value and insts)
      frame : Set
      frame = vals × Nat.ℕ × insn × insns

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
        show-insns is = "[" ++ go is ++ "]" where
          go : insns → String
          go [] = ""
          go (i ∷ []) = show-insn i
          go (i ∷ is) = show-insn i ++ " " ++ show-insns is
 
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
        show-insn (block ft is) = concat-with-space ("block" ∷ show-functype ft ∷ show-insns is ∷ [])
        show-insn (if-else ft ist isf) = concat-with-space ("if" ∷ show-functype ft ∷ show-insns ist ∷ show-insns isf ∷ [])
        show-insn (loop ft is) = concat-with-space ("loop" ∷ show-functype ft ∷ show-insns is ∷ [])
        show-insn (br n) = concat-with-space ("br" ∷ NS.show n ∷ [])
        show-insn (br-if n) = concat-with-space ("br-if" ∷ NS.show n ∷ [])

      show-frame : frame → String
      show-frame (vs , a , l , is) = show-vals vs ++ "ℓ" ++ NS.show a ++ "{" ++ show-insn l ++ "}" ++ "*" ++ show-insns is

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

    append : vals → E ⊤
    append vs' (fs , vs , is) = ok (tt , fs , vs' ++ vs , is)

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

    infixl 4 _<|>_
    _<|>_ : ∀ {X} → E X → E X → E X
    (ma <|> mb) st = ma st |> λ where
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
    enter (vs' , a , l , is') (fs , vs , is) = ok (tt , (vs , a , l , is) ∷ fs , vs' , is')

    leave : E frame
    leave ((vs , a , l , is) ∷ fs , vs' , is') = ok ((vs' , a , l , is') , fs , vs , is)
    leave st = err "control stack underflow" st

    br-helper : ℕ → E ⊤
    br-helper zero = do
      vs , a , _ , _ ← leave
      append (take a vs)
    br-helper (suc n) = do
      vs , _ , _ , _ ← leave
      append vs
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
      enter (encvals vs , length b , nop , is)
    einsn (if-else (a ⇒ b) ist isf) = do
      p ← popchk bool
      vs ← popchks a
      if p then enter (encvals vs , length b , nop , ist)
           else enter (encvals vs , length b , nop , isf)
    einsn (loop (a ⇒ b) is) = do
      vs ← popchks a
      enter (encvals vs , length a , loop (a ⇒ b) is , is)

    einsn (br n) = br-helper n

    einsn (br-if n) = popchk bool >>= λ where
        false → return tt
        true → br-helper n

    eend : E ⊤
    eend = do
      vs , _ , _ , _ ← leave
      append vs

    estep : E ⊤
    estep ([] , vs , []) = ok (tt , [] , vs , [])
    estep (fs , vs , []) = eend (fs , vs , [])
    estep (fs , vs , is) = (fetch >>= einsn) (fs , vs , is)

    eval1 : state → error state
    eval1 st with estep st
    ...         | ok (_ , st') = ok st'
    ...         | err emsg st' = err emsg st'

  module Example where
    open Product
    open List hiding (drop ; and ; _++_)
    open Syntax public
    open Interpreter
    open Bool hiding (not)
    open String
    open Nat

    ex0 ex1 ex2 ex3 ex4 : state
    ex0 = ([] , (cnat 1 ∷ cnat 2 ∷ []) , (add ∷ []))
    ex1 = ([] , (cbool true ∷ cnat 1 ∷ cnat 0 ∷ []) , ( not ∷ (if-else (nat ∷ nat ∷ [] ⇒ [ nat ]) [ add ] [ drop ]) ∷ []))
    ex2 = ([] , [] , (block ([] ⇒ [ nat ]) (const (cnat 1) ∷ block ([ nat ] ⇒ [ nat ]) (br 1 ∷ []) ∷ []) ∷ []))
    ex3 = ([] , [] , (drop ∷ []))
    ex4 = ([] , [] , (loop ([] ⇒ nat ∷ nat ∷ []) ([ br 0 ])) ∷ [])
    ex5 = ([] , [] , const (cnat 1))

    evaln : state → ℕ → error vals
    evaln ([] , vs , []) _ = ok vs
    evaln st zero = err "time out" st
    evaln st (suc n) with eval1 st
    ...                 | ok st' = evaln st' n
    ...                 | (err emsg st') = err emsg st'

    show-result : error vals → String
    show-result (ok vs) = show-vals vs
    show-result (err emesg st) = show-list-with-sep (λ x → x) ": " (show-state st ∷ emesg ∷ [])

    show-eval : state → String
    show-eval ex = show-state ex ++ " ↪* " ++ show-result (evaln ex 1024)

    run : List String
    run = List.map show-eval (ex0 ∷ ex1 ∷ ex2 ∷ ex3 ∷ ex4 ∷ ex5 ∷ [])

  module TInterpreter where

  module Typing where
    open String using (String)
    open Syntax 
    open Category.Monad
    open IExc
    open Sum
    open Product
    open Fin
    open List using (_∷_ ; [] ; [_] ; _++_ ; length ; lookup ; List)
    open functype


    labelstype = List resulttype

    infix 4.9 _/_ 
    record lresulttype : Set where
      constructor _/_
      field
        main : resulttype
        labels : labelstype

    infix 4.5 _↠_
    record ctxtype {X : Set} : Set where
      constructor _↠_
      field
        delim : X
        answer : resulttype

    record scopetype : Set where
      constructor sc
      field
        vstacktype : resulttype
        outputtype : resulttype

    record frametype : Set where
      constructor fr
      field
        vstacktype : resulttype
        labeltype : resulttype
        outputtype : resulttype

    infix 2 _∈-v_
    infix 2 _∈-vs_
    infix 2 _∈-i_
    infix 2 _∈-is_
    infix 2 _∈-li_
    infix 2 _∈-lis_
    infix 2 _∈-fs_
    infix 2 _∈-s_
    data _∈-v_ : val → valtype → Set where
      tbool : ∀{b} → cbool b ∈-v bool
      tnat : ∀{n} → cnat n ∈-v nat
      tunit : cunit Unit.tt ∈-v unit

    data _∈-vs_ : vals → resulttype → Set where
      tvempty : [] ∈-vs []
      tvstack : ∀{v t vs ts} → v ∈-v t → vs ∈-vs ts → v ∷ vs ∈-vs t ∷ ts

    data _∈-i_ : insn → functype → Set where
      tconst : ∀{v t} → v ∈-v t → const v ∈-i [] ⇒ [ t ]
      tnop : nop ∈-i [] ⇒ []
      tnot : not ∈-i [ bool ] ⇒ [ bool ]
      tand : and ∈-i (bool ∷ bool ∷ []) ⇒ [ bool ]
      tadd : add ∈-i (nat ∷ nat ∷ []) ⇒ [ nat ]
      tsub : sub ∈-i (nat ∷ nat ∷ []) ⇒ [ nat ]
      teqz : eqz ∈-i [ nat ] ⇒ [ bool ]
      tdup : ∀{t} → dup ∈-i [ t ] ⇒ t ∷ t ∷ []
      tdrop : ∀{t} → drop ∈-i [ t ] ⇒ []

    data _∈-is_ : insns → functype → Set where
      tiempty : [] ∈-is [] ⇒ []
      tiseq : ∀ {i is a b c} → i ∈-i a ⇒ b → is ∈-is b ⇒ c → i ∷ is ∈-is a ⇒ c
      tiup : ∀ {i is a b c} → i ∈-i a ⇒ b → is ∈-is a ++ c ⇒ b ++ c
    mutual

      data _∈-li_ : insn → functype → Set where
        textend : ∀{i a b ks} → i ∈-i a ⇒ b → i ∈-li a ⇒ b / ks
        tblock : ∀{is a b ks}
          → is ∈-lis a ⇒ b / b ∷ ks
          → block (a ⇒ b) is ∈-li a ⇒ b / ks
        tif-else : ∀{ist isf a ks b}
          → ist ∈-lis a ⇒ b / b ∷ ks
          → isf ∈-lis a ⇒ b / b ∷ ks
          → if-else (a ⇒ b) ist isf ∈-li bool ∷ a ⇒ b / ks
        tloop : ∀{is a b ks}
          → is ∈-lis a ⇒ b / a ∷ ks
          → loop (a ⇒ b) is ∈-li a ⇒ b / ks
        tbrn : ∀{ks b} → {n : Fin (length ks)} → br (toℕ n) ∈-li lookup ks n ⇒ b / ks

      data _∈-lis_ : insns → functype → Set where
        tliempty : [] ∈-lis [] ⇒ [] / []
        tliseq : ∀ {i is a b c ks} → i ∈-li a ⇒ b / ks → is ∈-lis b ⇒ c / ks → i ∷ is ∈-lis a ⇒ c / ks
        tliup : ∀ {is a b d ks ks'} → is ∈-lis a ⇒ b / ks → is ∈-lis a ++ d ⇒ b ++ d / ks ++ ks'
        tlicast : ∀ {is a b} → is ∈-is a ⇒ b → is ∈-lis a ⇒ b / []

    data _∈-fs_ : frames → ctxtype → Set where
      tfempty : ∀ {a} → [] ∈-fs (a / [] ↠ a)
      tfstack : ∀ {vs l cont r k a b c fs ks}
                → vs ∈-vs r
                → l ∈-li k ⇒ a / ks
                → cont ∈-lis a ++ r ⇒ b / ks
                → fs ∈-fs b / ks ↠ c
                → (vs , length k , l , cont) ∷ fs ∈-fs a / k ∷ ks ↠ c

    data _∈-s_ : state → resulttype → Set where
      tstate : ∀ {fs vs is a b c ks}
               → fs ∈-fs b / ks ↠ c
               → vs ∈-vs a
               → is ∈-lis a ⇒ b / ks
               → (fs , vs , is) ∈-s c

    ∈-vs-append : ∀ {vs vs' ts ts' } → vs ∈-vs ts → vs' ∈-vs ts' → vs ++ vs' ∈-vs ts ++ ts'
    ∈-vs-append tvempty ps' = ps'
    ∈-vs-append (tvstack p ps) ps' = tvstack p (∈-vs-append ps ps')

    open Interpreter
    open import Relation.Binary.PropositionalEquality


    safety : ∀{t} → (st : state) → st ∈-s t → ∃ λ st' → (eval1 st ≡ ok st') × (st' ∈-s t)
    safety ([] , vs , []) p = ([] , vs , []) , (refl , p)
    safety (fs , vs , const v ∷ is) (tstate pfs pvs (tliseq (textend (tconst pv)) pis)) = (fs , v ∷ vs , is) , (refl , ?)
    safety ((vs' , _ , _ , cont) ∷ fs , vs , []) (tstate (tfstack pvs' _ pcont pfs) pvs _) = (fs , vs ++ vs' , cont) , (refl , tstate pfs (∈-vs-append pvs pvs') pcont)
