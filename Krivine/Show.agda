module Krivine.Show where

open import Prelude
open import Krivine

termStr : Nat -> Term -> ShowS
termStr p < v , k > = showString "<" ∘ shows v ∘ showString "," ∘ shows k ∘ showString ">"
termStr p (app u v) = showString "(" ∘ termStr p u ∘ termStr p v ∘ showString ")"
termStr p (lam t)   = showString "λ." ∘ termStr p t
termStr p cc        = showString "cc"

mutual 
    envStr : Nat -> Env -> ShowS
    envStr p ∅         = showString "∅"
    envStr p (env e x) = showString "("  ∘ envStr p e ∘ showString "," ∘ contStr p x ∘ showString "("

    closureStr : Nat -> Closure -> ShowS
    closureStr p (γ x)      = showString "continuation " ∘ contStr p x
    closureStr p (pair t e) = showString "(" ∘ termStr p t ∘ showString ",\n    " ∘ envStr p e ∘ showString ")"

    contStr : Nat -> Cont -> ShowS
    contStr p []               = showString "[]"
    contStr p (γ x :: c)       = showString "continuation " ∘ contStr p x ∘ showString " | " ∘ contStr p c
    contStr p (c :: cs) = closureStr p c ∘ showString " | " ∘ contStr p cs

stateStr : Nat -> State -> ShowS
stateStr p (st x c) = showString "{" ∘ closureStr p x ∘ showString ",\n    " ∘ contStr p c ∘ showString "}"
stateStr p (halt x) = showString "halted w msg: " ∘ showString x

stateLsStr : Nat -> List State -> ShowS
stateLsStr p [] = showString "\n"
stateLsStr p (x ∷ ls) = stateStr p x ∘ showString "\n" ∘ stateLsStr p ls


instance 
    ShowTerm : Show Term
    ShowTerm = record { showsPrec = termStr }
    ShowEnv : Show Env
    ShowEnv = record { showsPrec = envStr }
    ShowClosure : Show Closure
    ShowClosure = record { showsPrec = closureStr }
    ShowCont : Show Cont
    ShowCont = record { showsPrec = contStr }
    ShowState : Show State
    ShowState = record { showsPrec = stateStr }
    ShowLS : Show (List State)
    ShowLS = record { showsPrec = stateLsStr }