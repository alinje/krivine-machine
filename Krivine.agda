module Krivine where

open import Prelude

Name = String

data Term : Set where
    <_,_> : (v k : Nat) -> Term
    app : (t u : Term) -> Term
    lam : (e : Term) -> Term
    cc : Term

    lit : (n : Bool) -> Term


mutual
    data Closure : Set where
        γ : Cont -> Closure
        pair : Term -> Env -> Closure

    data Cont : Set where
        [] : Cont
        _::_ : Closure -> Cont -> Cont

    data Env : Set where
        ∅ : Env
        env : Env -> Cont -> Env


data State : Set where
    st : Closure -> Cont -> State
    halt : String -> State

-- way I interpret it, however many arguments, reducing all is one step
exec-lam : Closure -> Cont -> State
exec-lam (pair (lam t) e) [] = halt "Congrats, a lambda expression"
exec-lam (pair (lam (lam t)) (env e φ)) (x₁ :: c) = exec-lam (pair (lam t) (env e (x₁ :: φ) )) c
exec-lam (pair (lam t) (env e φ)) (x₁ :: c) = st (pair t (env e (x₁ :: φ) )) c
exec-lam _ _ = halt "build away" -- TODO type should be restricted for this to not be a case


exec-var : State -> State
exec-var (st (pair < v , k > ∅) c)                        = halt "Variable does not exist"
exec-var (st (pair < v , k > (env e [])) c)               = halt "Variable does not exist 2"
exec-var (st (pair < zero , zero > (env _ (x :: _))) c)   = st x c
exec-var (st (pair < zero , suc k > (env e (x :: x₁))) c) = exec-var (st (pair < zero , k > (env e x₁)) c)
exec-var (st (pair < suc v , k > (env e _)) c)            = exec-var (st (pair < v , k > e) c)
exec-var _                                                = halt "build away" -- TODO type should be restricted for this to not be a case

exec : State -> State
exec (st (γ (x :: x₂)) [])      = halt "continuation on empty stack"
exec (st (γ c) (φ :: φs))       = st φ c
exec (st (pair < v , k > e) c)  = exec-var (st (pair < v , k > e) c)
exec (st (pair (app u v) e) c)  = st (pair u e) (pair v e :: c)
exec (st (pair (lam t) e) c)    = exec-lam (pair (lam t) (env e [])) c
exec (st (pair cc e) [])        = halt "cc on empty stack"
exec (st (pair cc e) (φ′ :: p)) = st φ′ (γ p :: p)
exec h                          = h

run : Nat -> State -> State
run zero s           = s
run (suc n) (halt m) = halt m
run (suc n) s        = run n (exec s)

eval : Closure -> Cont -> State
eval φ π = run 10 (st φ π)



