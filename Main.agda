module Main where

open import Prelude
open import Krivine
open import Krivine.Ex
open import Krivine.Show


ev : Nat -> Nat -> State -> List State -> List State
ev zero i s ss    = s ∷ ss
ev _ _ (halt m) ss = (halt m) ∷ ss
ev (suc n) i s ss = ev n (suc i) (exec s) (s ∷ ss)

evH : Term -> List State
evH t = ev 100 0 (st (pair t ∅) []) []

ex1 : IO ⊤
ex1 = putStrLn $ show {{ ShowLS }} (evH Krivine.Ex.fstT)