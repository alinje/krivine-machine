module Krivine.Ex where

-- open import Prelude
open import Krivine

-- TODO trust no one
-- \x -> \y -> x
fstT : Term
fstT = lam (lam < 0 , 1 >)

-- \x -> \y -> y
sndT : Term
sndT = lam (lam < 0 , 0 >)


------- booleans --------

true : Term
true = fstT

false : Term
false = sndT

-- 
fst24 : Term
fst24 = app (app fstT true) false

not : Term
not = lam (app (app < 0 , 0 > false) true)

notTrue : Term
notTrue = app not true

notFalse : Term
notFalse = app not false

and : Term
and = lam (lam (app (app < 0 , 0 > < 0 , 1 >) false))

t&f : Term
t&f = app (app and true) false


------ integers --------

zero : Term
zero = lam (lam sndT)

succ : Term
succ = lam (lam (lam (app (app < 0 , 1 > < 0 , 0 >) < 0 , 2 >)))

one : Term
one = app succ zero