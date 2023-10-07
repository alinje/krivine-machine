module Krivine.Ex where

open import Krivine
open import Prelude.Nat

-- \x -> \y -> x
fstT : Term
fstT = lam (lam < 0 , 0 >)

-- \x -> \y -> y
sndT : Term
sndT = lam (lam < 0 , 1 >)


------- booleans --------

true : Term
true = fstT

false : Term
false = sndT

not : Term
not = lam (app (app < 0 , 0 > false) true)

and : Term
and = lam (lam (app (app < 0 , 0 > < 0 , 1 >) false))

or : Term
or = lam (lam (app (app < 0 , 0 > true) < 0 , 1 >))

-- \x -> \y -> \z -> if x then y else z
if : Term
if = lam (lam (lam (app (app < 0 , 0 > < 0 , 1 >) < 0 , 2 >)))

-- \x -> \y -> x == y
eq : Term
eq = lam (lam (app (app < 0 , 0 > < 0 , 1 >) (app not < 0 , 1 >)))

------------
-- lemlem : Term -> Term
-- lemlem a = app {!   !} {!   !} --app (app or a) (not a) 
data _≡_ {A : Set} (x : A) : (y : A) -> Set where
    refl : x ≡ x

Id : {A : Set} -> (x : A) -> (y : A) -> Set
Id = _≡_

id : {A : Set} -> A -> A
id x = x

infix 4 _≡_

data Σ (A : Set) (B : A -> Set) : Set where
 pair : (a : A) -> (b : B a) -> Σ A B

elimSig : {A : Set} {B : A -> Set} {C : Set} ->
              ((x : A) -> B x -> C) ->
              Σ A B -> C
elimSig {A} {B} {C} f (pair a b) = f a b

∃ : {A : Set} -> (A -> Set) -> Set
∃ {A} = Σ A

thm : {p : Term} -> ∃ (\n -> run n p) ≡ ∃ (\t -> (app (app or t) (not t)))
thm = ?

-- thm : {a : Set} -> lemlem a
-- thm {a} = ?


-- exs bools

fst24 : Term
fst24 = app (app fstT true) false

notTrue : Term
notTrue = app not true

notFalse : Term
notFalse = app not false

t&f : Term
t&f = app (app and true) false

fvf : Term
fvf = app (app or false) false

fvt : Term
fvt = app (app or false) true

iftfet : Term
iftfet = app (app (app if true) false) true

t=t : Term
t=t = app (app eq true) true

t=f : Term
t=f = app (app eq true) false

f=t : Term
f=t = app (app eq false) true

f=f : Term
f=f = app (app eq false) false

------ integers --------

zerot : Term
zerot = lam (lam sndT)

succ : Term
succ = lam (lam (lam (app (app < 0 , 1 > < 0 , 0 >) < 0 , 2 >)))

one : Term
one = app succ zerot 