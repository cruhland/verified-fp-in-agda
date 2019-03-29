module my-bool where

open import level

data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

infix 7 ~_
infixr 6 _&&_
infixl 6 _xor_
infixr 5 _||_
infix  4 if_then_else_
infixr 4 _imp_

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor b = ~ b
ff xor b = b

_imp_ : 𝔹 → 𝔹 → 𝔹
tt imp b = b
ff imp _ = tt

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then t else f = t
if ff then t else f = f

-- Exercise 1.1
ex1a : 𝔹
ex1a = tt && (ff xor ~ ff)
-- Evaluates to: tt

ex1b : 𝔹
ex1b = ~ tt && (ff imp ff)
-- Evaluates to: ff

ex1c : 𝔹
ex1c = if tt xor tt then ff else ff
-- Evaluates to: ff

-- Exercise 1.2
ex2a : 𝔹
ex2a = tt

ex2b : 𝔹
ex2b = if tt then ff else tt

ex2c : 𝔹 → 𝔹 → 𝔹
ex2c = _&&_

ex2d : Set
ex2d = 𝔹

-- Exercise 1.3
-- Already redefined the operations here
-- Good to know about open import bool hiding (...), though

-- Exercise 1.4
data day : Set where
  mon : day
  tue : day
  wed : day
  thu : day
  fri : day
  sat : day
  sun : day

-- Exercise 1.5
nextday : day → day
nextday mon = tue
nextday tue = wed
nextday wed = thu
nextday thu = fri
nextday fri = sat
nextday sat = sun
nextday sun = mon

-- Exercise 1.6
data suit : Set where
  clubs : suit
  diamonds : suit
  hearts : suit
  spades : suit

-- Exercise 1.7
is-red : suit → 𝔹
is-red diamonds = tt
is-red hearts = tt
is-red _ = ff
