module my-vector where

open import bool
open import list using (list; _::_; [])
open import nat

data vector {ℓ} (A : Set ℓ) : nat → Set ℓ where
  [] : vector A 0
  _::_ : {n : nat} (x : A) (xs : vector A n) → vector A (suc n)

test-vector : vector bool 4
test-vector = ff :: tt :: ff :: ff :: []

test-vector2 : list (vector bool 2)
test-vector2 = (ff :: tt :: []) :: (tt :: ff :: []) :: (tt :: ff :: []) :: []

test-vector3 : vector (vector bool 3) 2
test-vector3 = (tt :: tt :: tt :: []) :: (ff :: ff :: ff :: []) :: []

_++_ :
  ∀ {ℓ} {A : Set ℓ} {n m : nat} → vector A n → vector A m → vector A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

test-vector-append : vector bool 8
test-vector-append = test-vector ++ test-vector

head : ∀ {ℓ} {A : Set ℓ} {n : nat} → vector A (suc n) → A
head (x :: _) = x

tail : ∀ {ℓ} {A : Set ℓ} {n : nat} → vector A n → vector A (pred n)
tail [] = []
tail (_ :: xs) = xs

tail-strict : ∀ {ℓ} {A : Set ℓ} {n : nat} → vector A (suc n) → vector A n
tail-strict (_ :: xs) = xs
