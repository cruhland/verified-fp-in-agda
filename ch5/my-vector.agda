module my-vector where

open import bool
open import list using (list; _::_; [])
open import nat hiding (_≤_; _<_)

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

map :
  ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : nat} →
  (A → B) →
  vector A n →
  vector B n
map f [] = []
map f (x :: xs) = f x :: map f xs

concat :
  ∀ {ℓ} {A : Set ℓ} {n m : nat} → vector (vector A n) m → vector A (m * n)
concat [] = []
concat (xs :: xss) = xs ++ concat xss

data _≤_ : nat → nat → Set where
  ≤-zero : ∀ {n} → 0 ≤ n
  ≤-suc : ∀ {n m} → n ≤ m → suc n ≤ suc m

_<_ : nat → nat → Set
n < m = suc n ≤ m

nth : ∀ {ℓ} {A : Set ℓ} {m : nat} → (n : nat) → n < m → vector A m → A
nth n () []
nth zero p (x :: xs) = x
nth (suc n) (≤-suc p) (x :: xs) = nth n p xs

repeat : ∀ {ℓ} {A : Set ℓ} (a : A) (n : nat) → vector A n
repeat x zero = []
repeat x (suc n) = x :: repeat x n
