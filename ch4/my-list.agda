module my-list where

open import bool
open import empty
open import eq
open import maybe
open import nat
open import nat-thms
open import negation
open import product
open import product-thms

data List (A : Set) : Set where
  Nil : List A
  _::_ : (x : A) (xs : List A) → List A

infixr 6 _::_

length : ∀ {A : Set} → List A → nat
length Nil = 0
length (x :: xs) = suc (length xs)

_++_ : ∀ {A : Set} → List A → List A → List A
Nil ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f Nil = Nil
map f (x :: xs) = f x :: map f xs

filter : ∀ {A : Set} → (A → bool) → List A → List A
filter p Nil = Nil
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

remove : ∀ {A : Set} → (eq : A → A → bool) (a : A) (as : List A) → List A
remove eq a as = filter (λ x → ~ (eq a x)) as

nth : ∀ {A : Set} → nat → List A → maybe A
nth i Nil = nothing
nth zero (x :: xs) = just x
nth (suc i) (x :: xs) = nth i xs

sreverse : ∀ {A : Set} → List A → List A
sreverse Nil = Nil
sreverse (x :: xs) = (sreverse xs) ++ (x :: Nil)

reverse-helper : ∀ {A : Set} → List A → List A → List A
reverse-helper Nil rxs = rxs
reverse-helper (x :: xs) rxs = reverse-helper xs (x :: rxs)

reverse : ∀ {A : Set} → List A → List A
reverse xs = reverse-helper xs Nil

length-++ :
  ∀ {A : Set} (xs ys : List A) →
  length (xs ++ ys) ≡ (length xs) + (length ys)
length-++ Nil ys = refl
length-++ (x :: xs) ys = cong suc (length-++ xs ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc Nil ys zs = refl
++-assoc (x :: xs) ys zs = cong (_::_ x) (++-assoc xs ys zs)

data _<=_ : nat → nat → Set where
  z<=n : ∀ {n} → 0 <= n
  s<=s : ∀ {n m} → n <= m → suc n <= suc m

<=s : ∀ {n m} → n <= m → n <= suc m
<=s z<=n = z<=n
<=s (s<=s n<=m) = s<=s (<=s n<=m)

length-filter :
  ∀ {A : Set} (p : A → bool) (xs : List A) → length (filter p xs) <= length xs
length-filter p Nil = z<=n
length-filter p (x :: xs) with p x
... | tt = s<=s (length-filter p xs)
... | ff = <=s (length-filter p xs)

filter-idem :
  ∀ {A : Set} (p : A → bool) (xs : List A) →
  filter p (filter p xs) ≡ filter p xs
filter-idem p Nil = refl
filter-idem p (x :: xs) with keep (p x)
... | tt , p' rewrite p' | p' = cong (_::_ x) (filter-idem p xs)
... | ff , p' rewrite p' = filter-idem p xs

length-reverse-helper :
  ∀ {A : Set} (xs rxs : List A) →
  length (reverse-helper xs rxs) ≡ length xs + length rxs
length-reverse-helper Nil rxs = refl
length-reverse-helper (x :: xs) rxs
  rewrite length-reverse-helper xs (x :: rxs) = +suc (length xs) (length rxs)

length-reverse : ∀ {A : Set} (xs : List A) → length (reverse xs) ≡ length xs
length-reverse xs rewrite length-reverse-helper xs Nil = +0 (length xs)

-- Exercises
-- 4.1 (a)
++-comm-false :
  Σ Set (λ A → Σ (List A × List A) (λ { (xs , ys) → ¬ (xs ++ ys ≡ ys ++ xs) }))
++-comm-false = bool , (tt :: Nil , ff :: Nil) , λ ()
