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

-- 4.1 (b)
length-map-suc-never :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  ¬ (length (map f xs) ≡ suc (length xs))
length-map-suc-never f Nil ()
length-map-suc-never f (x :: xs) contra =
  length-map-suc-never f xs (suc-inj contra)

-- 4.1 (c)
repeat : ∀ {A : Set} → nat → A → List A
repeat zero x = Nil
repeat (suc n) x = x :: repeat n x

filter-out-repeats :
  ∀ {A : Set} {p : A → bool} {a : A} (n : nat) →
  p a ≡ ff →
  filter p (repeat n a) ≡ Nil
filter-out-repeats zero pa≡ff = refl
filter-out-repeats (suc n) pa≡ff rewrite pa≡ff = filter-out-repeats n pa≡ff

-- 4.1 (d)
is-empty : ∀ {A : Set} → List A → bool
is-empty Nil = tt
is-empty (_ :: _) = ff

reverse-not-empty-never :
  ∀ {A : Set} (xs : List A) → is-empty xs ≡ tt → ¬ (is-empty (reverse xs) ≡ ff)
reverse-not-empty-never Nil exs≡tt = λ ()
reverse-not-empty-never (x :: xs) ()

-- 4.1 (e)
filter-preserves-order :
  ∀ {A : Set} (p : A → bool) (xs ys : List A) →
  filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
filter-preserves-order p Nil ys = refl
filter-preserves-order p (x :: xs) ys with p x
... | tt = cong (_::_ x) (filter-preserves-order p xs ys)
... | ff = filter-preserves-order p xs ys

-- 4.2 (a)
test-a-i : List nat
test-a-i = Nil

-- test-a-ii : List List
-- test-a-ii = Nil

test-a-iii : List bool
test-a-iii = Nil

test-a-iv : List (List bool)
test-a-iv = Nil

-- test-a-v : List Set
-- test-a-v = Nil

module _ where
  open import list

  test-a-v' : list Set
  test-a-v' = []

-- 4.2 (b)
test-b-i : ∀ {A : Set} → List A → nat
test-b-i Nil = 0
test-b-i (x :: xs) = suc (test-b-i xs)

-- test-b-ii : List A → nat
-- test-b-ii Nil = 0
-- test-b-ii (x :: xs) = suc (test-b-ii xs)

test-b-iii : List bool → nat
test-b-iii Nil = 0
test-b-iii (x :: xs) = suc (test-b-iii xs)

-- test-b-iv : ∀ {A : Set} → (xs : List A) → length xs
-- test-b-iv Nil = 0
-- test-b-iv (x :: xs) = suc (test-b-iv xs)

-- 4.2 (c)
test-c-i : ∀ {A B C : Set} → (A → B) → (B → C) → List A → List C
test-c-i f g x = map g (map f x)

test-c-ii : ∀ {A : Set} → (A → A) → (A → A) → List A → List A
test-c-ii f g x = map g (map f x)

-- test-c-iii : ∀ {A B C : Set} → (B → C) → (A → B) → List A → List C
-- test-c-iii f g x = map g (map f x)

-- test-c-iv : ∀ {A B C : Set} → (A → B → C) → List A → List (B → C)
-- test-c-iv f g x = map g (map f x)

-- test-c-v : ∀ {B : Set} {A : List B} → (A → B) → (B → B) → List A → List B
-- test-c-v f g x = map g (map f x)

-- 4.3
takeWhile : ∀ {A : Set} → (A → bool) → List A → List A
takeWhile p Nil = Nil
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else Nil

-- 4.4
takeWhileRepeat :
  ∀ {A : Set} (p : A → bool) (n : nat) (a : A) →
  p a ≡ tt →
  takeWhile p (repeat n a) ≡ repeat n a
takeWhileRepeat p zero a pa≡tt = refl
takeWhileRepeat p (suc n) a pa≡tt rewrite pa≡tt =
  cong (_::_ a) (takeWhileRepeat p n a pa≡tt)

-- 4.5
take : ∀ {A : Set} (n : nat) (xs : List A) → List A
take (suc n) (x :: xs) = x :: take n xs
take _ _ = Nil

-- 4.6
drop : ∀ {A : Set} (n : nat) (xs : List A) → List A
drop zero xs = xs
drop (suc n) Nil = Nil
drop (suc n) (_ :: xs) = drop n xs

take++drop : ∀ {A : Set} (n : nat) (xs : List A) → take n xs ++ drop n xs ≡ xs
take++drop zero xs = refl
take++drop (suc n) Nil = refl
take++drop (suc n) (x :: xs) = cong (_::_ x) (take++drop n xs)
