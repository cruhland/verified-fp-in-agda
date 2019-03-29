module div where

open import nat
open import nat-thms
open import eq
open import product
open import empty
open import sum

data _divides_ : ℕ → ℕ → Set where
  div0 : ∀ {n} → n divides 0
  div+ : ∀ {n m} → n divides m → n divides (n + m)

one-divides-n : ∀ {n} → 1 divides n
one-divides-n {zero} = div0
one-divides-n {suc n} = div+ one-divides-n

n-divides-n : ∀ {n} → n divides n
n-divides-n {n} with div+ (div0 {n}) | cong (\x → n divides x) (+0 n)
n-divides-n {n} | d | prf rewrite prf = d

division-by-zero : ∀ {n} → 0 divides (suc n) → ⊥
division-by-zero (div+ 0\n) = division-by-zero 0\n

divides-multiple : ∀ {n m} → n divides m → Σ ℕ (\k → k * n ≡ m)
divides-multiple div0 = 0 , refl
divides-multiple {n} (div+ div) with divides-multiple div
divides-multiple {n} (div+ div) | k' , p = suc k' , cong (_+_ n) p

multiple-divides : ∀ {n m} → Σ ℕ (\k → k * n ≡ m) → n divides m
multiple-divides {n} {m} (zero , p) rewrite sym p =
  div0
multiple-divides {n} {m} (suc k , p) rewrite sym p =
  div+ (multiple-divides (k , refl))

divides-trans : ∀ {a b c} → a divides b → b divides c → a divides c
divides-trans {a} a\b b\c with divides-multiple a\b | divides-multiple b\c
... | (m , p) | (n , q) rewrite sym p | *assoc n m a =
  multiple-divides (n * m , q)

+lemma : ∀ {n x} → n + x ≡ n → x ≡ 0
+lemma {zero} p = p
+lemma {suc n} p = +lemma (suc-inj p)

*lemma : ∀ {x n} → x * n ≡ n → n ≡ 0 ∨ x ≡ 1
*lemma {x} {zero} p = inj₁ refl
*lemma {zero} {suc n} ()
*lemma {suc zero} {suc n} p = inj₂ refl
*lemma {suc (suc x)} {suc n} p with +lemma (suc-inj p)
... | ()

*≡1 : ∀ {a b} → a * b ≡ 1 → a ≡ 1 × b ≡ 1
*≡1 {zero} {b} ()
*≡1 {suc a} {zero} p rewrite *0 a with p
... | ()
*≡1 {suc zero} {suc zero} p = refl , refl
*≡1 {suc zero} {suc (suc b)} p with suc-inj p
... | ()
*≡1 {suc (suc a)} {suc b} p rewrite +suc b (b + a * suc b) with suc-inj p
... | ()

divides-sym : ∀ {a b} → a divides b → b divides a → a ≡ b
divides-sym {a} a\b b\a with divides-multiple a\b | divides-multiple b\a
... | (m , p) | (n , q) rewrite sym p | *assoc n m a with *lemma {n * m} {a} q
... | inj₁ a0 rewrite a0 = sym (*0 m)
... | inj₂ nm1 with *≡1 {n} {m} nm1
... | (n≡1 , m≡1) rewrite m≡1 = sym (+0 a)
