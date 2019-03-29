module exercises where

open import bool
open import eq

-- 2.1
&&-tt : ∀ (b : 𝔹) → b && tt ≡ b
&&-tt tt = refl
&&-tt ff = refl

&&-ff : ∀ (b : 𝔹) → b && ff ≡ ff
&&-ff tt = refl
&&-ff ff = refl

&&-over-||-r : ∀ (a b c : 𝔹) → (a || b) && c ≡ (a && c) || (b && c)
&&-over-||-r a b tt rewrite &&-tt (a || b) | &&-tt a | &&-tt b = refl
&&-over-||-r a b ff rewrite &&-ff (a || b) | &&-ff a | &&-ff b = refl

-- 2.2
lnc : ∀ (b : 𝔹) → b && ~ b ≡ ff
lnc tt = refl
lnc ff = refl

lem : ∀ (b : 𝔹) → b || ~ b ≡ tt
lem tt = refl
lem ff = refl

-- 2.3
ex3a : tt ≡ tt
ex3a = refl

ex3b : ff ≡ ff
ex3b = refl

-- Impossible
-- ex3c : ff ≡ tt
-- ex3c = refl

ex3d : ff && ff ≡ ~ tt
ex3d = refl

ex3e : ∀ (x : 𝔹) → tt && x ≡ x
ex3e x = refl

-- Impossible
-- ex3f : ∀ (x : 𝔹) → x && tt ≡ x
-- ex3f x = refl
