module lt where

open import nat hiding (_≤_; _<_)
open import empty
open import eq

data _≤_ : ℕ → ℕ → Set where
  0≤ : ∀ {n} → 0 ≤ n
  suc≤ : ∀ {n m} → n ≤ m → suc n ≤ suc m

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans 0≤ 0≤ = 0≤
≤-trans 0≤ (suc≤ y≤z) = 0≤
≤-trans (suc≤ x≤y) (suc≤ y≤z) = suc≤ (≤-trans x≤y y≤z)

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = 0≤
≤-refl {suc n} = suc≤ ≤-refl

≤-refl-suc : ∀ {n} → n ≤ suc n
≤-refl-suc {zero} = 0≤
≤-refl-suc {suc n} = suc≤ ≤-refl-suc

_<_ : ℕ → ℕ → Set
n < m = (suc n) ≤ m

<-trans : ∀ {x y z} → x < y → y < z → x < z
<-trans {x} {y} x<y y<z = ≤-trans x<y (≤-trans ≤-refl-suc y<z)

data Dec : Set → Set where
  Yes : ∀ {P} → (prf : P) → Dec P
  No : ∀ {P} → (contra : P → ⊥) → Dec P

ℕ≡Dec : (n m : ℕ) → Dec (n ≡ m)
ℕ≡Dec zero zero = Yes refl
ℕ≡Dec zero (suc m) = No (\ ())
ℕ≡Dec (suc n) zero = No (\ ())
ℕ≡Dec (suc n) (suc m) with (ℕ≡Dec n m)
ℕ≡Dec (suc n) (suc m) | Yes prf = Yes (cong suc prf)
ℕ≡Dec (suc n) (suc m) | No contra = No (\ { refl → contra refl })
