
open import eq
open import level
open import negation
open import product
open import sum

module my-relations {ℓ ℓ'} {A : Set ℓ} (_≤_ : A → A → Set ℓ') where

transitive : Set (ℓ ⊔ ℓ')
transitive = ∀ {a b c : A} → a ≤ b → b ≤ c → a ≤ c

total : Set (ℓ ⊔ ℓ')
total = ∀ {a b : A} → a ≤ b ∨ b ≤ a

reflexive : Set (ℓ ⊔ ℓ')
reflexive = ∀ {a : A} → a ≤ a

merge : ∀ {ℓ} {A : Set ℓ} → A ∨ A → A
merge (inj₁ a) = a
merge (inj₂ a) = a

total→reflexive : total → reflexive
total→reflexive p {a} = merge (p {a} {a})

decidable : Set (ℓ ⊔ ℓ')
decidable = ∀ {a b : A} → a ≤ b ∨ ¬ (a ≤ b)

antisym : Set (ℓ ⊔ ℓ')
antisym = ∀ {a b : A} → a ≤ b → b ≤ a → a ≡ b
