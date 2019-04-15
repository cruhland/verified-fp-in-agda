
open import empty
open import eq
open import level
open import negation
open import maybe
open import my-relations
open import product
open import sum

module my-bst
  {ℓ ℓ'}
  (A : Set ℓ)
  (_≤_ : A → A → Set ℓ')
  (≤-trans : transitive _≤_)
  (≤-total : total _≤_)
  (≤-decidable : decidable _≤_)
  (≤-antisym : antisym _≤_)
  where

data bst : A → A → Set (ℓ ⊔ ℓ') where
  leaf : ∀ {a z : A} → a ≤ z → bst a z
  node : ∀ {a b y z : A} (m : A) → bst b m → bst m y → a ≤ b → y ≤ z → bst a z

search : ∀ {a z : A} (v : A) → bst a z → maybe (Σ A (λ v' → v ≤ v' ∧ v' ≤ v))
search v (leaf _) = nothing
search v (node m bst≤ ≤bst p q) with (≤-decidable {v} {m})
search v (node m bst≤ ≤bst p q) | inj₁ v≤m with (≤-decidable {m} {v})
search v (node m bst≤ ≤bst p q) | inj₁ v≤m | inj₁ m≤v = just (m , v≤m , m≤v)
search v (node m bst≤ ≤bst p q) | inj₁ v≤m | inj₂ ¬m≤v = search v bst≤
search v (node m bst≤ ≤bst p q) | inj₂ ¬v≤m = search v ≤bst

data in-bst : {a z : A} → A → bst a z → Set ℓ' where
  in-node :
    ∀ {a b y z} {a≤ : a ≤ b} {≤z : y ≤ z}
    (m : A) (bst≤ : bst b m) (≤bst : bst m y) →
    in-bst m (node m bst≤ ≤bst a≤ ≤z)

  in-left :
    ∀ {a b y z} {a≤ : a ≤ b} {≤z : y ≤ z}
    (v w : A) (bst≤ : bst b w) (≤bst : bst w y) →
    in-bst v bst≤ →
    in-bst v (node w bst≤ ≤bst a≤ ≤z)

  in-right :
    ∀ {a b y z} {a≤ : a ≤ b} {≤z : y ≤ z}
    (u v : A) (bst≤ : bst b u) (≤bst : bst u y) →
    in-bst v ≤bst →
    in-bst v (node u bst≤ ≤bst a≤ ≤z)

bst-bounds : ∀ {a z : A} (t : bst a z) → a ≤ z
bst-bounds (leaf p) = p
bst-bounds (node m t≤ ≤t a≤ ≤z) =
  ≤-trans (≤-trans a≤ (bst-bounds t≤)) (≤-trans (bst-bounds ≤t) ≤z)

in-bst→lower-bound : ∀ {a z : A} (v : A) (t : bst a z) → in-bst v t → a ≤ v
in-bst→lower-bound v (node v t≤ ≤t a≤ _) (in-node .v t≤ ≤t) =
  ≤-trans a≤ (bst-bounds t≤)
in-bst→lower-bound v (node w t≤ ≤t a≤ _) (in-left .v w t≤ ≤t p) =
  ≤-trans a≤ (in-bst→lower-bound v t≤ p)
in-bst→lower-bound v (node u t≤ ≤t a≤ _) (in-right u .v t≤ ≤t p) =
  ≤-trans (≤-trans a≤ (bst-bounds t≤)) (in-bst→lower-bound v ≤t p)

in-bst→upper-bound : ∀ {a z : A} (v : A) (t : bst a z) → in-bst v t → v ≤ z
in-bst→upper-bound v (node v t≤ ≤t _ ≤z) (in-node .v t≤ ≤t) =
  ≤-trans (bst-bounds ≤t) ≤z
in-bst→upper-bound v (node w t≤ ≤t _ ≤z) (in-left .v w t≤ ≤t p) =
  ≤-trans (in-bst→upper-bound v t≤ p) (≤-trans (bst-bounds ≤t) ≤z)
in-bst→upper-bound v (node u t≤ ≤t _ ≤z) (in-right u .v t≤ ≤t p) =
  ≤-trans (in-bst→upper-bound v ≤t p) ≤z

search' : ∀ {a z : A} (v : A) (t : bst a z) → in-bst v t ∨ ¬ in-bst v t
search' v (leaf _) = inj₂ λ ()
search' v (node m t≤ ≤t a≤ ≤z) with (≤-decidable {v} {m})
search' v (node m t≤ ≤t a≤ ≤z) | inj₁ v≤m with (≤-decidable {m} {v})
search' v (node m t≤ ≤t a≤ ≤z) | inj₁ v≤m | inj₁ m≤v
  rewrite ≤-antisym v≤m m≤v = inj₁ (in-node m t≤ ≤t)
search' v (node m t≤ ≤t a≤ ≤z) | inj₁ v≤m | inj₂ ¬m≤v with search' v t≤
search' v (node m t≤ ≤t a≤ ≤z) | inj₁ v≤m | inj₂ ¬m≤v | inj₁ in-t≤ =
  inj₁ (in-left v m t≤ ≤t in-t≤)
search' v (node m t≤ ≤t a≤ ≤z) | inj₁ v≤m | inj₂ ¬m≤v | inj₂ ¬in-t≤ =
  inj₂ not-in-tree
    where
      not-in-tree : in-bst v (node m t≤ ≤t a≤ ≤z) → ⊥
      not-in-tree (in-node m bst≤ ≤bst) =
        ¬m≤v v≤m
      not-in-tree (in-left v w bst≤ ≤bst in-t) =
        ¬in-t≤ in-t
      not-in-tree (in-right u v bst≤ ≤bst in-t) =
        ¬m≤v (in-bst→lower-bound v ≤t in-t)
search' v (node m t≤ ≤t a≤ ≤z) | inj₂ ¬v≤m with search' v ≤t
search' v (node m t≤ ≤t a≤ ≤z) | inj₂ ¬v≤m | inj₁ in-≤t =
  inj₁ (in-right m v t≤ ≤t in-≤t)
search' v (node m t≤ ≤t a≤ ≤z) | inj₂ ¬v≤m | inj₂ ¬in-≤t =
  inj₂ not-in-tree
    where
      not-in-tree : in-bst v (node m t≤ ≤t a≤ ≤z) → ⊥
      not-in-tree (in-node m bst≤ ≤bst) =
        ¬v≤m (total→reflexive _≤_ ≤-total)
      not-in-tree (in-left v w bst≤ ≤bst in-t) =
        ¬v≤m (in-bst→upper-bound v t≤ in-t)
      not-in-tree (in-right u v bst≤ ≤bst in-t) =
        ¬in-≤t in-t
