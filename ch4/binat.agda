module binat where

open import empty
open import eq
open import list
open import maybe
open import nat using (nat)
open import nat-thms
open import product
open import product-thms
open import unit

data bit : Set where
  O : bit
  I : bit

binat : Set
binat = maybe (𝕃 bit)

zero : binat
zero = nothing

one : binat
one = just []

two : binat
two = just (O :: [])

bitToNat : bit → nat
bitToNat O = nat.zero
bitToNat I = nat.suc nat.zero

toNat⁺ : 𝕃 bit → nat
toNat⁺ [] = nat.suc nat.zero
toNat⁺ (b :: bs) = bitToNat b nat.+ (2 nat.* toNat⁺ bs)

toNat : binat → nat
toNat nothing = nat.zero
toNat (just bs) = toNat⁺ bs

suc⁺ : 𝕃 bit → 𝕃 bit
suc⁺ [] = O :: []
suc⁺ (O :: bs) = I :: bs
suc⁺ (I :: bs) = O :: suc⁺ bs

suc : binat → binat
suc nothing = just []
suc (just bs) = just (suc⁺ bs)

fromNatPred : nat → 𝕃 bit
fromNatPred nat.zero = []
fromNatPred (nat.suc n) = suc⁺ (fromNatPred n)

fromNat : nat → binat
fromNat nat.zero = nothing
fromNat (nat.suc n) = just (fromNatPred n)

toNat⁺suc⁺≡sucToNat⁺ : (bs : 𝕃 bit) → toNat⁺ (suc⁺ bs) ≡ nat.suc (toNat⁺ bs)
toNat⁺suc⁺≡sucToNat⁺ [] = refl
toNat⁺suc⁺≡sucToNat⁺ (O :: bs) = refl
toNat⁺suc⁺≡sucToNat⁺ (I :: bs) rewrite toNat⁺suc⁺≡sucToNat⁺ bs with toNat⁺ bs
... | n rewrite +0 n | +suc n n = refl

toNat⁺fromNatPred≡nat : (n : nat) → toNat⁺ (fromNatPred n) ≡ nat.suc n
toNat⁺fromNatPred≡nat nat.zero = refl
toNat⁺fromNatPred≡nat (nat.suc n)
  rewrite toNat⁺suc⁺≡sucToNat⁺ (fromNatPred n) =
    cong nat.suc (toNat⁺fromNatPred≡nat n)

toFrom≡nat : (n : nat) → toNat (fromNat n) ≡ n
toFrom≡nat nat.zero = refl
toFrom≡nat (nat.suc n) = toNat⁺fromNatPred≡nat n

toNat⁺≡suc : (bs : 𝕃 bit) → Σ nat (λ n → toNat⁺ bs ≡ nat.suc n)
toNat⁺≡suc [] = 0 , refl
toNat⁺≡suc (b :: bs) with toNat⁺≡suc bs
toNat⁺≡suc (b :: bs) | n , p rewrite
  p | +0 n | +suc (bitToNat b) (n nat.+ nat.suc n) =
  bitToNat b nat.+ (n nat.+ nat.suc n) , refl

0≡suc-false : {n : nat} → nat.zero ≡ nat.suc n → ⊥
0≡suc-false ()

+-same-inj : (n m : nat) → n nat.+ n ≡ m nat.+ m → n ≡ m
+-same-inj nat.zero nat.zero p = refl
+-same-inj nat.zero (nat.suc m) p = ⊥-elim (0≡suc-false p)
+-same-inj (nat.suc n) nat.zero p = ⊥-elim (0≡suc-false (sym p))
+-same-inj (nat.suc n) (nat.suc m) p rewrite +suc n n | +suc m m =
  cong nat.suc (+-same-inj n m (suc-inj (suc-inj p)))

+-same-suc-false : (n m : nat) → n nat.+ n ≡ nat.suc (m nat.+ m) → ⊥
+-same-suc-false nat.zero m p = 0≡suc-false p
+-same-suc-false (nat.suc n) nat.zero p rewrite +suc n n =
  0≡suc-false (suc-inj (sym p))
+-same-suc-false (nat.suc n) (nat.suc m) p rewrite +suc n n | +suc m m =
  +-same-suc-false n m (suc-inj (suc-inj p))

toNat⁺Inj : (nbs mbs : 𝕃 bit) → toNat⁺ nbs ≡ toNat⁺ mbs → nbs ≡ mbs
toNat⁺Inj [] [] p = refl
toNat⁺Inj [] (b :: mbs) p with toNat⁺≡suc mbs
... | r , q rewrite q | +0 (nat.suc r) | +suc r r with bitToNat b | r nat.+ r
... | bn | r2 rewrite +suc bn (nat.suc r2) | +suc bn r2 =
  ⊥-elim (0≡suc-false (suc-inj p))
toNat⁺Inj (b :: nbs) [] p with toNat⁺≡suc nbs
... | r , q rewrite q | +0 (nat.suc r) | +suc r r with bitToNat b | r nat.+ r
... | bn | r2 rewrite +suc bn (nat.suc r2) | +suc bn r2 =
  ⊥-elim (0≡suc-false (suc-inj (sym p)))
toNat⁺Inj (nb :: nbs) (mb :: mbs) p rewrite +0 (toNat⁺ nbs) | +0 (toNat⁺ mbs)
  with ⊤
toNat⁺Inj (O :: nbs) (O :: mbs) p | _ =
  cong (_::_ O) (toNat⁺Inj nbs mbs (+-same-inj (toNat⁺ nbs) (toNat⁺ mbs) p))
toNat⁺Inj (O :: nbs) (I :: mbs) p | _ =
  ⊥-elim (+-same-suc-false (toNat⁺ nbs) (toNat⁺ mbs) p)
toNat⁺Inj (I :: nbs) (O :: mbs) p | _ =
  ⊥-elim (+-same-suc-false (toNat⁺ mbs) (toNat⁺ nbs) (sym p))
toNat⁺Inj (I :: nbs) (I :: mbs) p | _ =
  cong (_::_ I)
       (toNat⁺Inj nbs mbs (+-same-inj (toNat⁺ nbs) (toNat⁺ mbs) (suc-inj p)))

toNatInj : (n m : binat) → toNat n ≡ toNat m → n ≡ m
toNatInj nothing nothing p = refl
toNatInj nothing (just mbs) p with toNat⁺≡suc mbs
toNatInj nothing (just mbs) p | r , q = ⊥-elim (0≡suc-false (trans p q))
toNatInj (just nbs) nothing p with toNat⁺≡suc nbs
toNatInj (just nbs) nothing p | r , q = ⊥-elim (0≡suc-false (trans (sym p) q))
toNatInj (just nbs) (just mbs) p = cong just (toNat⁺Inj nbs mbs p)

fromTo≡binat : (n : binat) → fromNat (toNat n) ≡ n
fromTo≡binat n = toNatInj (fromNat (toNat n)) n (toFrom≡nat (toNat n))

-- Can it be proved directly?
fromTo≡binat' : (n : binat) → fromNat (toNat n) ≡ n
fromTo≡binat' nothing = refl
fromTo≡binat' (just bs) with toNat⁺≡suc bs
... | r , p rewrite p = cong just {!!}

fromTo≡binat'' : (n : binat) → fromNat (toNat n) ≡ n
fromTo≡binat'' nothing = refl
fromTo≡binat'' (just []) = refl
fromTo≡binat'' (just (b :: bs)) rewrite +0 (toNat⁺ bs) with toNat⁺≡suc bs
fromTo≡binat'' (just (O :: bs)) | r , p rewrite p | +suc r r = {!!}
fromTo≡binat'' (just (I :: bs)) | r , p rewrite p | +suc r r = {!!}

-- Need something stronger than this:
-- toNat⁺≡suc : (bs : 𝕃 bit) → Σ nat (λ n → toNat⁺ bs ≡ nat.suc n)
