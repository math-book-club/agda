open import Relation.Binary.PropositionalEquality
open import Data.Nat

-- ind-ℕ : (D : ℕ → Set) →
--         D zero → ((n : ℕ) → D n → (D (suc n))) →
--         (m : ℕ) →
--         D m
-- ind-ℕ = {!!}
-- 
-- all-nat-≥-0 : (n : ℕ) → (n ≥ 0)
-- all-nat-≥-0 = {!!}

variable
  A : Set

ind-≡ : (D : (x₁ : A) → (y₁ : A) → x₁ ≡ y₁ → Set) →
        (d : (a : A) → D a a refl) →
        (x : A) → (y : A) → (p : x ≡ y) →
        D x y p
ind-≡ _ d a a refl = d a

lem-2-1-1 : {x y : A} → (x ≡ y) → (y ≡ x)
lem-2-1-1 {x = x} {y = y} x≡y =
  let
    D : (x₁ y₁ : A) → (x₁ ≡ y₁) → Set
    D x₁ y₁ _ = y₁ ≡ x₁

    d : (a : A) → D a a refl
    d a = refl
  in
    ind-≡ D d x y x≡y

-- lem-2-1-2 : (x y z : A) → (x ≡ y) → (y ≡ z) → (x ≡ z)
-- lem-2-1-2 x y z x≡y y≡z =
--   let
--     D : (x' y' : A) → (x' ≡ y') → Set
--     D x' y' x'≡y' = x
