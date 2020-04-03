module Chapter2 where

open import Relation.Binary.PropositionalEquality
open import Data.Nat

-- ind-single-step :  (D : ℕ → Set) → (n : ℕ) → D n → (D (suc n))

-- D = λ n → 0 ≤ n
-- ind-single-step-≤ : (n : ℕ) → (0 ≤ n) → (0 ≤ (suc n))
-- ind-single-step-≤ n dₙ = {!!}

ind-ℕ : (D : ℕ → Set) →
        D zero →
        ((n : ℕ) → D n → (D (suc n))) →
  -----------------------------------------
        (m : ℕ) → D m
ind-ℕ _ d₀ dₛ zero    = d₀
ind-ℕ D d₀ dₛ (suc m) = dₛ m (ind-ℕ D d₀ dₛ m)

rec-ℕ : (C : Set) →
        (c₀ : C) →
        (cₛ : (ℕ → C → C)) →
        ℕ →
        C
rec-ℕ C c₀ cₛ zero    = c₀
rec-ℕ C c₀ cₛ (suc n) = cₛ n (rec-ℕ C c₀ cₛ n)

-- double-ℕ n = rec-ℕ n (λ _ c → 

variable
  A : Set

ind-≡ : (D : (x₁ : A) → (y₁ : A) → x₁ ≡ y₁ → Set) →
        (d : (a : A) → D a a refl) →
        (x : A) → (y : A) →

        (p : x ≡ y) →
  -------------------------------------------------------
        D x y p
ind-≡ _ d a _ refl = d a

lem-2-1-1 : {x y : A} → (x ≡ y) → (y ≡ x)
lem-2-1-1 {x = x} {y = y} x≡y =
  let
    D : (x₁ y₁ : A) → (x₁ ≡ y₁) → Set
    D x₁ y₁ _ = y₁ ≡ x₁

    d : (a : A) → D a a refl
    d a = refl
  in
    ind-≡ D d x y x≡y

lem-2-1-2 : {A : Set} → (x y z : A) → (x ≡ y) → (y ≡ z) → (x ≡ z)
lem-2-1-2 {A} x₀ y₀ z₀ x≡y y≡z =
  let
    D : (x y : A) → (x ≡ y) → Set
    D x y y≡z = (z : A) → (y ≡ z) → (x ≡ z)

    E : (x z : A) → (x ≡ z) → Set
    E x z q = (x ≡ z)

    e : (x : A) → E x x refl
    e x = refl

    d : (x : A) → D x x refl
    d x = λ z x≡z → ind-≡ E e x z x≡z
  in
    (ind-≡ D d x₀ y₀ x≡y) z₀ y≡z
   
