import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Definitions.
_+_ : ℕ → ℕ → ℕ
zero + n    = n
(suc m) + n = suc (m + n)

infixl 6 _+_

-- Associativity of +
-- (m + n) + p ≡  m + (n + p)
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n ) ⟩
    suc (suc m + n)
  ∎


+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m  ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    (suc n) + m
  ∎


+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎


-- Rewrite

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl


-- Excercises
+-sucswap : ∀ (m n : ℕ) →  (suc m) + n ≡ m + (suc n)
+-sucswap zero n = refl
+-sucswap (suc m) n =
  begin
    (suc (suc m)) + n
  ≡⟨⟩
    suc ((suc m) + n)
  ≡⟨ cong suc (+-sucswap m n) ⟩
    suc (m + (suc n))
  ≡⟨⟩
    (suc m) + (suc n)
  ∎

+-parens : ∀ (m n p : ℕ) → m + n + p ≡ m + (n + p)
+-parens zero n p = refl
+-parens (suc m) n p =
  begin
    (suc m) + n + p
  ≡⟨⟩
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n + p)
  ≡⟨ cong suc (+-parens m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    (suc m) + (n + p)
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p =
  begin
    (suc m) + (n + p)
  ≡⟨ sym (+-parens (suc m) n p) ⟩
    (suc m) + n + p
  ≡⟨ cong (_+ p) (+-comm (suc m) n) ⟩
    n + (suc m) + p
  ≡⟨ +-parens n (suc m) p ⟩
   n + ((suc m) + p)
  ∎

