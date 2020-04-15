open import Relation.Binary.PropositionalEquality
open import Data.Nat

-- From "1.9 The natural numbers", p. 50
recℕ : {C : Set} → (c₀ : C) → (cₛ : ℕ → C → C) → ℕ → C
recℕ c₀ cₛ 0 = c₀
recℕ c₀ cₛ (suc n) = cₛ n (recℕ c₀ cₛ n)

-- (1.9.1), p. 50
double : ℕ → ℕ
double = recℕ 0 (λ n y → suc (suc y))

-- From "1.9 The natural numbers", p. 51
indℕ : {C : ℕ → Set}
     → (c₀ : C 0)
     → (cₛ : (n : ℕ) → C n → (C (suc n)))
     → (n : ℕ) → C n
indℕ c₀ cₛ 0 = c₀
indℕ c₀ cₛ (suc n) = cₛ n (indℕ c₀ cₛ n)

-- From "1.9 The natural numbers", p. 51
assoc : {j k : ℕ}
      → (i : ℕ)
      → i + (j + k) ≡ (i + j) + k
assoc {j} {k} i = indℕ (assoc₀ {j} {k}) assocₛ i
  where
    assoc₀ : {j k : ℕ}
           → 0 + (j + k) ≡ (0 + j) + k
    assoc₀ = refl

    assocₛ : {j k : ℕ}
           → (n : ℕ)
           → n + (j + k) ≡     (n + j) + k
           → suc n + (j + k) ≡ (suc n + j) + k
    assocₛ n h = ap h
      where
        -- Proof can be given after Chapter 2.2 Functions and functors
        postulate
            ap : {i k : ℕ} → i ≡ k → suc i ≡ suc k
