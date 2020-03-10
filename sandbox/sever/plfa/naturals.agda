-- Chapter 1 of PLFA

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

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero = (suc zero)
n ^ (suc m) = n * (n ^ m)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- Precedence.
infixl 6  _+_  _∸_
infixl 7  _*_

-- Tests.
_ : 2 + 3 ≡ 5
_ = refl

_ : 2 * 3 ≡ 6
_ = refl

_ : 2 ^ 3 ≡ 8                                                                                          
_ = refl

_ : 5 ∸ 3 ≡ 2
_ = refl

_ : 2 ∸ 5 ≡ 0                                                                                          
_ = refl
