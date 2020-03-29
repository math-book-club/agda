module DecidableEquality where
open import Data.Nat using (ℕ)
--import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.List.Relation.Unary.AllPairs using (AllPairs; allPairs?)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Sum using (_⊎_)
open import Level using (0ℓ)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; False; ⌊_⌋; toWitness; fromWitness)
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Data.Empty
open import Data.Product using (_×_)
open import Agda.Builtin.Unit

record DecEq (A : Set) : Set where
  field
    _≟_ : Decidable {A = A} _≡_

open DecEq {{...}}

module _ where
  _≟⊤_ : Decidable {A = ⊤} _≡_
  tt ≟⊤ tt = yes refl

instance
  DecEq⊤ : DecEq ⊤
  _≟_ {{DecEq⊤}} = _≟⊤_

  DecEqℕ : DecEq ℕ
  _≟_ {{DecEqℕ}} = Data.Nat._≟_

--  DecEqBool : DecEq Bool
--  _≟_ {{DecEqBool}} = Data.Bool._≟_

module _ where
  test : {A : Set} {{DecEqA : DecEq A}} → A → A → ℕ
  test a b with a ≟ b
  ... | yes p = 1
  ... | no ¬p = 2

  _ = test 4 5

--  _ = test true true
