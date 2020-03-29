module Pair where

open import Data.Fin using (Fin ; fromℕ)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or; _++_ )
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.List using (List; concat; map; length)
open import Data.List.Membership.Propositional
open import Relation.Nullary.Decidable using (True)
open import Relation.Nullary.Negation
open import Level
open import DecidableEquality

open DecEq {{...}}

open import Relation.Binary
open import Data.Empty

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

module _ where
  -- TODO: implement this using DecEq
  _≟Pair_ : {A B : Set} → {_≟A_ : Decidable {A = A} _≡_} → {_≟B_ : Decidable {A = B} _≡_} → Decidable {A = Pair A B} _≡_
  _≟Pair_ {_≟A_ = _≟A_} {_≟B_} (fl , sl) (fr , sr) with fl ≟A fr | sl ≟B sr
  ...                                           | yes p | yes q = yes
                                                                    (begin
                                                                     (fl , sl) ≡⟨ cong (_,_ fl) q ⟩
                                                                     (fl , sr) ≡⟨ cong (λ z → z , sr) p ⟩ (fr , sr) ∎)
  ...                                           | no ¬p | yes q = no lem
    where
    lem : (x : (fl , sl) ≡ (fr , sr)) → ⊥
    lem refl = ¬p refl
  ...                                           | no ¬p | no ¬q = no lem
    where
    lem : (x : (fl , sl) ≡ (fr , sr)) → ⊥
    lem refl = ¬q refl
  ...                                           | yes p | no ¬q = no lem
    where
    lem : (x : (fl , sl) ≡ (fr , sr)) → Data.Empty.⊥
    lem refl = ¬q refl

instance
  DecEqPair : {A B : Set} {{DecEqA : DecEq A}} {{DecEqB : DecEq B}} → DecEq (Pair A B)
  DecEq._≟_ DecEqPair = _≟Pair_ {_≟A_ = _≟_} {_≟B_ = _≟_}
