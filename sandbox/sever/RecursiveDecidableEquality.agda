module RecursiveDecidableEquality where

open import Data.Nat
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

open import Relation.Binary
open import Data.Empty

open import Data.List.Properties using (≡-dec)

record Dummy : Set where
  inductive
  field
    d : List Dummy

{-
=-dec-dum : Decidable {A = Dummy} _≡_
=-dec-dum record { d = d₁ } record { d = d } with ≡-dec =-dec-dum d₁ d
...                                             | yes p = {!!}
-}

list-append-eq : {A : Set} → (a0 a1 : A) → (l0 l1 : List A) → a0 ≡ a1 → l0 ≡ l1 → a0 ∷ l0 ≡ a1 ∷ l1
list-append-eq {A} a0 a1 l0 l1 x x₁ = begin
                                        a0 ∷ l0 ≡⟨ cong (_∷_ a0) x₁ ⟩
                                        a0 ∷ l1 ≡⟨ cong (λ z → z ∷ l1) x ⟩ a1 ∷ l1 ∎

dummy-append-eq : (a0 a1 : Dummy) → (l0 l1 : List Dummy) → a0 ≡ a1 → l0 ≡ l1 → record { d = (a0 ∷ l0) } ≡ record { d = (a1 ∷ l1) }
dummy-append-eq a0 a1 l0 l1 x x₁ = begin
                                     record { d = a0 ∷ l0 } ≡⟨ cong (λ z → record { d = a0 ∷ z }) x₁ ⟩
                                     record { d = a0 ∷ l1 } ≡⟨ cong (λ z → record { d = z ∷ l1 }) x ⟩
                                     record { d = a1 ∷ l1 } ∎

dummy-list-eq : {a0 a1 : Dummy} → a0 ≡ a1 → Dummy.d a0 ≡ Dummy.d a1
dummy-list-eq  = cong Dummy.d

dummy-lem : (a0 a1 : Dummy) → (l0 l1 : List Dummy) → a0 ≡ a1 → record { d = l0 } ≡ record { d = l1 } → record { d = (a0 ∷ l0) } ≡ record { d = (a1 ∷ l1) }
dummy-lem a0 a1 l0 l1 x x₁ with dummy-list-eq x₁
... | p = dummy-append-eq a0 a1 l0 l1 x p

=-dec-dum : Decidable {A = Dummy} _≡_
=-dec-dum record { d = [] } record { d = [] } = yes refl
=-dec-dum record { d = (x ∷ d₁) } record { d = [] } = no (λ ())
=-dec-dum record { d = [] } record { d = (x ∷ d) } = no (λ ())
=-dec-dum record { d = (x₁ ∷ d₁) } record { d = (x ∷ d) } with =-dec-dum record { d = d₁ } record { d = d }
...                                                          | no ¬p = no lem
  where
  lem : (x : record { d = x₁ ∷ d₁ } ≡ record { d = x ∷ d }) → ⊥
  lem refl = ¬p refl
...                                                          | yes p with =-dec-dum x₁ x
... | no ¬q = no lem
  where
  lem : (x : record { d = x₁ ∷ d₁ } ≡ record { d = x ∷ d }) → ⊥
  lem refl = ¬q refl
... | yes q = yes (dummy-lem x₁ x d₁ d q p)

