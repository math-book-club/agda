module AcyclicGraph where

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

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

record AcyclicGraphNode (E N : Set) : Set where
  inductive
  constructor n[_,_]n
  field
    value : N
    edges : List (Pair E (AcyclicGraphNode E N))

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

{-
_≟AGN_ : {E N : Set} → {_≟E_ : Decidable {A = E} _≡_} → {_≟N_ : Decidable {A = N} _≡_} → Decidable {A = AcyclicGraphNode E N} _≡_
_≟AGN_ {_≟E_ = _≟E_} {_≟N_} n[ value , edges ]n n[ value₁ , edges₁ ]n with value ≟N value₁
...                                                                      | no ¬p = no lem
  where
  lem : (x : n[ value , edges ]n ≡ n[ value₁ , edges₁ ]n) → ⊥
  lem refl = ¬p refl
...                                                                      | yes p with (≡-dec (_≟Pair_ {_≟A_ = _≟E_} {_≟B_ = _≟AGN_})) edges edges₁
...                                                                                 | no ¬q = no lem
  where
  lem : (x : n[ value , edges ]n ≡ n[ value₁ , edges₁ ]n) → ⊥
  lem refl = ¬q refl
...                                                                                 | yes q = yes
                                                                                                (begin
                                                                                                 n[ value , edges ]n ≡⟨ cong (n[_,_]n value) q ⟩
                                                                                                 n[ value , edges₁ ]n ≡⟨ cong (λ z → n[ z , edges₁ ]n) p ⟩
                                                                                                 n[ value₁ , edges₁ ]n ∎)
                                                                                                 -}
_≟AGN_ : {E N : Set} → {_≟E_ : Decidable {A = E} _≡_} → {_≟N_ : Decidable {A = N} _≡_} → Decidable {A = AcyclicGraphNode E N} _≡_
_≟AGN_ {_≟E_ = _≟E_} {_≟N_} n[ value , [] ]n n[ value₁ , [] ]n with value ≟N value₁
...                                                               | no ¬p = no lem
  where
  lem : (x : n[ value , [] ]n ≡ n[ value₁ , [] ]n) → ⊥
  lem refl = ¬p refl
...                                                               | yes p = yes (cong (λ z → n[ z , [] ]n) p)
_≟AGN_ {_≟E_ = _≟E_} {_≟N_} n[ value , [] ]n n[ value₁ , x ∷ edges₁ ]n = no λ ()
_≟AGN_ {_≟E_ = _≟E_} {_≟N_} n[ value , x ∷ edges ]n n[ value₁ , [] ]n = no λ ()
_≟AGN_ {_≟E_ = _≟E_} {_≟N_} n[ value , x ∷ edges ]n n[ value₁ , x₁ ∷ edges₁ ]n with value ≟N value₁
...                                                                               | no ¬p = no lem
  where
  lem : (x : n[ value , x ∷ edges ]n ≡ n[ value₁ , x₁ ∷ edges₁ ]n) → ⊥
  lem refl = ¬p refl
...                                                                               | yes p with _≟AGN_ {_≟E_ = _≟E_} {_≟N_ = _≟N_} n[ value , edges ]n n[ value₁ , edges₁ ]n
...                                                                                          | no ¬q = no lem
  where
  lem : (x : n[ value , x ∷ edges ]n ≡ n[ value₁ , x₁ ∷ edges₁ ]n) → ⊥
  lem refl = ¬q refl
_≟AGN_ {_≟E_ = _≟E_} {_≟N_} n[ value , (first , second) ∷ edges ]n n[ value₁ , (first₁ , second₁) ∷ edges₁ ]n | yes p | yes q with first ≟E first₁
...                                                                                                                              | no ¬z = no lem
  where
  lem : (x
           : n[ value , (first , second) ∷ edges ]n ≡
             n[ value₁ , (first₁ , second₁) ∷ edges₁ ]n) →
          ⊥
  lem refl = ¬z refl
...                                                                                                                              | yes z with _≟AGN_  {_≟E_ = _≟E_} {_≟N_} second second₁
...                                                                                                                                         | no ¬w = no lem
  where
  lem : (x
           : n[ value , (first , second) ∷ edges ]n ≡
             n[ value₁ , (first₁ , second₁) ∷ edges₁ ]n) →
          ⊥
  lem refl = ¬w refl
...                                                                                                                                         | yes w = yes (agn-append p z w (agn-eq-to-list-eq q))
  where
  pair-append : {A B : Set} {a0 a1 : A} {b0 b1 : B} → a0 ≡ a1 → b0 ≡ b1 → a0 , b0 ≡ a1 , b1
  pair-append {A} {B} {a0} {a1} {b0} {b1} x x₁ = begin
                       (a0 , b0) ≡⟨ cong (_,_ a0) x₁ ⟩
                       (a0 , b1) ≡⟨ cong (λ z → z , b1) x ⟩ (a1 , b1) ∎
  list-append : {A : Set} {a0 a1 : A} {l0 l1 : List A} → a0 ≡ a1 → l0 ≡ l1 → a0 ∷ l0 ≡ a1 ∷ l1
  list-append {A} {a0} {a1} {l0} {l1} x x₁ = begin
                       a0 ∷ l0 ≡⟨ cong (_∷_ a0) x₁ ⟩
                       a0 ∷ l1 ≡⟨ cong (λ z → z ∷ l1) x ⟩ a1 ∷ l1 ∎
  agn-append-helper :  {E N : Set} {n0 n1 : N} {l0 l1 : List (Pair E (AcyclicGraphNode E N))} → n0 ≡ n1 → l0 ≡ l1 → n[ n0 , l0 ]n ≡ n[ n1 , l1 ]n
  agn-append-helper {E} {N} {n0} {n1} {l0} {l1} x x₁ = begin
                                                         n[ n0 , l0 ]n ≡⟨ cong (n[_,_]n n0) x₁ ⟩
                                                         n[ n0 , l1 ]n ≡⟨ cong (λ z → n[ z , l1 ]n) x ⟩ n[ n1 , l1 ]n ∎
  agn-eq-to-list-eq : {E N : Set} {n0 n1 : N} {l0 l1 : List (Pair E (AcyclicGraphNode E N))} → n[ n0 , l0 ]n ≡ n[ n1 , l1 ]n → l0 ≡ l1
  agn-eq-to-list-eq refl = refl
  agn-append : {E N : Set} {n0 n1 : N} {e0 e1 : E} {s0 s1 : AcyclicGraphNode E N} {l0 l1 : List (Pair E (AcyclicGraphNode E N))} → n0 ≡ n1 → e0 ≡ e1 → s0 ≡ s1 → l0 ≡ l1 → n[ n0 , (e0 , s0) ∷ l0 ]n ≡ n[ n1 , (e1 , s1) ∷ l1 ]n
  agn-append x x₁ x₂ x₃ = agn-append-helper x (list-append (pair-append x₁ x₂)  x₃)

record AcyclicGraph (E N : Set) : Set where
  constructor g[_]g
  field
    head : AcyclicGraphNode E N

module _ where
  n0 : AcyclicGraphNode ℕ ℕ
  n0 = n[ 0 , [] ]n

  n1 : AcyclicGraphNode ℕ ℕ
  n1 = n[ 1 , ((10 , n0) ∷ []) ]n

  g = g[ n1 ]g

  list-head-guaranteed : {A : Set} → (l : List A) → {p : 1 ≤ (Data.List.length l)} → A
  list-head-guaranteed (x ∷ xs) = x

  -- Equality.
  ll = AcyclicGraphNode.edges n1
  _ : n0 ≡ Pair.second (list-head-guaranteed ll {s≤s z≤n})
  _ = refl


successors : {E N : Set} → AcyclicGraphNode E N → List (AcyclicGraphNode E N)
successors n = Data.List.map Pair.second (AcyclicGraphNode.edges n)

-- This version doesn't pass the termination checker :(
-- descendants : {E N : Set} → AcyclicGraphNode E N → List (AcyclicGraphNode E N)
-- descendants n = concat (map descendants (successors n)) ++ (successors n)

open import Data.List.Membership.DecPropositional hiding (_∈_)
open import Relation.Binary
open import Relation.Nullary

list-remove-duplicates : {A : Set} → List A → Decidable {A = A} _≡_ → List A
list-remove-duplicates l deq = remove-duplicates-impl [] l deq
  where
  remove-duplicates-impl : {A : Set} → List A → List A → Decidable {A = A} _≡_ → List A
  remove-duplicates-impl l [] deq = l
  remove-duplicates-impl l (x ∷ xs) deq with (_∈?_ deq) x l
  ...                                      | yes p = remove-duplicates-impl l xs deq
  ...                                      | no ¬p = remove-duplicates-impl (x ∷ l) xs deq


{-
list-contains-duplicates : {A : Set} → (l : List A) → (deq : Decidable {A = A} _≢_) → AllPairs deq l
list-contains-duplicates l = {!!}
-}
{-
_ : {A : Set} (deq : Decidable {A = A} _≡_) → Relation.Nullary.Decidable.True ((_∈?_ deq) 1 (1 ∷ []))
_ = {!!}
-}

descendants : {E N : Set} → AcyclicGraphNode E N → List (AcyclicGraphNode E N)
descendants n[ _ , [] ]n = []
descendants n[ value , (_ , child) ∷ edges ]n = descendants child ++ (child ∷ descendants n[ value , edges ]n)

all-nodes : {E N : Set} → {_≟E_ : Decidable {A = E} _≡_} → {_≟N_ : Decidable {A = N} _≡_} → AcyclicGraph E N → List (AcyclicGraphNode E N)
all-nodes {_≟E_ = _≟E_} {_≟N_ = _≟N_} g[ head ]g = list-remove-duplicates (descendants head) (_≟AGN_ {_≟E_ = _≟E_} {_≟N_ = _≟N_})

data _↝_ : {E N : Set} → Rel (AcyclicGraphNode E N) 0ℓ where
  depends-on : {E N : Set} → (_≟E_ : Decidable {A = E} _≡_) → (_≟N_ : Decidable {A = N} _≡_) → {parent : AcyclicGraphNode E N} → {child :  AcyclicGraphNode E N} → {proof : True ((_∈?_ (_≟AGN_ {_≟E_ = _≟E_} {_≟N_ = _≟N_})) child (descendants parent))} → parent ↝ child


_ : n1 ↝ n0
_ = depends-on Data.Nat._≟_ Data.Nat._≟_

--_ : n0 ↝ n1 -- Doesn't compile!
--_ = depends-on Data.Nat._≟_ Data.Nat._≟_

↝⇒p : {E N : Set} {p c : AcyclicGraphNode E N} → p ↝ c → c ∈ (descendants p)
↝⇒p (depends-on _≟E_ _≟N_ {proof = p}) = toWitness p


_↝?_ : {E N : Set} → (_≟E_ : Decidable {A = E} _≡_) → (_≟N_ : Decidable {A = N} _≡_) → Decidable {A = AcyclicGraphNode E N} _↝_
(_≟E_ ↝? _≟N_) parent child with (_∈?_ (_≟AGN_ {_≟E_ = _≟E_} {_≟N_ = _≟N_})) child (descendants parent)
...                            | yes p = yes (depends-on _≟E_ _≟N_ {proof = fromWitness p})
...                            | no ¬p = no lem
  where
  lem : (x : parent ↝ child) → ⊥
  lem (depends-on _≟E_ _≟N_ {proof = p}) = contradiction (toWitness p)  ¬p
