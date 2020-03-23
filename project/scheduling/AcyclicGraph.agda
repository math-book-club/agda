module AcyclicGraph where

open import Data.Nat
open import Data.Fin using (Fin ; fromℕ)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or; _++_ )
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.List using (List; concat; map; length)
open import Data.List.Membership.Propositional

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
successors n = map Pair.second (AcyclicGraphNode.edges n)

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

open import Data.List.Relation.Unary.AllPairs
--allpairs-dec : {A : Set} → (l : List A) → (deq : Decidable {A = A} _≢_) → AllPairs deq l

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

data _↝_ : {E N : Set} → AcyclicGraphNode E N → AcyclicGraphNode E N → Set where
  depends-on : {E N : Set} → {parent : AcyclicGraphNode E N} → {child :  AcyclicGraphNode E N} → (proof : child ∈ (descendants parent)) → parent ↝ child

module _ where
  open import Data.List.Relation.Unary.Any using (Any)

  _ : n1 ↝ n0
  _ = depends-on (Any.here refl)


