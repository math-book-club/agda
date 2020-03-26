module Schedule where
open import Data.Nat
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.All
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Sum
open import Level using (0ℓ)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; False; ⌊_⌋; toWitness)
open import Relation.Nullary.Negation
open import Data.Empty
open import Data.Product
open import Interval
open import AcyclicGraph
open import Agda.Builtin.Unit


Runnable = AcyclicGraphNode ⊤ Interval

_≟⊤_ : Decidable {A = ⊤} _≡_
tt ≟⊤ tt = yes refl


record Schedule : Set where
  field
    schedule : AcyclicGraph ⊤ Interval
    {no-interval-intersection} : True (NoneIntersect? (Data.List.map AcyclicGraphNode.value (all-nodes {_≟E_ = _≟⊤_} {_≟N_ = _≟Interval_} schedule)))
