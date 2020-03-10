module dag-v3 where

open import Data.Nat
open import Data.Fin using (Fin ; fromℕ)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.Maybe using (Maybe ; nothing ; just)

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


_n0 : AcyclicGraphNode ℕ ℕ
_n0 = n[ 0 , [] ]n

_n1 : AcyclicGraphNode ℕ ℕ
_n1 = n[ 1 , ((10 , _n0) ∷ []) ]n

_g = g[ _n1 ]g


