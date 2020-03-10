module schedulingt where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary.Decidable
open import Data.Bool
open import Data.Maybe

record Runnable : Set where
  constructor Runnable[_]
  field
    duration      : ℕ

-- Dummy type for dependencies.
data Dependency : Set where
  dependency : Dependency

record ScheduledRunnable : Set where
  constructor ScheduledRunnable[_-_]
  field
    start : ℕ
    end : ℕ

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 50 _::_

sample-list : List ℕ
sample-list  = 2 :: 1 :: []

l-elem-i : {A : Set} → List A → ℕ → Maybe A
l-elem-i [] _ = nothing
l-elem-i (x :: _) zero = just x
l-elem-i (_ :: xs) (suc i) = l-elem-i xs i

_ : l-elem-i  (2 :: []) 0 ≡  just 2
_ = refl

l-length : {A : Set} → List A → ℕ
l-length [] = 0
l-length (_ :: xs) = 1 + l-length xs

_ : l-length (1 :: 2 :: []) ≡ 2
_ = refl

l-map : {A B : Set} → (A →  B) →  List A → List B
l-map _ [] = []
l-map f (x :: xs) = (f x) :: (l-map f xs)

_ : l-map ( 1 +_ ) (1 :: 2 :: []) ≡ 2 :: 3 :: []
_ = refl

l-all : List Bool →  Bool
l-all [] = true
l-all (x :: xs) = x ∧ (l-all xs)

_ : l-all (true :: true :: false :: true :: []) ≡ false
_ = refl

_ : l-all (true :: true :: true :: []) ≡ true
_ = refl


l-any : List Bool →  Bool
l-any [] = false
l-any (x :: xs) = x ∨ (l-any xs)

_ : l-any (true :: true :: false :: true :: []) ≡ true
_ = refl

_ : l-any (false :: false :: []) ≡ false
_ = refl

_ : l-any [] ≡ false
_ = refl

-- TODO: how to write this for the general case?
l-contains : List ℕ → ℕ → Bool
l-contains [] _ = false
l-contains (x :: xs) a = if ( ⌊ a Data.Nat.≟ x ⌋ ) then true else (l-contains xs a)

_ : l-contains (1 :: 3 :: []) 3 ≡ true
_ = refl

_ : l-contains (1 :: 3 :: []) 5 ≡ false
_ = refl

-- Static assertions on type.
n-is-even : ℕ → Bool
n-is-even zero = true
n-is-even (suc (suc n)) = n-is-even n
n-is-even (suc n) = false

_ : n-is-even 5 ≡ false
_ = refl

_ : n-is-even 6 ≡ true
_ = refl

data EvenList : Set where
  even-list : (x : List ℕ ) →  {{_ : l-all ( l-map n-is-even x) ≡ true }} → EvenList

_ = even-list (2 :: 4 :: [])

--_ = l-map (λ x →  x) (even-list (2 :: 4 :: []))


-------------------------------------------
-- Graph stuff
-------------------------------------------

data Edge (E : Set) : Set where
  edge-context : E →  ℕ → Edge E

e-edge-value : {E : Set} → Edge E →  E
e-edge-value (edge-context e _) = e

e-edge-index : {E : Set} → Edge E → ℕ
e-edge-index (edge-context _ n) = n


data Graph (E : Set) (N : Set) : Set where
  ∅ : Graph E N
  node-context : N → List (Edge E) → Graph E N → Graph E N

g-num-nodes : {E N : Set} → Graph E N → ℕ
g-num-nodes ∅ = 0
g-num-nodes (node-context _ _ rest) = 1 + g-num-nodes rest

dummy-graph : Graph ℕ ℕ
dummy-graph = node-context 4 ((edge-context 11 0) :: []) (node-context 5 ((edge-context 10 0) :: []) ∅ )

_ : g-num-nodes dummy-graph ≡  2
_ = refl


g-num-edges : {E N : Set} → Graph E N → ℕ
g-num-edges ∅  = 0
g-num-edges (node-context _ edges rest) = l-length edges + g-num-edges rest

_ : g-num-edges dummy-graph ≡  2
_ = refl

g-node-n : {E N : Set} → Graph E N → ℕ →  Maybe N
g-node-n ∅ _ = nothing
g-node-n (node-context node _ _) zero = just node
g-node-n (node-context _ _ rest) (suc n) = g-node-n rest n

_ : g-node-n dummy-graph 1 ≡ just 5
_ = refl

--TODO: how do we make it so that there is no maybe, and that we error out here?
g-edge-n : {E N : Set} →  (graph : Graph E N) → (index : ℕ) →  List (Edge E)
g-edge-n ∅ _ = [] -- shouldn't be possible.
g-edge-n (node-context _ e _) zero = e
g-edge-n (node-context _ _ rest) (suc n) = g-edge-n rest n

_ : g-edge-n dummy-graph 1 ≡ ((edge-context 10 0) :: [])
_ = refl

e-comparison-helper : {E : Set} → ℕ → Edge E → Bool
e-comparison-helper n (edge-context _ i) = ⌊ i Data.Nat.<? n ⌋

g-edges-valid-helper :  { E N : Set } → Graph E N → ℕ → Bool
g-edges-valid-helper ∅  _ = true
g-edges-valid-helper (node-context node edges rest) n = l-all ( l-map (e-comparison-helper n) edges ) ∧ g-edges-valid-helper rest n

g-edges-valid : { E N : Set } → Graph E N → Bool
g-edges-valid ∅ = true
g-edges-valid (node-context node edges rest) = let full-graph = node-context node edges rest
                                             in g-edges-valid-helper full-graph (g-num-nodes full-graph)

data ValidGraph (E N : Set) : Set where
  valid-graph : (g : Graph E N) → {{_ : g-edges-valid g ≡ true}} → ValidGraph E N

_ = valid-graph dummy-graph
--_ = valid-graph (node-context 4 ((edge-context 11 0) :: []) (node-context 5 ((edge-context 10 5) :: []) ∅ ))



-- function signiature: <current index> <current_edges> <graph> <visited_indices>
-- TODO: checks for whether inputs are valid?
{-# TERMINATING #-} -- TODO: can we get rid of this?
contains-cycle-node-traverse : {E N : Set} → ℕ → List (Edge E) →  Graph E N → List ℕ → Bool
contains-cycle-node-traverse n e g seen = if (l-contains seen n) then true else (l-any (l-map (contains-cycle-edge-propagate g (n :: seen)) e))
    where
    contains-cycle-edge-propagate : {E' N' : Set} →  Graph E' N' → List ℕ → Edge E' → Bool
    contains-cycle-edge-propagate g' seen' (edge-context _ n') = contains-cycle-node-traverse n' (g-edge-n g' n') g' seen'

contains-cycle : {E N : Set} → Graph E N → Bool
contains-cycle ∅ = false
contains-cycle (node-context n e rest) = let g = node-context n e rest
    in contains-cycle-helper g g 0
    where
    contains-cycle-helper : {E' N' : Set} → Graph E' N' → Graph E' N' → ℕ → Bool
    contains-cycle-helper _ ∅ _ = false
    contains-cycle-helper full-graph (node-context _ e' rest') index = (contains-cycle-node-traverse index e' full-graph []) ∨ (contains-cycle-helper full-graph rest' (suc index))

_ : contains-cycle dummy-graph ≡ true
_ = refl

_ : contains-cycle {ℕ} {ℕ} ∅ ≡ false
_ = refl

dummy-dag : Graph ℕ ℕ
dummy-dag = node-context 0 ((edge-context 1 1) :: []) (node-context 1 [] ∅)

_ : contains-cycle dummy-dag ≡ false
_ = refl


data AcyclicGraph (E N : Set) : Set where
  acyclic-graph : (g : Graph E N) → {{_ : contains-cycle g ≡ false }} → AcyclicGraph E N

_ = acyclic-graph dummy-dag
--_ = acyclic-graph dummy-graph
