module dag-v2 where

open import Data.Nat
open import Data.Fin using (Fin ; fromℕ)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.Maybe using (Maybe ; nothing ; just)

-- Static assertions on type.
n-is-even : ℕ → Bool
n-is-even zero = true
n-is-even (suc (suc n)) = n-is-even n
n-is-even (suc n) = false

_ : n-is-even 5 ≡ false
_ = refl

_ : n-is-even 6 ≡ true
_ = refl


list-is-even : List ℕ → Bool
list-is-even l = all n-is-even l

_ : list-is-even (2 ∷ 4 ∷ []) ≡ true
_ = refl

_ : list-is-even (2 ∷ 3 ∷ []) ≡ false
_ = refl

-- a type-level assertion on a function
my-list-func : (L : List ℕ) → {{_ : list-is-even L ≡ true}} → List ℕ
my-list-func l = map suc l

_ : my-list-func (2 ∷ 4 ∷ []) ≡ (3 ∷ 5 ∷ [])
_ = refl -- works, as expected

--_ : my-list-func (2 ∷ 5 ∷ [])
--_ = (3 ∷ 6 ∷ []) -- doesn't compile, as expected

test = my-list-func (2 ∷ 5 ∷ []) -- this line compiles !?
--manipulate = map suc test -- it only seems to start failing when I try to use the result
--assert = test ≡  (3 ∷ 6 ∷ []) -- happens here as well


-------------------------------------------
-- Graph stuff
-------------------------------------------
data Edge (E : Set) : Set where
  e[_,_]e : E → ℕ → Edge E

data Node (E N : Set) : Set where
  n[_,_]n : N → (List (Edge E)) → Node E N


infixr 3 _&_

data Graph (E : Set) (N : Set) : ℕ → Set where
  ∅  : Graph E N zero
  _&_ : {n : ℕ} →  Node E N → Graph E N n → Graph E N (suc n)

-- How do we pull n down from type space to value space?
num-nodes : {E N : Set} {n : ℕ} → Graph E N n → ℕ
num-nodes {_} {_} {n} (_) = n

map-nodes : {E N : Set} {R : Set} {n : ℕ} → (Node E N →  R) → Graph E N n → List R
map-nodes _ ∅ = []
map-nodes f (node & rest) = (f node) ∷ (map-nodes f rest)

map-edges : {E N : Set} {R : Set} {n : ℕ} → (Edge E →  R) → Graph E N n → List (List R)
map-edges f g = map-nodes (node-op f) g
  where
  node-op : {E N : Set} {R : Set} → (Edge E → R) → Node E N → List R
  node-op f n[ _ , e ]n = map f e

-- theres gotta be a better way to do this.
list-contains : ℕ → List ℕ → Bool
list-contains n l = any (is-equal n) l
  where
  is-equal : ℕ → ℕ → Bool
  is-equal rhs lhs = ⌊ rhs ≟ lhs  ⌋

get-node-by-ref : {E N : Set} {n : ℕ} → Fin n → Graph E N n → Node E N
get-node-by-ref Fin.zero (node & _) = node -- Magic! agda somehow knows we cover all cases even though we didn't use ∅
get-node-by-ref (Fin.suc i) (node & rest) = get-node-by-ref i rest

graph-is-valid : {E N : Set} {n : ℕ}→ Graph E N n → Bool
graph-is-valid g = all-true (map-edges (has-valid-reference (num-nodes g)) g)
  where
  has-valid-reference : {E : Set} → ℕ → Edge E → Bool
  has-valid-reference max-ref e[ _ , r ]e = ⌊ r <? max-ref ⌋

  all-true : List (List Bool) → Bool
  all-true l = and (map and l)

{-
contains-cycle : {E N : Set} {n : ℕ} → (G : Graph E N n) → {{ _ : graph-is-valid G ≡ true }} → Bool
contains-cycle g = iterate 0 g g
  where
  iterate : {E N : Set} {n : ℕ} → ℕ → Graph E N n → Graph E N n → Bool
  iterate _ _ ∅  = false
  iterate i full-graph (current-node & rest) = (node-contains-cycle full-graph [] i current-node) ∨ (iterate (suc i) full-graph rest)
    where
    node-contains-cycle : {E N : Set} {n : ℕ} → Graph E N n → List ℕ → ℕ → Node E N → Bool
    node-contains-cycle full-graph seen i n[ _ , e ]n = if (list-contains i seen) then true else (map (edge-propagate full-graph (i ∷ seen)) e)
      where
      edge-propagate : {E N : Set} {n : ℕ} → Graph E N n → List ℕ → Edge E → Bool
      edge-propagate full-graph seen e[ _ , r ]e = node-contains-cycle full-graph seen r (get-node-by-ref (Data.Fin.fromℕ≤ r) full-graph)
      -}


-- Tests.
dummy-graph : Graph ℕ ℕ 2
dummy-graph = n[ 1 , (e[ 11 , 1 ]e ∷ []) ]n & n[  2 , (e[ 21 , 0 ]e ∷ []) ]n & ∅

_ : graph-is-valid dummy-graph ≡ true
_ = refl

_ : graph-is-valid (n[ 1 , (e[ 11 , 2 ]e ∷ []) ]n & n[ 2 , (e[ 21 , 0 ]e ∷ []) ]n & ∅) ≡ false
_ = refl

{-
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
-}
