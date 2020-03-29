module Schedule where
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
open import Interval
open import Pair
open import AcyclicGraph
open import Agda.Builtin.Unit
open import DecidableEquality

open DecEq {{...}}

Runnable = AcyclicGraphNode ⊤ Interval

data _↝⇒<<_ : Rel Runnable 0ℓ where
  dependency-implies-ordering : {l r : Runnable} → {proof : True (((l ↝? r) ×-dec (get-val l <<? get-val r)) ⊎-dec ¬? (l ↝? r))} → l ↝⇒<< r

↝⇒<<⇒p : {l r : Runnable} → l ↝⇒<< r → ((l ↝ r) × (get-val l << get-val r) ⊎ (¬ l ↝ r))
↝⇒<<⇒p (dependency-implies-ordering {proof = p}) = toWitness p

_↝⇒<<?_ : Decidable {A = Runnable} _↝⇒<<_
l ↝⇒<<? r with  ((l ↝? r) ×-dec (get-val l <<? get-val r)) ⊎-dec ¬? (l ↝? r)
...          | yes p = yes (dependency-implies-ordering {proof = fromWitness p})
...          | no ¬p = no lem
  where
  lem : (x : l ↝⇒<< r) → ⊥
  lem (dependency-implies-ordering {proof = p}) = contradiction (toWitness p) ¬p


data _↝⇔<<_ : Rel Runnable 0ℓ where
  bidierctional-dependency-implies-ordering : {l r : Runnable} → {proof : True ((l ↝⇒<<? r) ×-dec (r ↝⇒<<? l))} → l ↝⇔<< r

_↝⇔<<?_ : Decidable {A = Runnable} _↝⇔<<_
l ↝⇔<<? r with ((l ↝⇒<<? r) ×-dec (r ↝⇒<<? l))
...          | yes p = yes (bidierctional-dependency-implies-ordering {proof = fromWitness p})
...          | no ¬p = no lem
  where
  lem : (x : l ↝⇔<< r) → ⊥
  lem (bidierctional-dependency-implies-ordering {proof = p}) = contradiction (toWitness p) ¬p

record Schedule : Set where
  constructor s[_]s
  field
    schedule : AcyclicGraph ⊤ Interval
    {no-interval-intersection} : True (NoneIntersect? (map get-val (all-nodes schedule)))
    {forall-dependencies-imply-ordering} : True (allPairs? _↝⇔<<?_ (all-nodes schedule))

schedule⇒no-interval-intersection : (s : Schedule) → NoneIntersect (map get-val (all-nodes (Schedule.schedule s)))
schedule⇒no-interval-intersection s = toWitness (Schedule.no-interval-intersection s)

schedule⇒forall-dependencies-imply-ordering : (s : Schedule) → AllPairs _↝⇔<<_ (all-nodes (Schedule.schedule s))
schedule⇒forall-dependencies-imply-ordering s = toWitness (Schedule.forall-dependencies-imply-ordering s)

r0 : Runnable
r0 = n[ [ 7 ▹ 3 ] , [] ]n

r1 : Runnable
r1 = n[ [ 0 ▹ 4 ] , ((tt , r0) ∷ []) ]n

r2 : Runnable
r2 = n[ [ 6 ▹ 2 ] , (tt , r0) ∷ [] ]n

r3 : Runnable
r3 = n[ [ 11 ▹ 2 ] , (tt , r0) ∷ [] ]n

g0 = g[ r1 ]g
s0 = s[ g0 ]s

-- g1 = g[ r2 ]g
-- s1 = s[ g1 ]s -- doesn't compile: interval overlap!

--g2 = g[ r3 ]g
--s2 = s[ g2 ]s -- doesn't compile: dependencies out of order!

