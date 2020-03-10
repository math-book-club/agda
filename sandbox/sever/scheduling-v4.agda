module scheduling-v4 where
open import Data.Nat
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.All
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Sum
open import Level using (0ℓ)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Empty
open import Data.Product

record Interval : Set where
  constructor [_▹_]
  field
    lower : ℕ
    size : ℕ

interval-upper : Interval → ℕ
interval-upper i = Interval.lower i + Interval.size i

i₀ = [ 2 ▹ 4 ]
i₁ = [ 4 ▹ 6 ]
i₂ = [ 11 ▹ 5 ]
i₃ = [ 1 ▹ 10 ]


data _∈_ : (n : ℕ) → Interval → Set where
  contains : {n : ℕ} → {i : Interval} → (proof : ((n ≤ Interval.lower i + Interval.size i) × (Interval.lower i ≤ n))) → n ∈ i

_ : 3 ∈ i₀
_ = contains (s≤s (s≤s (s≤s z≤n)) , s≤s (s≤s z≤n))


data _∩_ : Rel Interval 0ℓ where
  intersects : {l r : Interval} → (proof : ((Interval.lower l ∈ r) ⊎ ((Interval.lower l + Interval.size l) ∈ r) ⊎ (Interval.lower r ∈ l))) → l ∩ r


data AllIntersect : Pred (List Interval) 0ℓ where
  all-intersect : {l : List Interval} →  AllPairs _∩_ l → AllIntersect l

{-
module _ where
  checkInRange : {l u : ℕ} → [ l ▹ u ] → (n : ℕ) → Dec ((n ≤ l + u) × (l ≤ n))
  checkInRange {l} {u} i n with n ≤? l + u
  ...                | no ¬p = no (λ z → ¬p (proj₁ z))
  ...                | yes p with n ≥? l
  ...                           | yes q = yes (p , q)
  ...                           | no ¬q = no (λ z → ¬q (proj₂ z))


data _∈_ : {l u : ℕ} → (n : ℕ) → [ l ▹ u ] → Set where
  contains : {l u : ℕ} → {n : ℕ}→ {i : [ l ▹ u ]} → (proof : ((n ≤ l + u) × (l ≤ n))) → n ∈ i

construct-contains : {l u : ℕ} → {n : ℕ} → {i : [ l ▹ u ]} → {proof : True (checkInRange i n)} → n ∈ i
construct-contains {l} {u} {n} {i} {proof} = contains (toWitness proof)

_ : 7 ∈ i₁
_ = contains
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) ,
       s≤s (s≤s (s≤s (s≤s z≤n)))) -- alernatively, construct-contains

--_ : 11 ∈ i₁ -- Yay, doesn't compile!
--_ = construct-contains


_∈?_ : {l u : ℕ} → (n : ℕ) → (i : [ l ▹ u ]) → Dec (n ∈ i)
_∈?_ {l} {u} n i with checkInRange i n
...                 | yes p = yes (contains p)
...                 | no ¬p = no lem
  where
  lem : (x : n ∈ i) → ⊥
  lem (contains prf) = ¬p prf


module _ where
  checkIntersect : {ll lu rl ru : ℕ} → (l : [ ll ▹ lu ]) → (r : [ rl ▹ ru ]) → Dec ((ll ∈ r) ⊎ (lu ∈ r))
  checkIntersect {ll} {lu} {rl} {ru} l r with ll ∈? r
  ...                                       | yes p = yes (inj₁ p)
  ...                                       | no ¬p with lu ∈? r
  ...                                                  | yes q = yes (inj₂ q)
  ...                                                  | no ¬q = no lem
    where
    lem : (x : (ll ∈ r) ⊎ (lu ∈ r)) → ⊥
    lem (inj₁ ll∈r) = ¬p ll∈r
    lem (inj₂ lu∈r) = ¬q lu∈r

open import Relation.Binary
data _∩_ : {ll lu rl ru : ℕ} → (l : [ ll ▹ lu ]) → (r : [ rl ▹ ru ]) → Set where
  intersect : {ll lu rl ru : ℕ} → {l : [ ll ▹ lu ]} → {r : [ rl ▹ ru ]} → (proof : ((ll ∈ r) ⊎ (lu ∈ r))) → l ∩ r

construct-intersect : {ll lu rl ru : ℕ} → {l : [ ll ▹ lu ]} → {r : [ rl ▹ ru ]} → {proof : True (checkIntersect l r)} → l ∩ r
construct-intersect {ll} {lu} {rl} {ru} {l} {r} {proof} = intersect (toWitness proof)

_ : i₀ ∩ i₁
_ = intersect (inj₂
                 (contains (s≤s (s≤s (s≤s (s≤s z≤n))) , s≤s (s≤s (s≤s (s≤s z≤n)))))) -- alternatively, construct-intersect

--_ : i₁ ∩ i₂
--_ = construct-intersect -- Yay, doesn't compile!

¬∩ : {ll lu rl ru : ℕ} → (l : [ ll ▹ lu ]) → (r : [ rl ▹ ru ]) → Set
¬∩ l r = ¬ ( l ∩ r )


module _ where
  demorgan : {A B : Set} → {DA : Dec A} → {DB : Dec B} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
  demorgan {DA = da} {DB = db} p with da     | db
  ...                                | yes a | yes b = inj₁ (λ x → p (x , b))
  ...                                | no ¬a | yes b = inj₁ (λ x → p (x , b))
  ...                                | yes a | no ¬b = inj₂ (λ x → p (a , x))
  ...                                | no ¬a | no ¬b = inj₁ ¬a

  demorgan' : {A B : Set} → {DA : Dec A} → {DB : Dec B} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
  demorgan' {DA = da} {DB = db} p with da    | db
  ...                                | no ¬a | yes b = λ z → ¬a (proj₁ z)
  ...                                | yes a | no ¬b = λ z → ¬b (proj₂ z)
  ...                                | no ¬a | no ¬b = λ z → ¬b (proj₂ z)
  ...                                | yes a | yes b with p
  ...                                                   | inj₁ ¬aa = λ z → ¬aa (proj₁ z)
  ...                                                   | inj₂ ¬bb = λ z → ¬bb (proj₂ z)


  neg-trans : {A B : Set} → (B → A) → ¬ A → ¬ B
  neg-trans {A} {B} B→A ¬A = λ z → ¬A (B→A z)

  p⇒¬p : { l u n : ℕ } →  ¬ ((n ≤ l + u) × (l ≤ n)) → ((n > l + u) ⊎ (l > n))
  p⇒¬p {l} {u} {n} p with demorgan {DA = n ≤? l + u} {DB = l ≤? n} p
  ...                  | (inj₁ ¬n≤l+u) = (inj₁ (Data.Nat.Properties.≰⇒> ¬n≤l+u))
  ...                  | (inj₂ ¬l≤n)   = (inj₂ (Data.Nat.Properties.≰⇒> ¬l≤n))

  postulate
    ¬p⇒p : { l u n : ℕ } → ((n > l + u) ⊎ (l > n)) → ¬ ((n ≤ l + u) × (l ≤ n))
  --¬p⇒p (inj₁ x) p = contradiction {!!} {!!}
  --¬p⇒p (inj₂ y) p = {!!}

∈⇒p : { l u n : ℕ } → {i : [ l ▹ u ]} → n ∈ i → ((n ≤ l + u) × (l ≤ n))
∈⇒p (contains p) = p

p⇒∈ : { l u n : ℕ } → {i : [ l ▹ u ]} → ((n ≤ l + u) × (l ≤ n)) → n ∈ i
p⇒∈ {l} {u} {n} p = contains p

_∉_ : { l u : ℕ } → ℕ → [ l ▹ u ] → Set
_∉_ n i = ¬ (n ∈ i)

∉⇒¬p : { l u n : ℕ } → {i : [ l ▹ u ]} → n ∉ i → ((n > l + u) ⊎ (l > n))
∉⇒¬p n∉i = p⇒¬p (neg-trans p⇒∈ n∉i)


¬p⇒∉ : { l u n : ℕ } → {i : [ l ▹ u ]} → ((n > l + u) ⊎ (l > n)) → n ∉ i
¬p⇒∉ ¬p = neg-trans ∈⇒p (¬p⇒p ¬p)




IntervalList = List (∃[ l ] (∃[ u ] ([ l ▹ u ])))

data ScheduleList : IntervalList → Set₁

data NoIntersections {l u : ℕ} (p : [ l ▹ u ]) : Pred (IntervalList) (0ℓ) where
  ni-trivial :  NoIntersections p []
  ni-cons : {l' u' : ℕ} →
            {q : [ l' ▹ u' ]} → {t : IntervalList} →
            (¬ (p ∩ q))       → (NoIntersections p t) →
            NoIntersections p (( -, -, q) ∷ t)


data _∩'_ : Rel (∃[ l ] (∃[ u ] ([ l ▹ u ]))) 0ℓ where
   intersect : {ll lu rl ru : ℕ} → {l : [ ll ▹ lu ]} → {r : [ rl ▹ ru ]} → (proof : ((ll ∈ r) ⊎ (lu ∈ r))) → (ll , lu , interval)  ∩' (rl , ru , interval)

ii : (∃[ l ] (∃[ u ] ([ l ▹ u ])))
ii = (2 , 4 , interval)

iii : (∃[ l ] (∃[ u ] ([ l ▹ u ])))
iii = (4 , 6 , interval)

interval-erasure : { l u : ℕ } → (i : [ l ▹ u ]) → (∃[ x ] (∃[ y ] ([ x ▹ y ])))
interval-erasure {l} {u} i = l , u , interval



data ScheduleList where
  emp : ScheduleList ([])
  cons : {l u : ℕ} → {Tail : IntervalList} →
         (p : [ l ▹ u ]) →
         {tail : ScheduleList (Tail)} →
         .(NoIntersections p Tail) →
         ScheduleList ((-, -, p) ∷ Tail)

module _ where
  a : [ 1 ▹ 2 ]
  a = interval
  b : [ 4 ▹ 1 ]
  b = interval
  c : [ 10 ▹ 1 ]
  c = interval

  ab : IntervalList
  ab = (-, -, a) ∷ (-, -, b) ∷ []

  --c¬∩ : NoIntersections c ab
  
-}
