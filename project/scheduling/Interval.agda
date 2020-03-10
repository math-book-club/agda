module Interval where
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

module _ where
  i₀ = [ 2 ▹ 4 ]
  i₁ = [ 4 ▹ 6 ]
  i₂ = [ 11 ▹ 5 ]
  i₃ = [ 1 ▹ 10 ]


data _∈_ : (n : ℕ) → Interval → Set where
  contains : {n : ℕ} → {i : Interval} → (proof : ((n ≤ Interval.lower i + Interval.size i) × (Interval.lower i ≤ n))) → n ∈ i

module _ where
  checkInRange : (i : Interval) → (n : ℕ) → Dec ((n ≤ Interval.lower i + Interval.size i) × (Interval.lower i ≤ n))
  checkInRange i n with n ≤? Interval.lower i + Interval.size i
  ...                | no ¬p = no (λ z → ¬p (proj₁ z))
  ...                | yes p with  Interval.lower i ≤? n
  ...                           | yes q = yes (p , q)
  ...                           | no ¬q = no (λ z → ¬q (proj₂ z))

construct-contains : {n : ℕ} → {i : Interval} → {proof : True (checkInRange i n)} → n ∈ i
construct-contains {n} {i} {proof} = contains (toWitness proof)


_ : 3 ∈ i₀
_ = construct-contains

--_ : 1 ∈ i₀ -- Doesn't compile!
--_ = construct-contains

_∈?_ : (n : ℕ) → (i : Interval) → Dec (n ∈ i)
_∈?_ n i with checkInRange i n
...         | yes p = yes (contains p)
...         | no ¬p = no lem
  where
  lem : (x : n ∈ i) → ⊥
  lem (contains prf) = ¬p prf


module _ where
  checkIntersect : (l : Interval) → (r : Interval) → Dec ((Interval.lower l ∈ r) ⊎ ((Interval.lower l + Interval.size l) ∈ r) ⊎ (Interval.lower r ∈ l))
  checkIntersect l r with (Interval.lower l) ∈? r
  ...                   | yes p = yes (inj₁ p)
  ...                   | no ¬p with (Interval.lower l + Interval.size l) ∈? r
  ...                              | yes q = yes (inj₂ (inj₁ q))
  ...                              | no ¬q with (Interval.lower r) ∈? l
  ...                                         | yes k = yes (inj₂ (inj₂ k))
  ...                                         | no ¬k = no lem
    where
    lem : ¬ ((Interval.lower l ∈ r) ⊎ ((Interval.lower l + Interval.size l) ∈ r) ⊎ (Interval.lower r ∈ l))
    lem (inj₁ x) = ¬p x
    lem (inj₂ (inj₁ x)) = ¬q x
    lem (inj₂ (inj₂ y)) = ¬k y

data _∩_ : Rel Interval 0ℓ where
  intersects : {l r : Interval} → (proof : ((Interval.lower l ∈ r) ⊎ ((Interval.lower l + Interval.size l) ∈ r) ⊎ (Interval.lower r ∈ l))) → l ∩ r

construct-intersect : {l : Interval} → {r : Interval} → {proof : True (checkIntersect l r)} → l ∩ r
construct-intersect {l} {r} {proof} = intersects (toWitness proof)

_ : i₀ ∩ i₁
_ = construct-intersect


--_ : i₁ ∩ i₂
--_ = construct-intersect -- Yay, doesn't compile!

¬∩ : (l : Interval) → (r : Interval) → Set
¬∩ l r = ¬ ( l ∩ r )


module _ where
  demorgan : {A B : Set} → {DA : Dec A} → {DB : Dec B} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
  demorgan {DA = da} {DB = db} p with da     | db
  ...                                | yes a | yes b = inj₁ (λ x → p (x , b))
  ...                                | no ¬a | yes b = inj₁ (λ x → p (x , b))
  ...                                | yes a | no ¬b = inj₂ (λ x → p (a , x))
  ...                                | no ¬a | no ¬b = inj₁ ¬a

  neg-trans : {A B : Set} → (B → A) → ¬ A → ¬ B
  neg-trans {A} {B} B→A ¬A = λ z → ¬A (B→A z)


data AllIntersect : Pred (List Interval) 0ℓ where
  all-intersect : {l : List Interval} →  AllPairs _∩_ l → AllIntersect l

data NoneIntersect : Pred (List Interval) 0ℓ where
  none-intersect : {l : List Interval} → AllPairs ¬∩ l → NoneIntersect l

_ : AllIntersect ( i₀ ∷ i₁ ∷ [])
_ = all-intersect
      ((intersects
        (inj₂
         (inj₂ (contains (s≤s (s≤s (s≤s (s≤s z≤n))) , s≤s (s≤s z≤n)))))
        ∷ [])
       ∷ [] ∷ [])
