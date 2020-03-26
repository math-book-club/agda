module Interval where
open import Data.Nat
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.All
open import Data.Sum
open import Level using (0ℓ; Level)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; False; toWitness; fromWitness; fromWitnessFalse)
open import Relation.Nullary.Negation
open import Relation.Nullary.Sum
open import Relation.Nullary.Product
open import Data.Empty
open import Data.Product

record Interval : Set where
  constructor [_▹_]
  field
    lower : ℕ
    size : ℕ

∣_∣ : Interval → ℕ
∣_∣ i = Interval.size i

⌈_⌉ : Interval → ℕ
⌈_⌉ i = Interval.lower i + Interval.size i

⌊_⌋ : Interval → ℕ
⌊_⌋ i = Interval.lower i

_≟Interval_ : Decidable {A = Interval} _≡_
[ lower ▹ size ] ≟Interval [ lower₁ ▹ size₁ ] with lower ≟ lower₁ | size ≟ size₁
...                                              | yes p          | yes q = yes
                                                                              (begin
                                                                               [ lower ▹ size ] ≡⟨ cong ([_▹_] lower) q ⟩
                                                                               [ lower ▹ size₁ ] ≡⟨ cong (λ z → [ z ▹ size₁ ]) p ⟩
                                                                               [ lower₁ ▹ size₁ ] ∎)
...                                              | no ¬p          | yes q = no lem
  where
  lem : (x : [ lower ▹ size ] ≡ [ lower₁ ▹ size₁ ]) → ⊥
  lem refl = ¬p refl
...                                              | yes p          | no ¬q = no lem
  where
  lem : (x : [ lower ▹ size ] ≡ [ lower₁ ▹ size₁ ]) → ⊥
  lem refl = ¬q refl
...                                              | no ¬p          | no ¬q = no lem
  where
  lem : (x : [ lower ▹ size ] ≡ [ lower₁ ▹ size₁ ]) → ⊥
  lem refl = ¬q refl

module _ where
  i₀ = [ 2 ▹ 4 ]
  i₁ = [ 4 ▹ 6 ]
  i₂ = [ 11 ▹ 5 ]
  i₃ = [ 1 ▹ 10 ]

data _<<_ : Rel Interval 0ℓ where
  strictly-less : {l r : Interval} → {proof : True (⌈ l ⌉ <? ⌊ r ⌋)} → l << r

_ : i₀ << i₂
_ = strictly-less

--_ : i₀ << i₁ -- doesn't compile!
--_ = strictly-less

_<<?_ : Decidable {A = Interval} _<<_
l <<? r with (⌈ l ⌉ <? ⌊ r ⌋)
...        | yes p = yes (strictly-less {proof = fromWitness p})
...        | no ¬p = no lem
  where
  lem : (x : l << r) → ⊥
  lem (strictly-less {proof = p}) = contradiction (toWitness p) ¬p

data _∈_ : REL ℕ Interval 0ℓ where
  contains : {n : ℕ} → {i : Interval} → {proof : True ((n ≤? ⌈ i ⌉) ×-dec (⌊ i ⌋ ≤? n))} → n ∈ i

∈⇒∈p : {n : ℕ} {i : Interval} → n ∈ i → (n ≤ ⌈ i ⌉) × (⌊ i ⌋ ≤ n)
∈⇒∈p (contains {proof = proof}) = toWitness proof

_ : 3 ∈ i₀
_ = contains

--_ : 10 ∈ i₀ -- Doesn't compile!
--_ = contains

_∈?_ : Decidable _∈_
_∈?_ n i with ((n ≤? ⌈ i ⌉) ×-dec (⌊ i ⌋ ≤? n))
...        | yes p = yes (contains {n} {i} {fromWitness p})
...        | no ¬p = no lem
  where
  lem : n ∈ i → ⊥
  lem (contains {proof = p}) = contradiction (toWitness p) ¬p

data _∩_ : Rel Interval 0ℓ where
  intersects : {l r : Interval} → {proof : True ((⌊ l ⌋ ∈? r) ⊎-dec (⌈ l ⌉ ∈? r) ⊎-dec (⌊ r ⌋ ∈? l))} → l ∩ r

_ : i₀ ∩ i₁
_ = intersects

--_ : i₁ ∩ i₂
--_ = intersects -- Yay, doesn't compile!

--¬∩? : Decidable _∩_
--¬∩? l r = ¬ ( l ∩ r )

_∩?_ : Decidable _∩_
_∩?_ l r with ((⌊ l ⌋ ∈? r) ⊎-dec (⌈ l ⌉ ∈? r) ⊎-dec (⌊ r ⌋ ∈? l))
...         | yes p = yes (intersects {l} {r} {fromWitness p})
...         | no ¬p = no lem
  where
  lem : (x : l ∩ r) → ⊥
  lem (intersects {proof = p}) = contradiction (toWitness p) ¬p

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
  all-intersect : {l : List Interval} →  {proof : True (allPairs? _∩?_ l)} → AllIntersect l


_ : AllIntersect (i₀ ∷ i₁ ∷ i₃ ∷ [])
_ = all-intersect

--_ : AllIntersect (i₀ ∷ i₁ ∷ i₃ ∷ i₂ ∷ []) -- Doesn't compile!
--_ = all-intersect


module _ where
  ¬∩ : Rel Interval 0ℓ
  ¬∩ l r = ¬ (l ∩ r)

  ¬∩? : Decidable ¬∩
  ¬∩? l r = ¬? (l ∩? r)

data NoneIntersect : Pred (List Interval) 0ℓ where
  none-intersect : {l : List Interval} → {proof : True (allPairs? ¬∩? l)} → NoneIntersect l

_ : NoneIntersect (i₁ ∷ i₂ ∷ [])
_ = none-intersect

--_ : NoneIntersect (i₁ ∷ i₂ ∷ i₀ ∷ []) -- Doesn't compile!
--_ = none-intersect

NoneIntersect⇒p : {l : List Interval} → NoneIntersect l → AllPairs ¬∩ l
NoneIntersect⇒p (none-intersect {proof = proof}) = toWitness proof

NoneIntersect? : Relation.Unary.Decidable NoneIntersect
NoneIntersect? l with (allPairs? ¬∩? l)
...                  | yes p = yes (none-intersect {l} {fromWitness p})
...                  | no ¬p = no lem
  where
  lem : NoneIntersect l → ⊥
  lem (none-intersect {proof = p}) = contradiction (toWitness p) ¬p
