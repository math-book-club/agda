module scheduling-v2 where
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Unit
open import Data.Empty
open import Data.Product

data [_▹_] : ℕ → ℕ → Set where
  interval : { s d : ℕ } →  [ s ▹ d ]

i₁ : [ 4 ▹ 6 ]
i₁ = interval
i₂ : [ 11 ▹ 5 ]
i₂ = interval

module _ where
  checkNoIntersect : { ls ld rs rd : ℕ } → [ ls ▹ ld ] → [ rs ▹ rd ] →
                     Dec ((ls > (rs + rd)) ⊎ ((ls + ld) < rs))
  checkNoIntersect {ls} {ld} {rs} {rd} l r with ls >? (rs + rd)
  ...                                      | yes p = yes (inj₁ p)
  ...                                      | no ¬p with ((ls + ld) <? rs)
  ...                                              | yes q = yes (inj₂ q)
  ...                                              | no ¬q = no lem
    where
      lem : ¬ ((ls > (rs + rd)) ⊎ ((ls + ld) < rs))
      lem (inj₁ ls>rs+rd) = ¬p ls>rs+rd
      lem (inj₂ ls+ld<rs) = ¬q ls+ld<rs


data NoIntersect : { ls ld rs rd : ℕ } →  [ ls ▹ ld ] →  [ rs ▹ rd ] → Set where
  mk : { ls ld rs rd : ℕ } →
         {l : [ ls ▹ ld ]} → {r : [ rs ▹ rd ]} →
         (proof :  (ls > (rs + rd)) ⊎ ((ls + ld) < rs)) →
         NoIntersect l r

construct-no-intersect : { ls ld rs rd : ℕ } → {l : [ ls ▹  ld ]} → {r : [ rs ▹ rd ]} → {proof : True (checkNoIntersect l r)} →  NoIntersect l r
construct-no-intersect {ls} {ld} {rs} {rd} {l} {r} {proof} = mk (toWitness proof)

intersect-prf : (4 > (11 + 5)) ⊎ ((4 + 6) < 11)
intersect-prf = inj₂
                  (s≤s
                   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))

_ : NoIntersect i₁ i₂
_ = construct-no-intersect

{-
data InRange : ℕ → ℕ → Set where
  gn : {ll : ℕ} {ul : ℕ} → (n : ℕ) → (proof : (n < ul) ⊎ (ll < n)) → InRange ll ul

checkInRange : (ll ul n : ℕ) → Dec ((n < ul) ⊎ (ll < n))
checkInRange ll ul n with n <? ul
...                | yes p = yes (inj₁ p)
...                | no ¬p  with ll <? n
...                            | yes q = yes (inj₂ q)
...                            | no ¬q = no lem
  where
  lem : (proof : n < ul ⊎ ll < n) → ⊥
  lem (inj₁ n<ul) = ¬p n<ul
  lem (inj₂ ll<n) = ¬q ll<n


construct-ir : {ll ul : ℕ} (n : ℕ) → {proof : True (checkInRange ll ul n)} → InRange ll ul
construct-ir n {proof} = gn n (toWitness proof)


_ : InRange 1 5
_ = construct-ir 4
-}

{-
data InRange : ℕ → ℕ → ℕ → Set where
  gn : {ll : ℕ} {ul : ℕ} → {n : ℕ} → (proof : (n < ul) ⊎ (ll < n)) → InRange ll ul n

checkInRange : (ll ul n : ℕ) → Dec ((n < ul) ⊎ (ll < n))
checkInRange ll ul n with n <? ul
...                | yes p = yes (inj₁ p)
...                | no ¬p  with ll <? n
...                            | yes q = yes (inj₂ q)
...                            | no ¬q = no lem
  where
  lem : (proof : n < ul ⊎ ll < n) → ⊥
  lem (inj₁ n<ul) = ¬p n<ul
  lem (inj₂ ll<n) = ¬q ll<n


construct-ir : {ll ul n : ℕ} → {proof : True (checkInRange ll ul n)} → InRange ll ul n
construct-ir {ll} {ul} {n} {proof} = gn (toWitness proof)


_ : InRange 1 5 4
_ = construct-ir
-}

{-
data InRange : {l u : ℕ} → [ l ▹ u ] → ℕ → Set where
   gn : {l u : ℕ} → {i : [ l ▹ u ]} → {n : ℕ} → (proof : (n < u) ⊎ (l < n)) → InRange i n

checkInRange : {l u : ℕ} → [ l ▹ u ] → (n : ℕ) → Dec ((n < u) ⊎ (l < n))
checkInRange {l} {u} i n with n <? u
...                | yes p = yes (inj₁ p)
...                | no ¬p  with l <? n
...                            | yes q = yes (inj₂ q)
...                            | no ¬q = no lem
  where
  lem : (proof : n < u ⊎ l < n) → ⊥
  lem (inj₁ n<u) = ¬p n<u
  lem (inj₂ l<n) = ¬q l<n


construct-ir : {l u : ℕ} → {i : [ l ▹ u ]} → {n : ℕ} → {proof : True (checkInRange i n)} → InRange i n
construct-ir {l} {u} {i} {n} {proof} = gn (toWitness proof)


range : [ 1 ▹ 5 ]
range = interval

proof : (4 < 5) ⊎ (1 < 4)
proof = inj₂ (s≤s (s≤s z≤n))

_ : InRange range 4
_ = construct-ir
-}

{-
checkInRange : {l u : ℕ} → [ l ▹ u ] → (n : ℕ) → Dec ((n < l + u) × (n > l))
checkInRange {l} {u} i n with n <? l + u
...                | no ¬p = no (λ z → ¬p (proj₁ z))
...                | yes p with n >? l
...                           | yes q = yes (p , q)
...                           | no ¬q = no (λ z → ¬q (proj₂ z))

data InRange : {l u : ℕ} → [ l ▹ u ] → ℕ → Set where
  gn : {l u : ℕ} → {i : [ l ▹ u ]} → {n : ℕ} → {dec-proof : True (checkInRange i n)} → InRange i n

range : [ 1 ▹ 5 ]
range = interval

proof : (4 < 5) ⊎ (1 < 4)
proof = inj₂ (s≤s (s≤s z≤n))

_ : InRange range 4
_ = gn


--_ : (InRange range 6) ≡ ⊥
--_ = refl
-}

module _ where
  checkInRange : {l u : ℕ} → [ l ▹ u ] → (n : ℕ) → Dec ((n < l + u) × (n > l))
  checkInRange {l} {u} i n with n <? l + u
  ...                | no ¬p = no (λ z → ¬p (proj₁ z))
  ...                | yes p with n >? l
  ...                           | yes q = yes (p , q)
  ...                           | no ¬q = no (λ z → ¬q (proj₂ z))


data _∈_ : {l u : ℕ} → (n : ℕ) → [ l ▹ u ] → {proof : (n < l + u) × (n > l)} → Set where
  gn : {l u : ℕ} → {n : ℕ}→ {i : [ l ▹ u ]}  → {dec-proof : True (checkInRange i n)} → _∈_ n i {toWitness dec-proof}


r₀ : [ 1 ▹ 5 ]
r₀ = interval

_ : 4 ∈ r₀
_ = gn

--_ : InRange r₀ 10
--_ = gn
