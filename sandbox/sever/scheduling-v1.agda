module scheduling-v1 where

open import Data.Nat
open import Data.Fin using (Fin ; fromℕ)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List ; [] ; _∷_ ; map ; all ; any ; and ; or )
open import Data.Maybe using (Maybe ; nothing ; just)
open import dag-v3

data Resource : Set where
  cpu : Resource
  gpu : Resource


record Runnable : Set where
  constructor r[_,_,_]r
  field
    start : ℕ
    duration : ℕ
    resource : Resource


record Schedule : Set where
  constructor s[_]s
  field
    runnables : List Runnable


validSchedule = s[ r[ 0 , 5 , cpu ]r ∷ r[ 6 , 8 , cpu ]r ∷ r[ 0 , 8 , gpu ]r ∷ [] ]s
invalidSchedule = s[ r[ 0 , 7 , cpu ]r ∷ r[ 6 , 8 , cpu ]r ∷ r[ 0 , 8 , gpu ]r ∷ [] ]s

overlaps : Runnable → Runnable → Bool
overlaps (r[ _ , _ , cpu ]r) (r[ _ , _ , gpu ]r) = false
overlaps (r[ ls , ld , _ ]r) (r[ rs , rd , _ ]r) = ⌊ ls ≥? rs ⌋ ∧  ⌊ ls ≤? rs + rd ⌋ ∨ ⌊ ls + ld ≥? rs ⌋ ∧ ⌊ ls + ld ≤? rs + rd ⌋

_ : overlaps r[ 0 , 7 , cpu ]r r[ 6 , 8 , cpu ]r ≡ true
_ = refl

_ : overlaps r[ 0 , 5 , cpu ]r r[ 6 , 8 , cpu ]r ≡ false
_ = refl

_ : overlaps r[ 0 , 7 , cpu ]r r[ 6 , 8 , gpu ]r ≡ false
_ = refl


--data _<|>_ : Runnable →  Runnable →  Set where
--  resource<|> : { lhs : r[ _ , _ , cpu ]r }  →  { rhs : r[ _ , _ , gpu ]r } →  lhs <|> rhs
