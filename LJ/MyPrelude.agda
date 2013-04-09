open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality

module MyPrelude where

data _∈_ {A : Set} : A → List A → Set where
  Z : {a : A}{as : List A} → a ∈ (a ∷ as)            -- "a" is in a head of a list
  S : {a b : A}{as : List A} → a ∈ as → a ∈ (b ∷ as) -- "a" is in a tail somewhere

-- if x is in as then it is in bs appended to as
relax-right : ∀ {A} {x : A} {as bs} → x ∈ as → x ∈ (as ++ bs)
relax-right Z = Z
relax-right (S y) = S (relax-right y)

-- similarly, but if x is in bs
relax-left : ∀ {A} {x : A} as {bs} → x ∈ bs → x ∈ (as ++ bs)
relax-left [] p = p
relax-left (a ∷ as) p = S (relax-left as p)

lemma-b∧-ololo : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
lemma-b∧-ololo {true} {true} pa pb = refl
lemma-b∧-ololo {true} {false} pa pb = pb
lemma-b∧-ololo {false} {true} pa pb = pa
lemma-b∧-ololo {false} {false} pa pb = pb

lemma-b∧-left : ∀ {a b} → a ∧ b ≡ true → a ≡ true
lemma-b∧-left {true} p = refl
lemma-b∧-left {false} {true} p = p
lemma-b∧-left {false} {false} p = p

lemma-b∧-right : ∀ {a b} → a ∧ b ≡ true → b ≡ true
lemma-b∧-right {a} {true} p = refl
lemma-b∧-right {true} {false} p = p
lemma-b∧-right {false} {false} p = p
