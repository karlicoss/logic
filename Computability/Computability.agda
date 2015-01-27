module Computability where

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data BB : Set where
  Z : BB
  O : BB

infix 50 _∷_
data FinSequence : Set where
  [] : FinSequence
  _∷_ : BB → FinSequence → FinSequence

infix 40 _≤_
data _≤_ : FinSequence → FinSequence → Set where
  ≤-[] : ∀ {x} → [] ≤ x
  ≤-∷ : ∀ {x y a} → x ≤ y → a ∷ x ≤ a ∷ y
  

InfSequence = ℕ → BB


infix 40 _≤i_
data _≤i_ : FinSequence → InfSequence → Set where
  _≤i
