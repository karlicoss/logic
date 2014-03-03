module Handout1 where

-- open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product

postulate V : Set

infix 50 _⊃_
infix 60 _∨_
infix 70 _∧_
data Pro : Set where
  ⊥ : Pro
  ⊤ : Pro
  ⋆_ : V → Pro
  _∧_ : Pro → Pro → Pro
  _∨_ : Pro → Pro → Pro
  _⊃_ : Pro → Pro → Pro
  
data _≤_ : Pro → Pro → Set where
  refl≤ : ∀ {A} → A ≤ A
  trans≤ : ∀ {A B C} → A ≤ B → B ≤ C → A ≤ C
  ∧L : ∀ {A B} → A ∧ B ≤ A
  ∧R : ∀ {A B} → A ∧ B ≤ B
  ∨L : ∀ {A B} → A ≤ A ∨ B
  ∨R : ∀ {A B} → B ≤ A ∨ B
  ⊤I : ∀ {A} → A ≤ ⊤
  ⊥I : ∀ {A} → ⊥ ≤ A
  ⊃I : ∀ {A B} → A ∧ (A ⊃ B) ≤ B

postulate ∧glb : ∀ {A B C} → C ≤ A → C ≤ B → C ≤ A ∧ B
postulate ∨lub : ∀ {A B C} → A ≤ C → B ≤ C → A ∨ B ≤ C
postulate ⊃exp : ∀ {A B C} → A ∧ C ≤ B → C ≤ A ⊃ B

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

-- postulate yoneda : ∀ {A B} → (A ≤ B) ⇔ (∀ (C : Pro) → B ≤ C → A ≤ C)

yonedabwd : ∀ {A B} → ((C : Pro) → B ≤ C → A ≤ C) → (A ≤ B) 
yonedabwd {A} {B} = λ z → z B refl≤

∧-comm : ∀ {A B : Pro} → A ∧ B ≤ B ∧ A
∧-comm {A} {B} = ∧glb ∧R ∧L

∨-comm : ∀ {A B : Pro} → A ∨ B ≤ B ∨ A
∨-comm {A} {B} = ∨lub ∨R ∨L

distr : ∀ {A B C : Pro} → A ∧ (B ∨ C) ≤ (A ∧ B) ∨ (A ∧ C)
distr {A} {B} {C} = {!!}

-- Negative fragment
-- data ⊢_ : Pro → Set where
--   ∧I : {A B : Pro} → ⊢ A → ⊢ B → ⊢ (A ∧ B)
--   ∧E₁ : {A B : Pro} → ⊢ (A ∧ B) → ⊢ A
--   ∧E₂ : {A B : Pro} → ⊢ (A ∧ B) → ⊢ B
--   ⊤I : ⊢ ⊤
