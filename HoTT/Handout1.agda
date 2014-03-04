module Handout1 where

-- open import Data.Empty
-- open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product

module HA (V : Set) where
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
  
  ¬_ : Pro → Pro  
  ¬ A = A ⊃ ⊥  
  
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
  
  ∧-covar-right : ∀ {A B C} → A ≤ B → A ∧ C ≤ B ∧ C
  ∧-covar-right {A} {B} {C} p = ∧glb (trans≤ ∧L p) ∧R
  
  ∧-covar-left : ∀ {A B C} → A ≤ B → C ∧ A ≤ C ∧ B
  ∧-covar-left p = trans≤ ∧-comm (trans≤ (∧-covar-right p) ∧-comm)
  
  ⊃-right-to-left : ∀ {A B C} → A ≤ B ⊃ C → B ∧ A ≤ C
  ⊃-right-to-left {A} {B} {C} p = trans≤ {B = B ∧ (B ⊃ C)} (∧-covar-left p) ⊃I
  
  distr : ∀ {A B C : Pro} → A ∧ (B ∨ C) ≤ (A ∧ B) ∨ (A ∧ C)
  distr {A} {B} {C} = yonedabwd (λ D x → ⊃-right-to-left (∨lub (⊃exp (trans≤ ∨L x)) (⊃exp (trans≤ ∨R x))))
  
  ¬-largest-inconsistent : ∀ {A B} → A ∧ B ≤ ⊥ → B ≤ ¬ A
  ¬-largest-inconsistent {A} {B} p = ⊃exp p

module BA (V : Set) where
  infix 50 _⊃_
  infix 60 _∨_
  infix 70 _∧_
  data BPro : Set where
    ⊥ : BPro
    ⊤ : BPro
    ⋆_ : V → BPro
    _∧_ : BPro → BPro → BPro
    _∨_ : BPro → BPro → BPro
    co_ : BPro → BPro
    -- _⊃_ : BPro → BPro → BPro
  
  _⊃_ : BPro → BPro → BPro
  A ⊃ B = co A ∨ B

  ¬_ : BPro → BPro  
  ¬ A = A ⊃ ⊥  
  
  data _≤_ : BPro → BPro → Set where
    refl≤ : ∀ {A} → A ≤ A
    trans≤ : ∀ {A B C} → A ≤ B → B ≤ C → A ≤ C
    ∧L : ∀ {A B} → A ∧ B ≤ A
    ∧R : ∀ {A B} → A ∧ B ≤ B
    ∨L : ∀ {A B} → A ≤ A ∨ B
    ∨R : ∀ {A B} → B ≤ A ∨ B
    ⊤I : ∀ {A} → A ≤ ⊤
    ⊥I : ∀ {A} → ⊥ ≤ A
    -- ⊃I : ∀ {A B} → A ∧ (A ⊃ B) ≤ B
  
  postulate distr : ∀ {A B C} → A ∧ (B ∨ C) ≤ (A ∧ B) ∨ (A ∧ C)
  postulate ∧glb : ∀ {A B C} → C ≤ A → C ≤ B → C ≤ A ∧ B
  postulate ∨lub : ∀ {A B C} → A ≤ C → B ≤ C → A ∨ B ≤ C
  postulate co⊤ : ∀ {A} → ⊤ ≤ co A ∨ A
  postulate co⊥ : ∀ {A} → co A ∧ A ≤ ⊥

  yonedabwd : ∀ {A B} → ((C : BPro) → B ≤ C → A ≤ C) → (A ≤ B) 
  yonedabwd {A} {B} = λ z → z B refl≤
  
  ∧-comm : ∀ {A B : BPro} → A ∧ B ≤ B ∧ A
  ∧-comm {A} {B} = ∧glb ∧R ∧L
  
  ∨-comm : ∀ {A B : BPro} → A ∨ B ≤ B ∨ A
  ∨-comm {A} {B} = ∨lub ∨R ∨L
  
  ∧-covar-right : ∀ {A B C} → A ≤ B → A ∧ C ≤ B ∧ C
  ∧-covar-right {A} {B} {C} p = ∧glb (trans≤ ∧L p) ∧R
  
  ∧-covar-left : ∀ {A B C} → A ≤ B → C ∧ A ≤ C ∧ B
  ∧-covar-left p = trans≤ ∧-comm (trans≤ (∧-covar-right p) ∧-comm)
  
  ⊃exp : ∀ {A B C} → A ∧ C ≤ B → C ≤ A ⊃ B
  ⊃exp {A} {B} {C} p = {!!} -- yonedabwd (λ D x → {!!})

