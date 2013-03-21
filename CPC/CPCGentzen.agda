open import Prelude

module CPCGentzen (N : ℕ) where

open import CPCCommon N
open import CPCTree N

data _gl⊢_ : List CPC → List CPC → Set where
  G-AΓ : ∀ {Γ A} → A ∈ Γ → Γ gl⊢ A ∷ []
  G-IL : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A B} → Γ₁ gl⊢ (A ∷ Δ₁) → (B ∷ Γ₂) gl⊢ Δ₂ → (A ⊃ B) ∷ (Γ₁ ++ Γ₂) gl⊢ (Δ₁ ++ Δ₂)
  G-IR : ∀ {Γ Δ A B} → A ∷ Γ gl⊢ B ∷ Δ → Γ gl⊢ A ⊃ B ∷ Δ
  G-NL : ∀ {Γ Δ A} → Γ gl⊢ A ∷ Δ → ¬ A ∷ Γ gl⊢ Δ
  G-NR : ∀ {Γ Δ A} → A ∷ Γ gl⊢ Δ → Γ gl⊢ ¬ A ∷ Δ 

_g⊢_ : List CPC → CPC → Set
Γ g⊢ A = Γ gl⊢ A ∷ []

lemma-aa : ∀ {Γ A} → Γ g⊢ A ⊃ A
lemma-aa {Γ} {A} = G-IR (G-AΓ Z)

lemma-aba : ∀ {Γ A B} → Γ g⊢ A ⊃ (B ⊃ A)
lemma-aba {Γ} {A} {B} = G-IR (G-IR (G-AΓ (S Z)))

lemma-mp : ∀ {Γ A B} → Γ g⊢ A → Γ g⊢ A ⊃ B → Γ g⊢ B
lemma-mp {Γ} {A} {B} a ab = {!!}

lemma-abcabac : ∀ {Γ A B C} → Γ g⊢ (A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))
lemma-abcabac {Γ} {A} {B} {C} = G-IR (G-IR (G-IR {!!}))

-- lemma-a→a : ∀ {Γ A} → Γ g⊢ A ⊃ A
-- lemma-a→a {Γ} {A} = G-AR (G-AΓ Z)

