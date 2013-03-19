module CPC where

open import Prelude

N = succ (succ (succ zero))

open import CPCCommon N
open import CPCHilbert N
open import CPCTree N

T-AI₂ : ∀ {Γ A} → Γ t⊢ (A ⊃ A)
T-AI₂ {Γ} {A} = t→h (H-AI {Γ} {A})

theorem-deduction-t₂ : ∀ {Γ A B} → A ∷ Γ t⊢ B → Γ t⊢ (A ⊃ B)
theorem-deduction-t₂ p = t→h (theorem-deduction-hl (h→t p))

theorem-deduction-rev-t₂ : ∀ {Γ A B} → Γ t⊢ (A ⊃ B) → A ∷ Γ t⊢ B
theorem-deduction-rev-t₂ p = t→h (theorem-deduction-hl-rev (h→t p))
