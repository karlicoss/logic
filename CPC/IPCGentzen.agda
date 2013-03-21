open import Prelude

module IPCGentzen (V : Set) where

infix 50 _⊃_

data IPC : Set where
  ⋆_ : V → IPC
  _⊃_ : IPC → IPC → IPC
  ¬_ : IPC → IPC

data _g⊢_ : List IPC → IPC → Set where
  G-AΓ : ∀ {Γ A} → A ∈ Γ → Γ g⊢ A
  G-AL : ∀ {Γ A B} → A ∷ Γ g⊢ B → Γ g⊢ A ⊃ B
  G-AR : ∀ {Γ A B C} → Γ g⊢ A → B ∷ Γ g⊢ C → (A ⊃ B) ∷ Γ g⊢ C

data _gc⊢_ : List IPC → IPC → Set where
  GC-AΓ : ∀ {Γ A} → A ∈ Γ → Γ gc⊢ A
  GC-AL : ∀ {Γ A B} → A ∷ Γ gc⊢ B → Γ gc⊢ A ⊃ B
  GC-AR : ∀ {Γ A B C} → Γ gc⊢ A → B ∷ Γ gc⊢ C → (A ⊃ B) ∷ Γ gc⊢ C
  GC-C : ∀ {Γ A B} → Γ gc⊢ A → A ∷ Γ gc⊢ B → Γ gc⊢ B

g→gc : ∀ {Γ A} → Γ g⊢ A → Γ gc⊢ A
g→gc (G-AΓ x) = GC-AΓ x
g→gc (G-AL p) = GC-AL (g→gc p)
g→gc (G-AR p p₁) = GC-AR (g→gc p) (g→gc p₁)


-- cut elimination
gc→g : ∀ {Γ A} → Γ gc⊢ A → Γ g⊢ A
gc→g (GC-AΓ x) = G-AΓ x
gc→g (GC-AL p) = G-AL (gc→g p)
gc→g (GC-AR p p₁) = G-AR (gc→g p) (gc→g p₁)
gc→g {Γ} {A} (GC-C x y) = {!!}
