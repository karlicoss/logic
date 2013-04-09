open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import TSet

module LJ (V : Set) (cmpv : (a b : V) → Dec (a ≡ b)) where
  infix 50 _⊃_
  data IPC : Set where
    ⋆_ : V → IPC
    _⊃_ : IPC → IPC → IPC
    l¬_ : IPC → IPC

  lemma-ipccmp-¬ : ∀ {x y} → (x ≡ y → ⊥) → l¬ x ≡ l¬ y → ⊥
  lemma-ipccmp-¬ {⋆ x} {⋆ .x} p refl = p refl
  lemma-ipccmp-¬ {⋆ x} {y ⊃ y₁} p ()
  lemma-ipccmp-¬ {⋆ x} {l¬ y} p ()
  lemma-ipccmp-¬ {x ⊃ x₁} {⋆ x₂} p ()
  lemma-ipccmp-¬ {x ⊃ x₁} {.x ⊃ .x₁} p refl = p refl
  lemma-ipccmp-¬ {x ⊃ x₁} {l¬ y} p ()
  lemma-ipccmp-¬ {l¬ x} {⋆ x₁} p ()
  lemma-ipccmp-¬ {l¬ x} {y ⊃ y₁} p ()
  lemma-ipccmp-¬ {l¬ x} {l¬ .x} p refl = p refl 

  lemma-ipccmp-⋆ : ∀ {x y} → (x ≡ y → ⊥) → ⋆ x ≡ ⋆ y → ⊥
  lemma-ipccmp-⋆ p refl = p refl

  lemma-ipccmp-⊃ : ∀ {a ac b bc} → (ac ≡ bc → ⊥) ⊎ (a ≡ b → ⊥) → a ⊃ ac ≡ b ⊃ bc → ⊥
  lemma-ipccmp-⊃ (inj₁ x) refl = x refl
  lemma-ipccmp-⊃ (inj₂ x) refl = x refl
  
  ipccmp : (a b : IPC) → Dec (a ≡ b)
  ipccmp (⋆ x) (⋆ y) with cmpv x y
  ipccmp (⋆ x) (⋆ .x) | yes refl = yes refl
  ipccmp (⋆ x) (⋆ y) | no l¬a = no (λ e → lemma-ipccmp-⋆ l¬a e)
  ipccmp (⋆ x) (b ⊃ b₁) = no (λ ())
  ipccmp (⋆ x) (l¬ b) = no (λ ())
  ipccmp (a ⊃ a₁) (⋆ x) = no (λ ())
  ipccmp (a ⊃ ac) (b ⊃ bc) with ipccmp a b | ipccmp ac bc
  ipccmp (a ⊃ ac) (.a ⊃ .ac) | yes refl | yes refl = yes refl
  ipccmp (a ⊃ ac) (.a ⊃ bc) | yes refl | no l¬a = no (λ x → lemma-ipccmp-⊃ {a} {ac} {a} {bc} (inj₁ l¬a) x)
  ipccmp (a ⊃ ac) (b ⊃ .ac) | no l¬a | yes refl = no (λ x → lemma-ipccmp-⊃ (inj₂ l¬a) x)
  ipccmp (a ⊃ ac) (b ⊃ bc) | no l¬a | no l¬a₁ = no (λ x → lemma-ipccmp-⊃ (inj₁ l¬a₁) x)
  ipccmp (a ⊃ a₁) (l¬ b) = no (λ ())
  ipccmp (l¬ a) (⋆ x) = no (λ ())
  ipccmp (l¬ a) (b ⊃ b₁) = no (λ ())
  ipccmp (l¬ a) (l¬ b) with ipccmp a b
  ipccmp (l¬ a) (l¬ .a) | yes refl = yes refl
  ipccmp (l¬ a) (l¬ b) | no l¬a = no (lemma-ipccmp-¬ l¬a)

  open TSetOps IPC ipccmp public
  
  data RHS : Set where
    ø : RHS
    rhs_ : IPC → RHS
  
  data _s⊢_ : TSet IPC → RHS → Set where
    S-I : ∀ {Γ A} → A f∈ Γ → Γ s⊢ rhs A
    S-¬L : ∀ {Γ A} → Γ s⊢ rhs A → (el (l¬ A)) ∷ Γ s⊢ ø
    S-¬R : ∀ {Γ A} → (el A) ∷ Γ s⊢ ø → Γ s⊢ rhs (l¬ A)
    S-→L : ∀ {Γ A B C} → Γ s⊢ rhs A → (el B) ∷ Γ s⊢ C → (el (A ⊃ B)) ∷ Γ s⊢ C
    S-→R : ∀ {Γ A B} → (el A) ∷ Γ s⊢ rhs B → Γ s⊢ rhs (A ⊃ B)
    S-C : ∀ {Γ Δ A B} → Γ s⊢ rhs A → (el A) ∷ Δ s⊢ rhs B → Γ ∷ Δ s⊢ rhs B
    S-E : ∀ {Γ Δ A} → Γ s♯ Δ → Γ s⊢ A → Δ s⊢ A
    S-R : ∀ {Γ A} → Γ s⊢ ø → Γ s⊢ rhs A
    S-W : ∀ {Γ Δ A} → Γ s⊢ A → Γ ∷ Δ s⊢ A
  
  lemma-a¬a : ∀ {A} → (el A) ∷ (el l¬ A) s⊢ ø
  lemma-a¬a {A} = S-E SW (S-¬L (S-I Z))

  lemma-a⊃b⊃a : ∀ {Γ A B} → Γ s⊢ rhs A ⊃ (B ⊃ A)
  lemma-a⊃b⊃a {Γ} {A} {B} = S-→R (S-→R (S-I (SR (SL Z))))
  
  lemma-a⊃b⊃c⊃a⊃b⊃a⊃c : ∀ {Γ A B C} → Γ s⊢ rhs (A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))
  lemma-a⊃b⊃c⊃a⊃b⊃a⊃c {Γ} {A} {B} {C} =
    let Γ₂ = (el A) ∷ (el A ⊃ B) ∷ (el A ⊃ (B ⊃ C)) ∷ Γ
        Δ = (el A ⊃ (B ⊃ C)) ∷ (el A ⊃ B) ∷ (el A) ∷ Γ
        pexch : Δ s♯ Γ₂
        pexch = SL SWL s∙ SWL s∙ SL SWL
    in S-→R (S-→R (S-→R (S-E pexch (S-→L (S-I (SR (SL Z))) (S-E SWL (S-→L (S-I (SR (SL Z))) (S-E SWL (S-→L (S-I (SL Z)) (S-I (SL Z))))))))))

  lemma-ded : ∀ {Γ A B} → Γ s⊢ rhs (A ⊃ B) → (el A) ∷ Γ s⊢ rhs B
  lemma-ded (S-I Z) = S-E SW (S-→L (S-I Z) (S-I (SL Z)))
  lemma-ded (S-I (SL x)) = S-E RR (S-W (lemma-ded (S-I x)))
  lemma-ded (S-I (SR x)) = S-E (TR SW SWL) (S-W (lemma-ded (S-I x)))
  lemma-ded (S-→L pab pab₁) = S-E SWL (S-→L (S-E SW (S-W pab)) (S-E SWL (lemma-ded pab₁)))
  lemma-ded (S-→R pab) = pab
  lemma-ded (S-C pab pab₁) = S-E SWL (S-C pab (S-E SWL (lemma-ded pab₁)))
  lemma-ded (S-E x pab) = S-E (SL x) (lemma-ded pab)
  lemma-ded (S-R pab) = S-E SW (S-R (S-W pab))
  lemma-ded (S-W pab) = S-E RR (S-W (lemma-ded pab))
   
  lemma-mp : ∀ {Γ A B} → Γ s⊢ rhs A → Γ s⊢ rhs (A ⊃ B) → Γ s⊢ rhs B
  lemma-mp pa pab = S-E CP (S-C pa (lemma-ded pab))
