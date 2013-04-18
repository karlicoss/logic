open import TSet

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum

module LK (V : Set) (cmpv : (a b : V) → Dec (a ≡ b)) where

infix 50 _l⊃_
data CPC : Set where
  ⋆_ : V → CPC
  _l⊃_ : CPC → CPC → CPC
  l¬_ : CPC → CPC

postulate cpccmp : (a b : CPC) → Dec (a ≡ b)

open TSetOps CPC cpccmp 

data _⊢_ : TSet CPC → TSet CPC → Set where
  LK-I : ∀ {A} → e A ⊢ e A
  LK-C : ∀ {Γ Δ Σ Π A} → Γ ⊢ Δ ∷ (e A) → (e A) ∷ Σ ⊢ Π → Γ ∷ Σ ⊢ Δ ∷ Π
  LK-L⊃ : ∀ {Γ Δ Σ Π A B} → Γ ⊢ (e A) ∷ Δ → Σ ∷ (e B) ⊢ Π → Γ ∷ Σ ∷ (e (A l⊃ B)) ⊢ Δ ∷ Π
  LK-R⊃ : ∀ {Γ Δ A B} → Γ ∷ (e A) ⊢ (e B) ∷ Δ → Γ ⊢ (e (A l⊃ B)) ∷ Δ
  LK-L¬ : ∀ {Γ Δ A} → Γ ⊢ (e A) ∷ Δ → Γ ∷ (e (l¬ A)) ⊢ Δ
  LK-R¬ : ∀ {Γ Δ A} → Γ ∷ (e A) ⊢ Δ → Γ ⊢ (e (l¬ A)) ∷ Δ
  LK-PL : ∀ {Γ Δ Π} → Γ ⊢ Π → Γ ♯ Δ → Δ ⊢ Π
  LK-PR : ∀ {Γ Δ Π} → Γ ⊢ Π → Π ♯ Δ → Γ ⊢ Δ
  LK-WL : ∀ {Γ Δ A} → Γ ⊢ Δ → Γ ∷ (e A) ⊢ Δ
  LK-WR : ∀ {Γ Δ A} → Γ ⊢ Δ → Γ ⊢ (e A) ∷ Δ
  LK-CL : ∀ {Γ Δ A} → (e A) ∷ (e A) ∷ Γ ⊢ Δ → (e A) ∷ Γ ⊢ Δ
  LK-CR : ∀ {Γ Δ A} → Γ ⊢ (e A) ∷ (e A) ∷ Δ → Γ ⊢ (e A) ∷ Δ

LK-R⊃o : ∀ {Γ A B} → Γ ∷ (e A) ⊢ (e B) → Γ ⊢ e (A l⊃ B)
LK-R⊃o {Γ} {A} {B} p = LK-PR (LK-R⊃ (LK-PR p AZR)) RZR

lem-⊢-mp : ∀ {A B} → ø ⊢ e (A l⊃ ((A l⊃ B) l⊃ B))
lem-⊢-mp {A} {B} = LK-R⊃o (LK-R⊃o (LK-PR (LK-PL (LK-L⊃ (LK-PR LK-I AZR) (LK-PL LK-I AZL)) (SWL ♯∙ RTL)) RZL))

lem-⊢-weaken-right : ∀ {Γ Δ Σ} → Γ ⊢ Δ → Γ ⊢ Σ ∷ Δ
lem-⊢-weaken-right {Γ} {Δ} {ø} p = LK-PR p AZL
lem-⊢-weaken-right {Γ} {Δ} {e a} p = LK-WR p
lem-⊢-weaken-right {Γ} {Δ} {Σ ∷ Σ₁} p = LK-PR (lem-⊢-weaken-right (lem-⊢-weaken-right p)) RTL

lem-⊢-weaken-left : ∀ {Γ Δ Σ} → Γ ⊢ Δ → Γ ∷ Σ ⊢ Δ
lem-⊢-weaken-left {Γ} {Δ} {ø} p = LK-PL p AZR
lem-⊢-weaken-left {Γ} {Δ} {e a} p = LK-WL p
lem-⊢-weaken-left {Γ} {Δ} {Σ ∷ Σ₁} p = LK-PL (lem-⊢-weaken-left (lem-⊢-weaken-left p)) RTR

lem-⊢-false : ∀ {A B} → ø ⊢ e (A l⊃ B) l⊃ ((A l⊃ (l¬ B)) l⊃ (l¬ A))
lem-⊢-false {A} {B} = LK-R⊃o (LK-R⊃o (LK-PR (LK-PL (LK-CL (LK-PR (LK-CR (LK-L⊃ (LK-PR (LK-R¬ (LK-PL (LK-WL LK-I) SW)) SW) (LK-CR (LK-PL (LK-CL (LK-L⊃ (LK-PR (LK-R¬ (LK-PL (lem-⊢-weaken-left LK-I) SW)) SW) (LK-PL (LK-L¬ (LK-PR (lem-⊢-weaken-right LK-I) SW)) SW))) SW)))) SW)) (AZL ♯∙ RTL)) RZL))
