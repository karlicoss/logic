open import Prelude

module CPCHilbert (N : ℕ) where

open import CPCCommon N

data _hl⊢_ (Γ : List CPC) : List CPC → Set where
  H-EM : Γ hl⊢ []
  H-AΓ : ∀ {A pl} → A ∈ Γ → Γ hl⊢ pl → Γ hl⊢ (A ∷ pl)             -- assumption
  H-AK : ∀ {A B pl} → Γ hl⊢ pl     → Γ hl⊢ AK {A = A} {B = B} ∷ pl
  H-AS : ∀ {A B C pl} → Γ hl⊢ pl   → Γ hl⊢ AS {A = A} {B = B} {C = C} ∷ pl -- S
  H-AN : ∀ {A B pl} → Γ hl⊢ pl     → Γ hl⊢ AN {A = A} {B = B} ∷ pl -- N
  H-IM : ∀ {A B pl} → (A ⊃ B) ∈ pl → A ∈ pl → Γ hl⊢ pl → Γ hl⊢ (B ∷ pl) -- modus ponens

  
_h⊢_ : (Γ : List CPC) → CPC → Set
Γ h⊢ A = Σ (List CPC) (λ pl → Γ hl⊢ (A ∷ pl))

lemma-proof-drop : ∀ {Γ a la} → Γ hl⊢ a ∷ la → Γ hl⊢ la
lemma-proof-drop {Γ} {a} {[]} pa = H-EM
lemma-proof-drop {Γ} {a} {a₁ ∷ la} (H-AΓ x pa) = pa
lemma-proof-drop {Γ} {(A ⊃ (B ⊃ .A))} {a₁ ∷ la} (H-AK pa) = pa
lemma-proof-drop {Γ} {((A ⊃ (B ⊃ C)) ⊃ .((A ⊃ B) ⊃ (A ⊃ C)))} {a₁ ∷ la} (H-AS pa) = pa
lemma-proof-drop {Γ} {((¬ A ⊃ ¬ B) ⊃ .((¬ A ⊃ B) ⊃ A))} {a₁ ∷ la} (H-AN pa) = pa
lemma-proof-drop {Γ} {a} {a₁ ∷ la} (H-IM x x₁ pa) = pa

lemma-proof-concat : ∀ {Γ la lb} → Γ hl⊢ la → Γ hl⊢ lb → Γ hl⊢ (la ++ lb)
lemma-proof-concat H-EM pb = pb
lemma-proof-concat (H-AΓ x pa) pb = H-AΓ x (lemma-proof-concat pa pb)
lemma-proof-concat (H-AK pa) pb = H-AK (lemma-proof-concat pa pb)
lemma-proof-concat (H-AS pa) pb = H-AS (lemma-proof-concat pa pb)
lemma-proof-concat (H-AN pa) pb = H-AN (lemma-proof-concat pa pb)
lemma-proof-concat (H-IM x x₁ pa) pb = H-IM (relax-right x) (relax-right x₁) (lemma-proof-concat pa pb)

lemma-proof-trash : ∀ {Γ a b la} → Γ hl⊢ a ∷ la → Γ hl⊢ b ∷ la → Γ hl⊢ a ∷ b ∷ la
lemma-proof-trash (H-AΓ x pa) pb = H-AΓ x pb
lemma-proof-trash (H-AK pa) pb = H-AK pb
lemma-proof-trash (H-AS pa) pb = H-AS pb
lemma-proof-trash (H-AN pa) pb = H-AN pb
lemma-proof-trash (H-IM x x₁ pa) pb = H-IM (S x) (S x₁) pb

lemma-wasproven : ∀ {Γ la a} → a ∈ la → Γ hl⊢ la → Γ hl⊢ a ∷ la
lemma-wasproven Z (H-AΓ x p) = H-AΓ x (H-AΓ x p)
lemma-wasproven Z (H-AK p) = H-AK (H-AK p)
lemma-wasproven Z (H-AS p) = H-AS (H-AS p)
lemma-wasproven Z (H-AN p) = H-AN (H-AN p)
lemma-wasproven Z (H-IM x x₁ p) = H-IM (S x) (S x₁) (H-IM x x₁ p)
lemma-wasproven {Γ} {b ∷ bs} {a} (S pin) p = lemma-proof-trash {Γ} {a} {b} {bs} (lemma-wasproven pin (lemma-proof-drop p)) p

H-AI : ∀ {Γ A} → Γ h⊢ (A ⊃ A)
H-AI {Γ} {A = A} = let l0 = H-EM {Γ = Γ}
                       l1 = H-AK {A = A} {B = A ⊃ A} l0
                       l2 = H-AK {A = A} {B = A} l1
                       l3 = H-AS {A = A} {B = A ⊃ A} {C = A} l2
                       l4 = H-IM Z (S (S Z)) l3
                       l5 = H-IM Z (S (S Z)) l4
                   in ((A ⊃ (A ⊃ A)) ⊃ (A ⊃ A)) ∷
                        ((A ⊃ ((A ⊃ A) ⊃ A)) ⊃ ((A ⊃ (A ⊃ A)) ⊃ (A ⊃ A))) ∷
                        (A ⊃ (A ⊃ A)) ∷ (A ⊃ ((A ⊃ A) ⊃ A)) ∷ [] , l5                        
                        
lemma-weakening : ∀ {Γ la B} → Γ hl⊢ la → (B ∷ Γ) hl⊢ la
lemma-weakening {Γ} {[]} p = H-EM
lemma-weakening {Γ} {a ∷ la} (H-AΓ x p) = H-AΓ (S x) (lemma-weakening p)
lemma-weakening {Γ} {(A ⊃ (B₁ ⊃ .A)) ∷ la} (H-AK p) = H-AK (lemma-weakening p)
lemma-weakening {Γ} {((A ⊃ (B₁ ⊃ C)) ⊃ .((A ⊃ B₁) ⊃ (A ⊃ C))) ∷ la} (H-AS p) = H-AS (lemma-weakening p)
lemma-weakening {Γ} {((¬ A ⊃ ¬ B₁) ⊃ .((¬ A ⊃ B₁) ⊃ A)) ∷ la} (H-AN p) = H-AN (lemma-weakening p)
lemma-weakening {Γ} {a ∷ la} (H-IM x x₁ p) = H-IM x x₁ (lemma-weakening p)

lemma-weakening' : ∀ {Γ A B} → Γ h⊢ A → (B ∷ Γ) h⊢ A
lemma-weakening' (fst , snd) = fst , lemma-weakening snd

lemma-contraction : ∀ {Γ la A} → A ∈ Γ → A ∷ Γ hl⊢ la → Γ hl⊢ la
lemma-contraction {Γ} {[]} pin p = H-EM
lemma-contraction {Γ} {.A ∷ la} {A} pin (H-AΓ Z p) = H-AΓ pin (lemma-contraction pin p)
lemma-contraction {Γ} {a ∷ la} pin (H-AΓ (S x) p) = H-AΓ x (lemma-contraction pin p)
lemma-contraction {Γ} {(A₁ ⊃ (B ⊃ .A₁)) ∷ la} pin (H-AK p) = H-AK (lemma-contraction pin p)
lemma-contraction {Γ} {((A₁ ⊃ (B ⊃ C)) ⊃ .((A₁ ⊃ B) ⊃ (A₁ ⊃ C))) ∷ la} pin (H-AS p) = H-AS (lemma-contraction pin p)
lemma-contraction {Γ} {((¬ A₁ ⊃ ¬ B) ⊃ .((¬ A₁ ⊃ B) ⊃ A₁)) ∷ la} pin (H-AN p) = H-AN (lemma-contraction pin p)
lemma-contraction {Γ} {a ∷ la} pin (H-IM x x₁ p) = H-IM x x₁ (lemma-contraction pin p)

lemma-inproof : ∀ {Γ la a} → a ∈ la → Γ hl⊢ la → Γ h⊢ a
lemma-inproof {Γ} {[]} () p
lemma-inproof {Γ} {a ∷ la} Z p = la , p
lemma-inproof {Γ} {a ∷ la} (S pin) (H-AΓ x p) = lemma-inproof pin p
lemma-inproof {Γ} {(A ⊃ (B ⊃ .A)) ∷ la} (S pin) (H-AK p) = lemma-inproof pin p
lemma-inproof {Γ} {((A ⊃ (B ⊃ C)) ⊃ .((A ⊃ B) ⊃ (A ⊃ C))) ∷ la} (S pin) (H-AS p) = lemma-inproof pin p
lemma-inproof {Γ} {((¬ A ⊃ ¬ B) ⊃ .((¬ A ⊃ B) ⊃ A)) ∷ la} (S pin) (H-AN p) = lemma-inproof pin p
lemma-inproof {Γ} {a ∷ la} (S pin) (H-IM x x₁ p) = lemma-inproof pin p

theorem-deduction-hl-revaux : ∀ {Γ la A B} → Γ hl⊢ (A ⊃ B) ∷ la → (A ∷ Γ) hl⊢ B ∷ A ∷ (A ⊃ B) ∷ la
theorem-deduction-hl-revaux {Γ} {la} {A} {B} p = let pp = lemma-weakening {Γ} {(A ⊃ B) ∷ la} {A} p
                                                     pp' = H-AΓ {pl = (A ⊃ B) ∷ la} Z pp
                                                 in H-IM (S Z) Z pp'

                                                  
theorem-deduction-hl-rev : ∀ {Γ A B} → Γ h⊢ (A ⊃ B) → (A ∷ Γ) h⊢ B
theorem-deduction-hl-rev {Γ} {A} {B} (fst , snd) = let x = theorem-deduction-hl-revaux snd
                                                   in A ∷ (A ⊃ B) ∷ fst , x

h2 : ∀ {l1 l2 l3 a A b} →  b ∈ (a ∷ l1) → (b ∈ l1 → (A ⊃ b) ∈ l2) → (A ⊃ b) ∈ (A ⊃ a) ∷ (l3 ++ l2)
h2 Z p = Z
h2 {l1} {l2} {l3} {a} {A} {b} (S pin) p = relax-left ((A ⊃ a) ∷ l3) (p pin)

theorem-deduction-hlaux : ∀ {Γ A al} → A ∷ Γ hl⊢ al → Σ (List CPC) (λ ll → ((Γ hl⊢ ll) × ((a : CPC) → a ∈ al → (A ⊃ a) ∈ ll)))
theorem-deduction-hlaux {Γ} {A} {[]} H-EM = [] , < H-EM , (λ x → λ ()) >
theorem-deduction-hlaux {Γ} {A} {.A ∷ al} (H-AΓ Z p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {.A ∷ al} (H-AΓ Z p) | fst , < x , y > with H-AI {Γ} {A}
theorem-deduction-hlaux {Γ} {A} {.A ∷ al} (H-AΓ Z p) | fst₁ , < x , y > | fst , snd =
  (A ⊃ A) ∷ (fst ++ fst₁) , < lemma-proof-concat snd x , (λ q x₁ → h2 {l1 = al} {l2 = fst₁} {l3 = fst} (x₁) (y q)) >
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-AΓ (S t) p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-AΓ (S t) p) | fst , < x , y > =
  let xxx = H-AΓ t x
      yyy = H-AK {A = a} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (a ⊃ (A ⊃ a)) ∷ a ∷ []
      rrr = (A ⊃ a) ∷ qqq
  in (rrr ++ fst) , < H-IM Z (S Z) (H-AK (H-AΓ t x)) , (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)) >
theorem-deduction-hlaux {Γ} {A} {(A₁ ⊃ (B ⊃ .A₁)) ∷ al} (H-AK p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {(A₁ ⊃ (B ⊃ .A₁)) ∷ al} (H-AK p) | fst , < x , y > =
  let qq = A₁ ⊃ (B ⊃ A₁)
      xxx = H-AK {A = A₁} {B = B} x
      yyy = H-AK {A = qq} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (qq ⊃ (A ⊃ qq)) ∷ qq ∷ []
      rrr = (A ⊃ qq) ∷ qqq
  in (rrr ++ fst) , < H-IM Z (S Z) (H-AK (H-AK x)) , (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)) >
theorem-deduction-hlaux {Γ} {A} {((A₁ ⊃ (B ⊃ C)) ⊃ .((A₁ ⊃ B) ⊃ (A₁ ⊃ C))) ∷ al} (H-AS p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {((A₁ ⊃ (B ⊃ C)) ⊃ .((A₁ ⊃ B) ⊃ (A₁ ⊃ C))) ∷ al} (H-AS p) | fst , < x , y > =
  let qq = (A₁ ⊃ (B ⊃ C)) ⊃ ((A₁ ⊃ B) ⊃ (A₁ ⊃ C))
      xxx = H-AS {A = A₁} {B = B} {C = C} x
      yyy = H-AK {A = qq} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (qq ⊃ (A ⊃ qq)) ∷ qq ∷ []
      rrr = (A ⊃ qq) ∷ qqq
  in (rrr ++ fst) , < (H-IM Z (S Z) (H-AK (H-AS x))) , (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)) >
theorem-deduction-hlaux {Γ} {A} {((¬ A₁ ⊃ ¬ B) ⊃ .((¬ A₁ ⊃ B) ⊃ A₁)) ∷ al} (H-AN p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {((¬ A₁ ⊃ ¬ B) ⊃ .((¬ A₁ ⊃ B) ⊃ A₁)) ∷ al} (H-AN p) | fst , < x , y > =
  let qq = (¬ A₁ ⊃ ¬ B) ⊃ ((¬ A₁ ⊃ B) ⊃ A₁)
      xxx = H-AN {A = A₁} {B = B} x
      yyy = H-AK {A = qq} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (qq ⊃ (A ⊃ qq)) ∷ qq ∷ []
      rrr = (A ⊃ qq) ∷ qqq
  in (rrr ++ fst) , < H-IM Z (S Z) (H-AK (H-AN x)) , (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)) >
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-IM x x₁ p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-IM {A = B} {B = .a} x₂ x₃ p) | fst , < x , y > =
  let AB∈ = y B x₃
      AB→a∈ = y (B ⊃ a) x₂
      xxx = H-AS {A = A} {B = B} {C = a} x
      yyy = H-IM {A = A ⊃ (B ⊃ a)} {B = (A ⊃ B) ⊃ (A ⊃ a)} Z (S AB→a∈) xxx
      zzz = H-IM {A = A ⊃ B} {B = A ⊃ a} Z (S (S AB∈)) yyy
      qqq = ((A ⊃ B) ⊃ (A ⊃ a)) ∷ ((A ⊃ (B ⊃ a)) ⊃ ((A ⊃ B) ⊃ (A ⊃ a))) ∷ []
      rrr = (A ⊃ a) ∷ qqq
  in (rrr ++ fst) , < H-IM Z (S (S (y B x₃))) (H-IM Z (S (y (B ⊃ a) x₂)) (H-AS x)) , (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)) >

theorem-deduction-hl : ∀ {Γ A B} → A ∷ Γ h⊢ B → Γ h⊢ (A ⊃ B)
theorem-deduction-hl (fst , snd) with theorem-deduction-hlaux snd
theorem-deduction-hl {Γ} {A} {B} (fst , snd) | fst₁ , < x , y > = lemma-inproof (y B Z) x
