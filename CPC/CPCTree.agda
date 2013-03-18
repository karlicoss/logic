module CPCTree (V : Set) where

open import Prelude
open import CPCCommon V
open import CPCHilbert V

data _t⊢_ (Γ : List CPC) : CPC → Set where
  T-AΓ : ∀ {A} → A ∈ Γ → Γ t⊢ A
  T-AN : ∀ {A B} → Γ t⊢ AN {A} {B}
  T-AK : ∀ {A B} → Γ t⊢ AK {A} {B}
  T-AS : ∀ {A B C} → Γ t⊢ AS {A} {B} {C}
  T-IM : ∀ {A B} → Γ t⊢ A → Γ t⊢ (A ⊃ B) → Γ t⊢ B

_t⊬_ : List CPC → CPC → Set
hl t⊬ a = (hl t⊢ a) → ⊥

h→t : ∀ {Γ A} → Γ t⊢ A → Γ h⊢ A
h→t (T-AΓ x) = [] , (H-AΓ x H-EM)
h→t T-AN = [] , H-AN H-EM
h→t T-AK = [] , (H-AK H-EM)
h→t T-AS = [] , (H-AS H-EM)
h→t (T-IM {A = A} {B = B} p p₁) = let (la , pa) = h→t p
                                      (lb , pb) = h→t p₁
                                      pab = lemma-proof-concat pa pb
                                      pr = H-IM (relax-left (A ∷ la) {bs = (A ⊃ B) ∷ lb} Z) Z pab
                                  in (A ∷ la ++ (A ⊃ B) ∷ lb) , pr

connect-var : ∀ {Γ la A} → Γ hl⊢ la → A ∈ la → Γ t⊢ A
connect-var (H-AΓ x p) Z = T-AΓ x
connect-var (H-AK p) Z = T-AK
connect-var (H-AS p) Z = T-AS
connect-var (H-AN p) Z = T-AN
connect-var (H-IM x x₁ p) Z = T-IM (connect-var p x₁) (connect-var p x)
connect-var p (S pin) = connect-var (lemma-proof-drop p) pin
                                  
t→h : ∀ {Γ A} → Γ h⊢ A → Γ t⊢ A
t→h (fst , snd) = connect-var snd Z

T-AI : ∀ {Γ A} → Γ t⊢ (A ⊃ A)
T-AI {Γ} {A} = T-IM (T-AK {A = A} {B = A}) (T-IM (T-AK {A = A} {B = A ⊃ A}) (T-AS {A = A} {B = A ⊃ A} {C = A}))

lemma-structural-weakening : ∀ {Γ A B} → Γ t⊢ A → B ∷ Γ t⊢ A
lemma-structural-weakening {Γ} {A} {B} p = t→h (lemma-weakening' (h→t p)) 

lemma-structural-exchange : ∀ {Γ A B C} → A ∷ B ∷ Γ t⊢ C → B ∷ A ∷ Γ t⊢ C
lemma-structural-exchange (T-AΓ Z) = T-AΓ (S Z)
lemma-structural-exchange (T-AΓ (S Z)) = T-AΓ Z
lemma-structural-exchange (T-AΓ (S (S x))) = T-AΓ (S (S x))
lemma-structural-exchange T-AN = T-AN
lemma-structural-exchange T-AK = T-AK
lemma-structural-exchange T-AS = T-AS
lemma-structural-exchange (T-IM p p₁) = T-IM (lemma-structural-exchange p) (lemma-structural-exchange p₁)

theorem-deduction-rev-t : ∀ {Γ A B} → Γ t⊢ (A ⊃ B) → A ∷ Γ t⊢ B
theorem-deduction-rev-t p = T-IM (T-AΓ Z) (lemma-structural-weakening p)

theorem-deduction-t : ∀ {Γ A B} → A ∷ Γ t⊢ B → Γ t⊢ (A ⊃ B)
theorem-deduction-t (T-AΓ Z) = T-AI
theorem-deduction-t (T-AΓ (S x)) = T-IM (T-AΓ x) T-AK
theorem-deduction-t T-AN = T-IM T-AN T-AK
theorem-deduction-t T-AK = T-IM T-AK T-AK
theorem-deduction-t T-AS = T-IM T-AS T-AK
theorem-deduction-t (T-IM p p₁) = T-IM (theorem-deduction-t p) (T-IM (theorem-deduction-t p₁) T-AS)

lemma-¬¬-elim : ∀ {Γ A} → Γ t⊢ (¬ (¬ A) ⊃ A)
lemma-¬¬-elim {Γ} {A} = theorem-deduction-t (T-IM (T-AI {A = ¬ A}) (T-IM (T-IM (T-AΓ Z) T-AK) T-AN))

theorem-soundness₂ : ∀ {Γ A} → ((x : CPC) → x ∈ Γ → c⊨ x) → Γ t⊢ A → c⊨ A
theorem-soundness₂ {Γ} {A} ss (T-AΓ x) sign = ss A x sign
theorem-soundness₂ ss (T-AN {A} {B}) sign = lemma-taut-AN {A} {B} sign
theorem-soundness₂ ss (T-AK {A} {B}) sign = lemma-taut-AK {A} {B} sign
theorem-soundness₂ ss (T-AS {A} {B} {C}) sign = lemma-taut-AS {A} {B} {C} sign
theorem-soundness₂ ss (T-IM {A} {B} p p₁) sign = lemma-taut-IM {A} {B} (theorem-soundness₂ ss p) (theorem-soundness₂ ss p₁) sign

lemma-empty-sound : (x : CPC) → x ∈ [] → c⊨ x
lemma-empty-sound x ()

theorem-soundness : ∀ {A} → [] t⊢ A → c⊨ A
theorem-soundness {A} p = theorem-soundness₂ {Γ = []} {A} lemma-empty-sound p

-- Both A and ¬ A cannot be derived
theorem-consistency : ∀ {A} → [] t⊢ A → [] t⊢ ¬ A → ⊥
theorem-consistency {A} p pn with theorem-soundness p | theorem-soundness pn
... | x | y with x (λ sign → false) | y (λ sign → false)
... | xx | yy with eval (λ sign → false) A
theorem-consistency p pn | x | y | xx | () | true
theorem-consistency p pn | x | y | () | yy | false

  
lemma-proof-replace-equiv : ∀ {Γ A B C} → B ∷ Γ t⊢ C → Γ t⊢ (A ⊃ B) → A ∷ Γ t⊢ C
lemma-proof-replace-equiv (T-AΓ Z) pf = theorem-deduction-rev-t pf
lemma-proof-replace-equiv (T-AΓ (S x)) pf = T-AΓ (S x)
lemma-proof-replace-equiv T-AN pf = T-AN
lemma-proof-replace-equiv T-AK pf = T-AK
lemma-proof-replace-equiv T-AS pf = T-AS
lemma-proof-replace-equiv (T-IM p p₁) pf = T-IM (lemma-proof-replace-equiv p pf) (lemma-proof-replace-equiv p₁ pf)

lemma-proof-donotneed : ∀ {Γ A B} → A ∷ Γ t⊢ B → Γ t⊢ A → Γ t⊢ B
lemma-proof-donotneed (T-AΓ Z) pa = pa
lemma-proof-donotneed (T-AΓ (S x)) pa = T-AΓ x
lemma-proof-donotneed T-AN pa = T-AN
lemma-proof-donotneed T-AK pa = T-AK
lemma-proof-donotneed T-AS pa = T-AS
lemma-proof-donotneed (T-IM pb pb₁) pa = T-IM (lemma-proof-donotneed pb pa) (lemma-proof-donotneed pb₁ pa)

-- lemma-⊃-ololo : ∀ {Γ A B} → Γ t⊢ (¬ (¬ A) ⊃ B) ⊃ (A ⊃ B)
-- lemma-⊃-ololo {Γ} {A} {B} =
--   let Γ₂ = ¬ (¬ A) ⊃ B ∷ A ∷ Γ
--       pnota : Γ₂ t⊢ ¬ (¬ A)
--       pnota = T-IM {Γ = Γ₂} {A = A} (T-AΓ (S Z)) lemma-intro¬¬
--   in theorem-deduction-t (theorem-deduction-t (lemma-structural-exchange (T-IM pnota (T-AΓ Z))))

lemma-⊃-alala : ∀ {Γ A B} → Γ t⊢ (A ⊃ B) ⊃ (¬ (¬ A) ⊃ B)
lemma-⊃-alala {Γ} {A} {B} =
  let Γ₂ = ¬ (¬ A) ∷ A ⊃ B ∷ Γ
      pa : Γ₂ t⊢ A
      pa = T-IM {Γ = Γ₂} {A = ¬ (¬ A)} (T-AΓ Z) lemma-¬¬-elim
  in theorem-deduction-t (theorem-deduction-t (T-IM pa (T-AΓ (S Z))))
  
T-ANn : ∀ {Γ} {A} {B} → Γ t⊢ (A ⊃ B) ⊃ ((A ⊃ ¬ B) ⊃ ¬ A)
T-ANn {Γ} {A} {B} =
  let xx = T-AN {Γ = Γ} {A = ¬ A} {B = B}
      yy = theorem-deduction-rev-t (theorem-deduction-rev-t xx)
      zz = lemma-proof-replace-equiv {A = A ⊃ B} {B = ¬ (¬ A) ⊃ B} {C = ¬ A} yy lemma-⊃-alala
      qq = lemma-structural-exchange zz
      ww = lemma-proof-replace-equiv {A = A ⊃ ¬ B} {B = ¬ (¬ A) ⊃ ¬ B} {C = ¬ A} qq lemma-⊃-alala
  in theorem-deduction-t (theorem-deduction-t ww)

lemma-contradiction : ∀ {Γ A B} → Γ t⊢ A ⊃ B → Γ t⊢ A ⊃ ¬ B → Γ t⊢ ¬ A
lemma-contradiction {Γ} {A} {B} pb pnb = T-IM {A = A ⊃ ¬ B} {B = ¬ A} pnb (T-IM {A = A ⊃ B} {B = (A ⊃ ¬ B) ⊃ ¬ A} pb T-ANn)

-- Ex falso quodlibet or the principle of explosion
-- From contradicion follows anything
lemma-inc⊢any : ∀ {Γ A B} → Γ t⊢ A → Γ t⊢ ¬ A → Γ t⊢ B
lemma-inc⊢any {Γ} {A} {B} p pn =
  let Γ₂ = B ∷ Γ
      ba : Γ t⊢ (¬ B ⊃ A)
      ba = theorem-deduction-t {Γ = Γ} (lemma-structural-weakening p)
      bna : Γ t⊢ (¬ B ⊃ ¬ A)
      bna = theorem-deduction-t {Γ = Γ} (lemma-structural-weakening pn)
      nnb = lemma-contradiction ba bna
  in T-IM nnb lemma-¬¬-elim

lemma-¬¬-intro : ∀ {Γ A} → Γ t⊢ (A ⊃ ¬ (¬ A))
lemma-¬¬-intro {Γ} {A} =
  let pa : A ∷ Γ t⊢ ¬ A ⊃ A
      pa = theorem-deduction-t (T-AΓ (S Z))
      pna : A ∷ Γ t⊢ ¬ A ⊃ ¬ A
      pna = theorem-deduction-t (T-AΓ Z)
  in theorem-deduction-t (lemma-contradiction pa pna)


lemma-∨-leftfalse : ∀ {Γ A B} → Γ t⊢ (A ∨ B) → Γ t⊢ ¬ A → Γ t⊢ B
lemma-∨-leftfalse {Γ} {A} {B} p pna = T-IM pna p

lemma-∨-rightfalse : ∀ {Γ A B} → Γ t⊢ (A ∨ B) → Γ t⊢ ¬ B → Γ t⊢ A
lemma-∨-rightfalse {Γ} {A} {B} p pnb = T-IM p (T-IM (T-IM pnb T-AK) T-AN)

lemma-syll : ∀ {Γ A B C} → (A ⊃ B) ∷ (B ⊃ C) ∷ Γ t⊢ (A ⊃ C)
lemma-syll {Γ} {A} {B} {C} =
  let nc = A ∷ (A ⊃ B) ∷ (B ⊃ C) ∷ Γ
  in theorem-deduction-t (T-IM {A = B} {B = C} (T-IM {A = A} {B = B} (T-AΓ Z) (T-AΓ (S Z))) (T-AΓ {Γ = nc} (S (S Z))))

lemma-true-consequent : ∀ {Γ A B} → Γ t⊢ B → Γ t⊢ (A ⊃ B)
lemma-true-consequent {Γ} {A} {B} pb = T-IM pb T-AK

lemma-modus-tollens : ∀ {Γ A B} → (A ⊃ B) ∷ ¬ B ∷ Γ t⊢ ¬ A
lemma-modus-tollens {Γ} {A} {B} =
  let Γ₂ = (A ⊃ B) ∷ ¬ B ∷ Γ
  in lemma-∨-rightfalse {A = ¬ A} {B = B} (theorem-deduction-t (lemma-proof-replace-equiv {Γ = Γ₂} {A = ¬ (¬ A)} {B = A} {C = B} (T-IM (T-AΓ Z) (T-AΓ (S Z))) lemma-¬¬-elim)) (T-AΓ (S Z)) 

lemma-⊃-transpose : ∀ {Γ A B} → Γ t⊢ (A ⊃ B) ⊃ (¬ B ⊃ ¬ A)
lemma-⊃-transpose {Γ} {A} {B} = theorem-deduction-t (theorem-deduction-t (lemma-structural-exchange lemma-modus-tollens))

lemma-false-antecedent : ∀ {Γ A B} → Γ t⊢ ¬ A ⊃ (A ⊃ B)
lemma-false-antecedent {Γ} {A} {B} =
  let Γ₂ = A ∷ ¬ A ∷ Γ
      pa : Γ₂ t⊢ A
      pa = T-AΓ Z
      pna : Γ₂ t⊢ ¬ A
      pna = T-AΓ (S Z)
  in theorem-deduction-t (theorem-deduction-t (lemma-inc⊢any pa (T-AΓ (S Z))))

lemma-true-antecedent : ∀ {Γ A B} → Γ t⊢ ¬ (A ⊃ B) ⊃ A
lemma-true-antecedent {Γ} {A} {B} =
  let xx = lemma-⊃-transpose {Γ = Γ} {A = ¬ A} {B = A ⊃ B}
      yy = T-IM lemma-false-antecedent xx
      zz = theorem-deduction-rev-t yy
  in theorem-deduction-t (T-IM zz lemma-¬¬-elim)

lemma-∧-elim-left : ∀ {Γ A B} → Γ t⊢ (A ∧ B) ⊃ A
lemma-∧-elim-left {Γ} {A} {B} = lemma-true-antecedent -- theorem-deduction-t (lemma-true-antecedent {A = A} {B = ¬ B})

lemma-∧-elim-right : ∀ {Γ A B} → Γ t⊢ (A ∧ B) ⊃ B
lemma-∧-elim-right {Γ} {A} {B} =
  let xx = lemma-⊃-transpose {Γ = Γ} {A = ¬ B} {B = A ⊃ ¬ B}
      yy = T-IM T-AK xx
      zz = theorem-deduction-rev-t yy
  in theorem-deduction-t (T-IM zz lemma-¬¬-elim)

lemma-∧-intro : ∀ {Γ A B} → Γ t⊢ A ⊃ (B ⊃ A ∧ B)
lemma-∧-intro {Γ} {A} {B} =
  let tp = lemma-⊃-transpose {Γ = A ∷ Γ} {A = ¬ (A ⊃ ¬ B)} {B = A}
      Γ₂ = B ∷ A ∷ Γ
      pb : Γ₂ t⊢ (A ⊃ ¬ B) ⊃ B
      pb = theorem-deduction-t (T-AΓ (S Z))
      pnb : Γ₂ t⊢ (A ⊃ ¬ B) ⊃ ¬ B
      pnb = theorem-deduction-t (T-IM (T-AΓ (S (S Z))) (T-AΓ Z))
  in theorem-deduction-t (theorem-deduction-t (lemma-contradiction pb pnb))

lemma-∧-comm : ∀ {Γ A B} → Γ t⊢ (A ∧ B) ⊃ (B ∧ A)
lemma-∧-comm {Γ} {A} {B} =
  let Γ₂ = A ∧ B ∷ Γ
      pa : Γ₂ t⊢ A
      pa = T-IM (T-AΓ Z) lemma-∧-elim-left
      pb : Γ₂ t⊢ B
      pb = T-IM (T-AΓ Z) lemma-∧-elim-right
  in theorem-deduction-t (T-IM pa (T-IM pb lemma-∧-intro))


lemma-∨-intro-left : ∀ {Γ A B} → Γ t⊢ A ⊃ (A ∨ B)
lemma-∨-intro-left {Γ} {A} {B} = theorem-deduction-t (theorem-deduction-t (lemma-inc⊢any (T-AΓ (S Z)) (T-AΓ Z)))

lemma-∨-intro-right : ∀ {Γ} {A} {B} → Γ t⊢ B ⊃ (A ∨ B)
lemma-∨-intro-right {Γ} {A} {B} = theorem-deduction-t (theorem-deduction-t (T-AΓ (S Z)))

lemma-∨-comm : ∀ {Γ A B} → Γ t⊢ (A ∨ B) → Γ t⊢ (B ∨ A)
lemma-∨-comm {Γ} {A} {B} p =
  let pb : ¬ B ∷ Γ t⊢ (¬ A ⊃ B)
      pb = theorem-deduction-t (T-IM (T-AΓ Z) (lemma-structural-weakening (lemma-structural-weakening p)))
      pnb : ¬ B ∷ Γ t⊢ (¬ A ⊃ ¬ B)
      pnb = theorem-deduction-t (T-AΓ (S Z))
      nna = lemma-contradiction pb pnb
  in theorem-deduction-t (T-IM nna lemma-¬¬-elim)

lemma-∨-elim : ∀ {Γ A} → Γ t⊢ (A ∨ A) ⊃ A
lemma-∨-elim {Γ} {A} =
  let Γ₂ = ¬ A ⊃ A ∷ Γ
      xx : Γ₂ t⊢ (¬ A ⊃ A) ⊃ ((¬ A ⊃ ¬ A) ⊃ ¬ (¬ A))
      xx = T-ANn
      yy : Γ₂ t⊢ (¬ A ⊃ ¬ A) ⊃ ¬ (¬ A)
      yy = T-IM (T-AΓ Z) xx
  in theorem-deduction-t (T-IM (T-IM T-AI yy) lemma-¬¬-elim)
  
lemma-excluded-middle : ∀ {Γ A} → Γ t⊢ A ∨ ¬ A
lemma-excluded-middle {Γ} {A} = T-AI
{-
lemma-[]⊬a : {a : V} → [] t⊬ (⋆ a)
lemma-[]⊬a (T-AΓ ())
lemma-[]⊬a {a} (T-IM t s) = {!!}
-}

lemma-∨-alala : ∀ {Γ A B} → A ∨ ¬ A ∷ Γ t⊢ B → Γ t⊢ B
lemma-∨-alala {Γ} {A} {B} p = lemma-proof-donotneed p T-AI

lemma-∨-ololo : ∀ {Γ A B C} → Γ t⊢ A ⊃ B → Γ t⊢ ¬ A ⊃ C → Γ t⊢ B ∨ C
lemma-∨-ololo {Γ} {A} {B} {C} pb pc with theorem-deduction-rev-t pb | theorem-deduction-rev-t pc
... | xx | yy = {!!}

lemma-∨-azaza : ∀ {Γ A B C} → A ∷ Γ t⊢ C → B ∷ Γ t⊢ C → A ∨ B ∷ Γ t⊢ C
lemma-∨-azaza {Γ} {A} {B} {C} pa pb = {!!}

lemma-proof-drop-redundant : ∀ {Γ A B} → A ∷ Γ t⊢ B → ¬ A ∷ Γ t⊢ B → Γ t⊢ B
lemma-proof-drop-redundant {Γ} {A} {B} pa pna =
  let xa : Γ t⊢ A ⊃ B
      xa = theorem-deduction-t pa
      xb : Γ t⊢ ¬ A ⊃ B
      xb = theorem-deduction-t pna
      b∨b : Γ t⊢ B ∨ B
      b∨b = lemma-∨-ololo {Γ} {A} {B} {B} xa xb 
  in T-IM b∨b lemma-∨-elim

-- is it true at all?
lemma-invalid⊨-any : ∀ {A B} → c⊮ A → A ∷ [] t⊢ B
lemma-invalid⊨-any {A} {B} inv = {!!}

-- lemma-composition : ∀ 

lemma-invalid-var : ∀ {v} → c⊮ ⋆ v
lemma-invalid-var {v} ev with ev (λ v → false)
lemma-invalid-var ev | ()

-- what do I want to prove here?
lemma-completeness-¬ : ∀ {A} → (V → Bool) → [] t⊢ ¬ A
lemma-completeness-¬ {A} ev with eval ev A
lemma-completeness-¬ {A} ev | true = {!!}
lemma-completeness-¬ {A} ev | false = {!!}

theorem-completeness : ∀ {A} → c⊨ A → [] t⊢ A
theorem-completeness {⋆ x} taut with lemma-invalid-var taut
theorem-completeness {⋆ x} taut | ()
theorem-completeness {A ⊃ B} taut = {!!}
theorem-completeness {¬ A} taut = {!!}
