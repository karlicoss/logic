module CPC where

infixr 40 _∷_
data List (A : Set) : Set where
  [] : List A                            -- an empty list
  _∷_ : (a : A) → (as : List A) → List A -- "cons" -- creates a new list with "a" in the head
                                           -- and "as" in the tail

-- appending two lists
_++_ : ∀ {A} → List A → List A → List A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
  
data _∈_ {A : Set} : A → List A → Set where
  Z : {a : A}{as : List A} → a ∈ (a ∷ as)            -- "a" is in a head of a list
  S : {a b : A}{as : List A} → a ∈ as → a ∈ (b ∷ as) -- "a" is in a tail somewhere

infix 40 _≤l_

data _≤l_ {A : Set} : List A → List A → Set where
  Z≤l : {al : List A} → [] ≤l al
  S≤l : {a b : A} {al bl : List A} → al ≤l bl → (a ∷ al) ≤l (b ∷ bl)

lemma-same : ∀ {A} → (la : List A) → la ≤l la
lemma-same [] = Z≤l
lemma-same (a ∷ la) = S≤l (lemma-same la)

lemma-≤l-append : ∀ {A} {la lb : List A} {a : A} → la ≤l lb → la ≤l a ∷ lb
lemma-≤l-append Z≤l = Z≤l
lemma-≤l-append (S≤l p) = S≤l (lemma-≤l-append p)

-- if x is in as then it is in bs appended to as
relax-right : ∀ {A} {x : A} {as bs} → x ∈ as → x ∈ (as ++ bs)
relax-right Z = Z
relax-right (S y) = S (relax-right y)

-- similarly, but if x is in bs
relax-left : ∀ {A} {x : A} as {bs} → x ∈ bs → x ∈ (as ++ bs)
relax-left [] p = p
relax-left (a ∷ as) p = S (relax-left as p)

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infix 40 _×_

data _×_ (P : Set) (Q : Set) : Set where
  _×i_ : P → Q → P × Q

data V : Set where
  varA varB varC varD varE : V

infix 50 _∨_
infix 60 _⊃_
infix 70 _∧_
  
data CPC : Set where
  ⋆_  : V → CPC               -- variable
  _⊃_ : CPC → CPC → CPC -- implication
  ¬  : CPC → CPC                   -- negation

AK : ∀ {A B} → CPC
AK {A} {B} = A ⊃ (B ⊃ A)

AS : ∀ {A B C} → CPC
AS {A} {B} {C} = (A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))

AN : ∀ {A B} → CPC
AN {A} {B} = (¬ A ⊃ ¬ B) ⊃ ((¬ A ⊃ B) ⊃ A)

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
theorem-deduction-hlaux {Γ} {A} {[]} H-EM = [] , (H-EM ×i (λ x → λ ()))
theorem-deduction-hlaux {Γ} {A} {.A ∷ al} (H-AΓ Z p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {.A ∷ al} (H-AΓ Z p) | fst , (x ×i y) with H-AI {Γ} {A}
theorem-deduction-hlaux {Γ} {A} {.A ∷ al} (H-AΓ Z p) | fst₁ , (x ×i y) | fst , snd =
  (A ⊃ A) ∷ (fst ++ fst₁) , (lemma-proof-concat snd x ×i (λ q x₁ → h2 {l1 = al} {l2 = fst₁} {l3 = fst} (x₁) (y q)))
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-AΓ (S t) p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-AΓ (S t) p) | fst , (x ×i y) =
  let xxx = H-AΓ t x
      yyy = H-AK {A = a} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (a ⊃ (A ⊃ a)) ∷ a ∷ []
      rrr = (A ⊃ a) ∷ qqq
  in (rrr ++ fst) , (H-IM Z (S Z) (H-AK (H-AΓ t x)) ×i (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)))
theorem-deduction-hlaux {Γ} {A} {(A₁ ⊃ (B ⊃ .A₁)) ∷ al} (H-AK p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {(A₁ ⊃ (B ⊃ .A₁)) ∷ al} (H-AK p) | fst , (x ×i y) =
  let qq = A₁ ⊃ (B ⊃ A₁)
      xxx = H-AK {A = A₁} {B = B} x
      yyy = H-AK {A = qq} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (qq ⊃ (A ⊃ qq)) ∷ qq ∷ []
      rrr = (A ⊃ qq) ∷ qqq
  in (rrr ++ fst) , (H-IM Z (S Z) (H-AK (H-AK x)) ×i (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)))
theorem-deduction-hlaux {Γ} {A} {((A₁ ⊃ (B ⊃ C)) ⊃ .((A₁ ⊃ B) ⊃ (A₁ ⊃ C))) ∷ al} (H-AS p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {((A₁ ⊃ (B ⊃ C)) ⊃ .((A₁ ⊃ B) ⊃ (A₁ ⊃ C))) ∷ al} (H-AS p) | fst , (x ×i y) =
  let qq = (A₁ ⊃ (B ⊃ C)) ⊃ ((A₁ ⊃ B) ⊃ (A₁ ⊃ C))
      xxx = H-AS {A = A₁} {B = B} {C = C} x
      yyy = H-AK {A = qq} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (qq ⊃ (A ⊃ qq)) ∷ qq ∷ []
      rrr = (A ⊃ qq) ∷ qqq
  in (rrr ++ fst) , ((H-IM Z (S Z) (H-AK (H-AS x))) ×i (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)))
theorem-deduction-hlaux {Γ} {A} {((¬ A₁ ⊃ ¬ B) ⊃ .((¬ A₁ ⊃ B) ⊃ A₁)) ∷ al} (H-AN p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {((¬ A₁ ⊃ ¬ B) ⊃ .((¬ A₁ ⊃ B) ⊃ A₁)) ∷ al} (H-AN p) | fst , (x ×i y) =
  let qq = (¬ A₁ ⊃ ¬ B) ⊃ ((¬ A₁ ⊃ B) ⊃ A₁)
      xxx = H-AN {A = A₁} {B = B} x
      yyy = H-AK {A = qq} {B = A} xxx
      zzz = H-IM Z (S Z) yyy
      qqq = (qq ⊃ (A ⊃ qq)) ∷ qq ∷ []
      rrr = (A ⊃ qq) ∷ qqq
  in (rrr ++ fst) , (H-IM Z (S Z) (H-AK (H-AN x)) ×i (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)))
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-IM x x₁ p) with theorem-deduction-hlaux {Γ} {A} {al} p
theorem-deduction-hlaux {Γ} {A} {a ∷ al} (H-IM {A = B} {B = .a} x₂ x₃ p) | fst , (x ×i y) =
  let AB∈ = y B x₃
      AB→a∈ = y (B ⊃ a) x₂
      xxx = H-AS {A = A} {B = B} {C = a} x
      yyy = H-IM {A = A ⊃ (B ⊃ a)} {B = (A ⊃ B) ⊃ (A ⊃ a)} Z (S AB→a∈) xxx
      zzz = H-IM {A = A ⊃ B} {B = A ⊃ a} Z (S (S AB∈)) yyy
      qqq = ((A ⊃ B) ⊃ (A ⊃ a)) ∷ ((A ⊃ (B ⊃ a)) ⊃ ((A ⊃ B) ⊃ (A ⊃ a))) ∷ []
      rrr = (A ⊃ a) ∷ qqq
  in (rrr ++ fst) , (H-IM Z (S (S (y B x₃))) (H-IM Z (S (y (B ⊃ a) x₂)) (H-AS x)) ×i (λ q x₁ → h2 {l1 = al} {l2 = fst} {l3 = qqq} x₁ (y q)))

theorem-deduction-hl : ∀ {Γ A B} → A ∷ Γ h⊢ B → Γ h⊢ (A ⊃ B)
theorem-deduction-hl (fst , snd) with theorem-deduction-hlaux snd
theorem-deduction-hl {Γ} {A} {B} (fst , snd) | fst₁ , (x ×i y) = lemma-inproof (y B Z) x

data _t⊢_ (Γ : List CPC) : CPC → Set where
  T-AΓ : ∀ {A} → A ∈ Γ → Γ t⊢ A
  T-AN : ∀ {A B} → Γ t⊢ AN {A} {B}
  T-AK : ∀ {A B} → Γ t⊢ AK {A} {B}
  T-AS : ∀ {A B C} → Γ t⊢ AS {A} {B} {C}
  T-IM : ∀ {A B} → Γ t⊢ A → Γ t⊢ (A ⊃ B) → Γ t⊢ B

  
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

T-AI₂ : ∀ {Γ A} → Γ t⊢ (A ⊃ A)
T-AI₂ {Γ} {A} = t→h (H-AI {Γ} {A})

theorem-deduction-rev-t : ∀ {Γ A B} → Γ t⊢ (A ⊃ B) → A ∷ Γ t⊢ B
theorem-deduction-rev-t p = t→h (theorem-deduction-hl-rev (h→t p))

theorem-deduction-t : ∀ {Γ A B} → A ∷ Γ t⊢ B → Γ t⊢ (A ⊃ B)
theorem-deduction-t p = t→h (theorem-deduction-hl (h→t p))

theorem-deduction-t₂ : ∀ {Γ A B} → A ∷ Γ t⊢ B → Γ t⊢ (A ⊃ B)
theorem-deduction-t₂ (T-AΓ Z) = T-AI
theorem-deduction-t₂ (T-AΓ (S x)) = T-IM (T-AΓ x) T-AK
theorem-deduction-t₂ T-AN = T-IM T-AN T-AK
theorem-deduction-t₂ T-AK = T-IM T-AK T-AK
theorem-deduction-t₂ T-AS = T-IM T-AS T-AK
theorem-deduction-t₂ (T-IM p p₁) = T-IM (theorem-deduction-t₂ p) (T-IM (theorem-deduction-t₂ p₁) T-AS)

lemma-elim¬¬ : ∀ {Γ A} → Γ t⊢ (¬ (¬ A) ⊃ A)
lemma-elim¬¬ {Γ} {A} = theorem-deduction-t (T-IM (T-AI {A = ¬ A}) (T-IM (T-IM (T-AΓ Z) T-AK) T-AN))

data ⊥ : Set where

_t⊬_ : List CPC → CPC → Set
hl t⊬ a = (hl t⊢ a) → ⊥

data Bool : Set where
  true false : Bool

data _b=_ : Bool → Bool → Set where
  ET : true b= true
  EF : false b= false
  
impl : Bool → Bool → Bool
impl true false = false
impl x y = true

not : Bool → Bool
not true = false
not false = true

eval : (V → Bool) → CPC → Bool
eval sign (⋆ x) = sign x
eval sign (f ⊃ f₁) = impl (eval sign f) (eval sign f₁)
eval sign (¬ f) = not (eval sign f)

c⊨_ : CPC → Set
c⊨ f = (sign : V → Bool) → (eval sign f b= true) 

c⊮_ : CPC → Set
c⊮ f = (c⊨ f) → ⊥

lemma-taut-AN : ∀ {A B} → c⊨ AN {A} {B}
lemma-taut-AN {A} {B} sign with eval sign A | eval sign B
lemma-taut-AN sign | true | true = ET
lemma-taut-AN sign | true | false = ET
lemma-taut-AN sign | false | true = ET
lemma-taut-AN sign | false | false = ET

lemma-taut-AK : ∀ {A B} → c⊨ AK {A} {B}
lemma-taut-AK {A} {B} sign with eval sign A | eval sign B
lemma-taut-AK sign | true | true = ET
lemma-taut-AK sign | true | false = ET
lemma-taut-AK sign | false | true = ET
lemma-taut-AK sign | false | false = ET

lemma-taut-AS : ∀ {A B C} → c⊨ AS {A} {B} {C}
lemma-taut-AS {A} {B} {C} sign with eval sign A | eval sign B | eval sign C
lemma-taut-AS sign | true | true | true = ET
lemma-taut-AS sign | true | true | false = ET
lemma-taut-AS sign | true | false | true = ET
lemma-taut-AS sign | true | false | false = ET
lemma-taut-AS sign | false | true | true = ET
lemma-taut-AS sign | false | true | false = ET
lemma-taut-AS sign | false | false | true = ET
lemma-taut-AS sign | false | false | false = ET

lemma-taut-IM : ∀ {A B} → c⊨ A → c⊨ (A ⊃ B) → c⊨ B
lemma-taut-IM {A} {B} ta tab sign with ta sign | tab sign
... | ea | eab with eval sign A | eval sign B
lemma-taut-IM ta tab sign | ea | eab | true | true = eab
lemma-taut-IM ta tab sign | ea | eab | true | false = eab
lemma-taut-IM ta tab sign | ea | eab | false | true = eab
lemma-taut-IM ta tab sign | ea | eab | false | false = ea

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

bot-elim : (A : Set) → ⊥ → A
bot-elim a ()

-- Both A and ¬ A cannot be derived
theorem-consistency : ∀ {A} → [] t⊢ A → [] t⊢ ¬ A → ⊥
theorem-consistency {A} p pn with theorem-soundness p | theorem-soundness pn
... | x | y with x (λ sign → false) | y (λ sign → false)
... | xx | yy with eval (λ sign → false) A
theorem-consistency p pn | x | y | xx | () | true
theorem-consistency p pn | x | y | () | yy | false

_∨_ : CPC → CPC → CPC
a ∨ b = ¬ a ⊃ b

_∧_ : CPC → CPC → CPC
a ∧ b = ¬ (a ⊃ ¬ b)
--a ∧ b = ¬ (¬ a ∨ ¬ b)

and : Bool → Bool → Bool
and true true = true
and true false = false
and false true = false
and false false = false

or : Bool → Bool → Bool
or true true = true
or true false = true
or false true = true
or false false = false

lemma-∨-good : ∀ {A B e} → eval e (A ∨ B) b= or (eval e A) (eval e B)
lemma-∨-good {A} {B} {e} with eval e A | eval e B
lemma-∨-good | true | true = ET
lemma-∨-good | true | false = ET
lemma-∨-good | false | true = ET
lemma-∨-good | false | false = EF

lemma-∧-good : ∀ {A B e} → eval e (A ∧ B) b= and (eval e A) (eval e B)
lemma-∧-good {A} {B} {e} with eval e A | eval e B
lemma-∧-good | true | true = ET
lemma-∧-good | true | false = EF
lemma-∧-good | false | true = EF
lemma-∧-good | false | false = EF

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
      pa = T-IM {Γ = Γ₂} {A = ¬ (¬ A)} (T-AΓ Z) lemma-elim¬¬
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
  in T-IM nnb lemma-elim¬¬

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
  in lemma-∨-rightfalse {A = ¬ A} {B = B} (theorem-deduction-t (lemma-proof-replace-equiv {Γ = Γ₂} {A = ¬ (¬ A)} {B = A} {C = B} (T-IM (T-AΓ Z) (T-AΓ (S Z))) lemma-elim¬¬)) (T-AΓ (S Z)) 

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
  in theorem-deduction-t (T-IM zz lemma-elim¬¬)

lemma-∧-elim-left : ∀ {Γ A B} → Γ t⊢ (A ∧ B) ⊃ A
lemma-∧-elim-left {Γ} {A} {B} = lemma-true-antecedent -- theorem-deduction-t (lemma-true-antecedent {A = A} {B = ¬ B})

lemma-∧-elim-right : ∀ {Γ A B} → Γ t⊢ (A ∧ B) ⊃ B
lemma-∧-elim-right {Γ} {A} {B} =
  let xx = lemma-⊃-transpose {Γ = Γ} {A = ¬ B} {B = A ⊃ ¬ B}
      yy = T-IM T-AK xx
      zz = theorem-deduction-rev-t yy
  in theorem-deduction-t (T-IM zz lemma-elim¬¬)

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
  in theorem-deduction-t (T-IM nna lemma-elim¬¬)

lemma-∨-elim : ∀ {Γ A} → Γ t⊢ (A ∨ A) ⊃ A
lemma-∨-elim {Γ} {A} =
  let Γ₂ = ¬ A ⊃ A ∷ Γ
      xx : Γ₂ t⊢ (¬ A ⊃ A) ⊃ ((¬ A ⊃ ¬ A) ⊃ ¬ (¬ A))
      xx = T-ANn
      yy : Γ₂ t⊢ (¬ A ⊃ ¬ A) ⊃ ¬ (¬ A)
      yy = T-IM (T-AΓ Z) xx
  in theorem-deduction-t (T-IM (T-IM T-AI yy) lemma-elim¬¬)
  
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

lemma-invalid⊨-any : ∀ {A B} → c⊮ A → A ∷ [] t⊢ B
lemma-invalid⊨-any {A} {B} inv = {!!}

-- lemma-composition : ∀ 

lemma-invalid-var : ∀ {v} → c⊮ ⋆ v
lemma-invalid-var {v} ev with ev (λ v → false)
lemma-invalid-var ev | ()

lemma-completeness-¬ : ∀ {A} → (V → Bool) → [] t⊢ ¬ A
lemma-completeness-¬ {A} ev with eval ev A
lemma-completeness-¬ {A} ev | true = {!!}
lemma-completeness-¬ {A} ev | false = {!!}

theorem-completeness : ∀ {A} → c⊨ A → [] t⊢ A
theorem-completeness {⋆ x} taut with lemma-invalid-var taut
theorem-completeness {⋆ x} taut | ()
theorem-completeness {A ⊃ B} taut = {!!}
theorem-completeness {¬ A} taut = {!!}
