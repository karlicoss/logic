open import Prelude

module CPCCommon (N : ℕ) where

V = Fin N

infix 50 _⊃_
infix 60 _∨_
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

_∨_ : CPC → CPC → CPC
a ∨ b = ¬ a ⊃ b

_∧_ : CPC → CPC → CPC
a ∧ b = ¬ (a ⊃ ¬ b)
--a ∧ b = ¬ (¬ a ∨ ¬ b)

eval : (V → Bool) → CPC → Bool
eval sign (⋆ x) = sign x
eval sign (f ⊃ f₁) = (eval sign f) b⊃ (eval sign f₁)
eval sign (¬ f) = b¬ (eval sign f)

lemma-∨-good : ∀ {A B e} → eval e (A ∨ B) b= ((eval e A) b∨ (eval e B))
lemma-∨-good {A} {B} {e} with eval e A | eval e B
lemma-∨-good | true | true = ET
lemma-∨-good | true | false = ET
lemma-∨-good | false | true = ET
lemma-∨-good | false | false = EF

lemma-∧-good : ∀ {A B e} → eval e (A ∧ B) b= ((eval e A) b∧ (eval e B))
lemma-∧-good {A} {B} {e} with eval e A | eval e B
lemma-∧-good | true | true = ET
lemma-∧-good | true | false = EF
lemma-∧-good | false | true = EF
lemma-∧-good | false | false = EF

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
