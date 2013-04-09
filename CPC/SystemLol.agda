open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import MyPrelude

module SystemLol where

-- open import Prelude

-- ▬ is \re
-- ■ is \sq
-- ● is \ci
-- ⊢ is \vdash
-- ↯ is \dz


-- WFF (denoted by ↯, I picked it because it looks awesome) consist of sequences like
-- ▬
-- ●●■▬
-- ●▬
-- ●●■■●■●▬
data ↯ : Set where
  ▬ : ↯
  ■_ : ↯ → ↯
  ●_ : ↯ → ↯

-- rule AΓ allows to deduce something assumed
-- rule AX is an axiom
-- rule AI is an inference rule
data _⊢_ (Γ : List ↯) : ↯ → Set where
  AΓ : ∀ {A} → A ∈ Γ → Γ ⊢ A
  AX : Γ ⊢ ■ ▬
  AI : ∀ {A} → Γ ⊢ A → Γ ⊢ ● A

-- you might notice the sequences deducible by these rules 
-- end by ■ ▬ and contain no other ■. Let's prove it!

endswith■ : ↯ → Bool
endswith■ ▬ = false
endswith■ (■ ▬) = true
endswith■ (● ▬) = false
endswith■ (■ x) = endswith■ x
endswith■ (● x) = endswith■ x

no■ : ↯ → Bool
no■ ▬ = true
no■ (■ f) = false
no■ (● f) = no■ f

onlyone■ : ↯ → Bool
onlyone■ ▬ = false
onlyone■ (■ f) = no■ f
onlyone■ (● f) = onlyone■ f

-- we want to prove consistency, that is, anything deducible from ⊢ is
-- a 'good sequence', that is, contains exactly one ■ which is at the
-- end of the formula
goodseq : ↯ → Bool
goodseq f = endswith■ f ∧ onlyone■ f

-- some useful lemmas

-- if a formula contains only one ■, it won't hurt if we prepend a ●
lemma-●₁ : ∀ {A} → onlyone■ A ≡ true → onlyone■ (● A) ≡ true
lemma-●₁ {A} p with onlyone■ A
lemma-●₁ p | true = refl
lemma-●₁ () | false

-- similarly, if a formula contains only one ■, it won't hurt to
-- prepend a ● 
lemma-●₂ : ∀ {A} → endswith■ A ≡ true → endswith■ (● A) ≡ true
lemma-●₂ {▬} ()
lemma-●₂ {■ A} p = p
lemma-●₂ {● A} p = p

-- the ■ is somewhere in the tail
lemma-●₃ : ∀ {A} → endswith■ (● A) ≡ true → endswith■ A ≡ true
lemma-●₃ {▬} ()
lemma-●₃ {■ A} p = p
lemma-●₃ {● A} p = p

theorem-↯-consistency : ∀ {A} → [] ⊢ A → goodseq A ≡ true
theorem-↯-consistency (AΓ ())
theorem-↯-consistency AX = refl
theorem-↯-consistency {● A} (AI {.A} p) with theorem-↯-consistency p
... | xx with lemma-b∧-left {a = endswith■ A} {b = onlyone■ A} xx | lemma-b∧-right {a = endswith■ A} {b = onlyone■ A} xx
... | yy | zz = lemma-b∧-ololo {a = endswith■ (● A)} {b = onlyone■ A} (lemma-●₂ {A = A} yy) zz

-- now we shall prove the other direction: every formula containing
-- exactly one ■ at the end is deducible

-- formula ending with ■ has to contain at least one square!
lemma-■ : ∀ {A} → endswith■ A ≡ true → no■ A ≢ true
lemma-■ {▬} () n
lemma-■ {■ A} e ()
lemma-■ {● A} e n = lemma-■ {A} (lemma-●₃ {A = A} e) n

theorem-↯-completeness : ∀ {A} → goodseq A ≡ true → [] ⊢ A
theorem-↯-completeness {▬} ()
theorem-↯-completeness {■ ▬} p = AX
theorem-↯-completeness {■ (■ A)} p with lemma-b∧-right {a = endswith■ (■ A)} {b = false}  p
theorem-↯-completeness {■ (■ A)} p | ()
theorem-↯-completeness {■ (● A)} p with lemma-b∧-left {a = endswith■ (● A)} {b = no■ A} p | lemma-b∧-right {a = endswith■ (● A)} {b = no■ A} p
... | xx | yy with lemma-■ {● A} xx yy
theorem-↯-completeness {■ (● A)} p | xx | yy | ()
theorem-↯-completeness {● A} p with lemma-b∧-left {a = endswith■ (● A)} {b = onlyone■ A} p | lemma-b∧-right {a = endswith■ (● A)} {b = onlyone■ A} p
... | xx | yy = AI (theorem-↯-completeness {A} (lemma-b∧-ololo {a = endswith■ A} {b = onlyone■ A} (lemma-●₃ {A = A} xx) yy))

-- yay!
