open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List
open import MyPrelude
open import TSet

module Test (V : Set) (cmpv : (a b : V) → Dec (a ≡ b)) where
  open import LJ V cmpv public

  data _t⊢_ (Γ : List IPC) : IPC → Set where
    T-I : ∀ {A} → A ∈ Γ   → Γ t⊢ A
    T-N : ∀ {A B}         → Γ t⊢ (l¬ A) ⊃ (A ⊃ B)
    T-AK : ∀ {A B}        → Γ t⊢ (A ⊃ (B ⊃ A))
    T-AS : ∀ {A B C}      → Γ t⊢ ((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C)))
    T-MP : ∀ {A B} → Γ t⊢ (A ⊃ B) → Γ t⊢ A → Γ t⊢ B
{-
  t→s : ∀ {A} → [] t⊢ A → ø s⊢ rhs A
  t→s (T-I ())
  t→s (T-N {A} {B}) = S-→R (S-→R (S-R (S-E (SIMM ((SL SW s∙ SWL) s∙ SIMM SEL)) lemma-a¬a)))
  t→s (T-AK {A} {B}) = S-→R (S-→R (S-I (SR (SL Z))))
  t→s (T-AS {A} {B} {C}) = S-→R (S-→R (S-→R (S-E (SL SWL s∙ SWL s∙ SL SWL) (S-→L (S-I (SR (SL Z))) (S-E SWL (S-→L (S-I (SR (SL Z))) (S-E SWL (S-→L (S-I (SL Z)) (S-I (SL Z))))))))))
  t→s (T-MP {A} {B} ab a) = lemma-mp (t→s a) (t→s ab)
-}

  listtotset : ∀ {T} → List T → TSet T
  listtotset [] = ø
  listtotset (x ∷ l) = el x ∷ listtotset l

  lemma-listtotset : ∀ {T} {ls : List T} {a : T} → a ∈ ls → a f∈ (listtotset ls)
  lemma-listtotset Z = SL Z
  lemma-listtotset (S p) = SR (lemma-listtotset p)

  t→s : ∀ {Γ A} → Γ t⊢ A → (listtotset Γ) s⊢ rhs A
  t→s (T-I x) = S-I (lemma-listtotset x)
  t→s T-N = S-→R (S-→R (S-R lemma-a¬a))
  t→s T-AK = lemma-a⊃b⊃a
  t→s T-AS = lemma-a⊃b⊃c⊃a⊃b⊃a⊃c
  t→s (T-MP ab a) = lemma-mp (t→s a) (t→s ab)

  tsettolist : ∀ {T} → TSet T → List T
  tsettolist ø = []
  tsettolist (el a) = a ∷ []
  tsettolist (l ∷ r) = tsettolist l ++ tsettolist r

  lemma-tsettolist : ∀ {T} {ts : TSet T} {a : T} → a f∈ ts → a ∈ (tsettolist ts)
  lemma-tsettolist Z = Z
  lemma-tsettolist (SL {a} {f} {g} p) with lemma-tsettolist p
  ... | xx = relax-right {as = tsettolist f} {bs = tsettolist g} xx
  lemma-tsettolist (SR {a} {f} {g} p) with lemma-tsettolist p
  ... | xx = relax-left (tsettolist f) xx

  -- TODO need some structural lemmas for tree style calculus to be proven
  s→t : ∀ {Γ A} → Γ s⊢ rhs A → (tsettolist Γ) t⊢ A
  s→t (S-I x) = T-I (lemma-tsettolist x)
  s→t (S-¬R p) = {!!}
  s→t (S-→L p p₁) = {!!}
  s→t (S-→R p) = {!!}
  s→t (S-C p p₁) = {!!}
  s→t (S-E x p) = {!!}
  s→t (S-R p) = {!!}
  s→t (S-W p) = {!!}
{-
  s→t : ∀ {A} → ø s⊢ rhs A → [] t⊢ A
  s→t (S-I ())
  s→t (S-¬R p) = {!!}
  s→t (S-→R p) = {!!}
  s→t (S-E x p) = {!!}
  s→t (S-R p) = {!!}
-}
