open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Nat

module TSet where

infixr 40 _∷_
data TSet (A : Set) : Set where
  ø : TSet A
  el_ : (a : A) → TSet A
  _∷_ : (a b : TSet A) → TSet A

data _f∈_ {A : Set} : A → TSet A → Set where
  Z : {a : A} → a f∈ el a
  SL : {a : A} {f g : TSet A} → a f∈ f → a f∈ f ∷ g
  SR : {a : A} {f g : TSet A} → a f∈ g → a f∈ f ∷ g

_f∉_ : {A : Set} → A → TSet A → Set
a f∉ s = ¬ (a f∈ s)
  
tmap : ∀ {A B} → (A → B) → TSet A → TSet B
tmap f ø = ø
tmap f (el a) = el (f a)
tmap f (l ∷ r) = tmap f l ∷ tmap f r


module TSetOps (A : Set) (cmp : (a : A) → (b : A) → Dec (a ≡ b)) where
  tadd : A → TSet A → TSet A
  tadd a s = (el a) ∷ s
  
  tdel : A → TSet A → TSet A
  tdel a ø = ø
  tdel a (el b) with cmp a b
  tdel a (el b) | yes a₁ = ø
  tdel a (el b) | no l¬a = el b
  tdel a (l ∷ r) = tdel a l ∷ tdel a r

  lemma-tdel : (d : A) → (s : TSet A) → d f∉ (tdel d s)
  lemma-tdel d ø ()
  lemma-tdel d (el a) p with cmp d a
  lemma-tdel d (el a) () | yes a₁
  lemma-tdel d (el .d) Z | no l¬a = l¬a refl
  lemma-tdel d (l ∷ r) (SL p) = lemma-tdel d l p
  lemma-tdel d (l ∷ r) (SR p) = lemma-tdel d r p

data _s♯_ { A : Set} : TSet A → TSet A → Set where
  Z : ø s♯ ø
  SL : ∀ {a sa sb} → sa s♯ sb → a ∷ sa s♯ a ∷ sb
  SR : ∀ {a sa sb} → sa s♯ sb → sa ∷ a s♯ sb ∷ a
  SW : ∀ {a b} → a ∷ b s♯ b ∷ a
  SWL : ∀ {a b c} → a ∷ (b ∷ c) s♯ b ∷ (a ∷ c)
  SWR : ∀ {a b c} → (a ∷ b) ∷ c s♯ (a ∷ c) ∷ b
  RL : ∀ {a b c} → a ∷ (b ∷ c) s♯ (a ∷ b) ∷ c
  RR : ∀ {a b c} → (a ∷ b) ∷ c s♯ a ∷ (b ∷ c)
  TR : ∀ {a b c} → a s♯ b → b s♯ c → a s♯ c
  SIMM : ∀ {a b} → a s♯ b → b s♯ a
  
infixr 10 _s∙_
_s∙_ : {A : Set} {p q r : TSet A} → p s♯ q → q s♯ r → p s♯ r
_s∙_ = TR


lemma-ooo : ((el 0) ∷ (el 1)) ∷ ((el 2) ∷ (el 3)) s♯ ((el 3) ∷ (el 2)) ∷ ((el 1) ∷ (el 0))
lemma-ooo = RR s∙ (SL (SL SW) s∙ SL SWL s∙ SWL s∙ SL (SL SW s∙ SWL s∙ SL SW)) s∙ RL
