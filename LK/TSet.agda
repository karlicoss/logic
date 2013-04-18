open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Nat

module TSet where

infixr 40 _∷_
data TSet (A : Set) : Set where
  ø : TSet A
  e_ : (a : A) → TSet A
  _∷_ : (a b : TSet A) → TSet A

data _f∈_ {A : Set} : A → TSet A → Set where
  Z : {a : A} → a f∈ e a
  AR : {a : A} {f g : TSet A} → a f∈ f → a f∈ f ∷ g -- append right
  AL : {a : A} {f g : TSet A} → a f∈ g → a f∈ f ∷ g -- append left

_f∉_ : {A : Set} → A → TSet A → Set
a f∉ s = ¬ (a f∈ s)
  
tmap : ∀ {A B} → (A → B) → TSet A → TSet B
tmap f ø = ø
tmap f (e a) = e (f a)
tmap f (l ∷ r) = tmap f l ∷ tmap f r


module TSetOps (A : Set) (cmp : (a : A) → (b : A) → Dec (a ≡ b)) where
  tadd : A → TSet A → TSet A
  tadd a s = (e a) ∷ s
  
  tdel : A → TSet A → TSet A
  tdel a ø = ø
  tdel a (e b) with cmp a b
  tdel a (e b) | yes a₁ = ø
  tdel a (e b) | no l¬a = e b
  tdel a (l ∷ r) = tdel a l ∷ tdel a r

  lemma-tdel : (d : A) → (s : TSet A) → d f∉ (tdel d s)
  lemma-tdel d ø ()
  lemma-tdel d (e a) p with cmp d a
  lemma-tdel d (e a) () | yes a₁
  lemma-tdel d (e .d) Z | no l¬a = l¬a refl
  lemma-tdel d (l ∷ r) (AR p) = lemma-tdel d l p
  lemma-tdel d (l ∷ r) (AL p) = lemma-tdel d r p

data _♯_ { A : Set} : TSet A → TSet A → Set where
  REFL : ∀ {S} → S ♯ S
  SIMM : ∀ {S T} → S ♯ T → T ♯ S
  TRANS : ∀ {S T U} → S ♯ T → T ♯ U → S ♯ U
  AL : ∀ {S T U} → S ♯ T → U ∷ S ♯ U ∷ T
  AR : ∀ {S T U} → S ♯ T → S ∷ U ♯ T ∷ U
  AZL : ∀ {S} → S ♯ ø ∷ S
  AZR : ∀ {S} → S ♯ S ∷ ø
  RZL : ∀ {S} → ø ∷ S ♯ S
  RZR : ∀ {S} → S ∷ ø ♯ S
  SW : ∀ {S T} → S ∷ T ♯ T ∷ S
  SWL : ∀ {S T U} → S ∷ (T ∷ U) ♯ T ∷ (S ∷ U)
  SWR : ∀ {S T U} → (S ∷ T) ∷ U ♯ (S ∷ U) ∷ T
  RTL : ∀ {S T U} → S ∷ (T ∷ U) ♯ (S ∷ T) ∷ U
  RTR : ∀ {S T U} → (S ∷ T) ∷ U ♯ S ∷ (T ∷ U)

infixr 10 _♯∙_
_♯∙_ : {A : Set} {S T U : TSet A} → S ♯ T → T ♯ U → S ♯ U
_♯∙_ = TRANS


lemma-ooo : ((e 0) ∷ (e 1)) ∷ ((e 2) ∷ (e 3)) ♯ ((e 3) ∷ (e 2)) ∷ ((e 1) ∷ (e 0))
lemma-ooo = RTR ♯∙ AL (AL SW) ♯∙ AL SWL ♯∙ SWL ♯∙ AL (AL SW ♯∙ SWL ♯∙ AL SW) ♯∙ RTL
