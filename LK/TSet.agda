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
--  E : ∀ {a} → e a ♯ e a
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

lem-♯-sim : ∀ {A} → {S T : TSet A} → S ♯ T → T ♯ S 
lem-♯-sim REFL = REFL
lem-♯-sim (AL p) = AL (lem-♯-sim p)
lem-♯-sim (AR p) = AR (lem-♯-sim p)
lem-♯-sim AZL = RZL
lem-♯-sim AZR = RZR
lem-♯-sim RZL = AZL
lem-♯-sim RZR = AZR
lem-♯-sim SW = SW
lem-♯-sim SWL = SWL
lem-♯-sim SWR = SWR
lem-♯-sim RTL = RTR
lem-♯-sim RTR = RTL

lem-♯-comb : ∀ {A} → {S T U V : TSet A} → S ♯ T → U ♯ V → S ∷ U ♯ T ∷ V
lem-♯-comb REFL q = AL q
lem-♯-comb (AL p) q with lem-♯-comb p q
... | xx = {!!}
lem-♯-comb (AR p) q = {!!}
lem-♯-comb AZL q = {!!}
lem-♯-comb AZR q = {!!}
lem-♯-comb RZL q = {!!}
lem-♯-comb RZR q = {!!}
lem-♯-comb SW q = {!!}
lem-♯-comb SWL q = {!!}
lem-♯-comb SWR q = {!!}
lem-♯-comb RTL q = {!!}
lem-♯-comb RTR q = {!!}


lem-♯-trans : ∀ {A} → {S T U : TSet A} → S ♯ T → T ♯ U → S ♯ U
lem-♯-trans REFL q = q
lem-♯-trans (AL p) REFL = AL p
lem-♯-trans (AL p) (AL q) = AL (lem-♯-trans p q)
lem-♯-trans (AL p) (AR q) = {!!}
lem-♯-trans (AL p) AZL = lem-♯-sim {!!}
lem-♯-trans (AL p) AZR = {!!}
lem-♯-trans (AL p) RZL = {!!}
lem-♯-trans (AL p) RZR = {!!}
lem-♯-trans (AL p) SW = {!!}
lem-♯-trans (AL p) SWL = {!!}
lem-♯-trans (AL p) SWR = {!!}
lem-♯-trans (AL p) RTL = {!!}
lem-♯-trans (AL p) RTR = {!!}
lem-♯-trans (AR p) q = {!!}
lem-♯-trans AZL q = {!!}
lem-♯-trans AZR q = {!!}
lem-♯-trans RZL q = {!!}
lem-♯-trans RZR q = {!!}
lem-♯-trans SW q = {!!}
lem-♯-trans SWL q = {!!}
lem-♯-trans SWR q = {!!}
lem-♯-trans RTL q = {!!}
lem-♯-trans RTR q = {!!}

--   AL : ∀ {a sa sb} → sa s♯ sb → a ∷ sa s♯ a ∷ sb
--   AR : ∀ {a sa sb} → sa s♯ sb → sa ∷ a s♯ sb ∷ a
--   
--   SEL : ∀ {a} → a s♯ ø ∷ a
--   SER : ∀ {a} → a s♯ a ∷ ø
--   SW : ∀ {a b} → a ∷ b s♯ b ∷ a
--   SWL : ∀ {a b c} → a ∷ (b ∷ c) s♯ b ∷ (a ∷ c)
--   SWR : ∀ {a b c} → (a ∷ b) ∷ c s♯ (a ∷ c) ∷ b
--   RL : ∀ {a b c} → a ∷ (b ∷ c) s♯ (a ∷ b) ∷ c
--   RR : ∀ {a b c} → (a ∷ b) ∷ c s♯ a ∷ (b ∷ c)
--   TR : ∀ {a b c} → a s♯ b → b s♯ c → a s♯ c
--   SIMM : ∀ {a b} → a s♯ b → b s♯ a
--   CP : ∀ {a} → a ∷ a s♯ a
  
infixr 10 _s∙_
_s∙_ : {A : Set} {p q r : TSet A} → p ♯ q → q ♯ r → p ♯ r
_s∙_ = {!!}


-- lemma-ooo : ((e 0) ∷ (e 1)) ∷ ((e 2) ∷ (e 3)) s♯ ((e 3) ∷ (e 2)) ∷ ((e 1) ∷ (e 0))
-- lemma-ooo = RR s∙ (SL (SL SW) s∙ SL SWL s∙ SWL s∙ SL (SL SW s∙ SWL s∙ SL SW)) s∙ RL
