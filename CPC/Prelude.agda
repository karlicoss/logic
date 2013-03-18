module Prelude where

infix 10 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

infixr 5 _~_
_~_ : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
_~_ = trans

cong : ∀ {A B} {a b : A} → (f : A → B) → a ≡ b → (f a) ≡ (f b)
cong f refl = refl

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


data ⊥ : Set where

bot-elim : (A : Set) → ⊥ → A
bot-elim a ()

data Bool : Set where
  true false : Bool

data _b=_ : Bool → Bool → Set where
  ET : true b= true
  EF : false b= false

infix 50 _b⊃_
infixl 60 _b∨_
infixl 70 _b∧_
  
_b⊃_ : Bool → Bool → Bool
true b⊃ false = false
x b⊃ y = true

b¬ : Bool → Bool
b¬ true = false
b¬ false = true

_b∧_ : Bool → Bool → Bool
true b∧ true = true
true b∧ false = false
false b∧ true = false
false b∧ false = false

_b∨_ : Bool → Bool → Bool
true b∨ true = true
true b∨ false = true
false b∨ true = true
false b∨ false = false

lemma-b∧-ololo : ∀ {a b} → a ≡ true → b ≡ true → a b∧ b ≡ true
lemma-b∧-ololo {true} {true} pa pb = refl
lemma-b∧-ololo {true} {false} pa pb = pb
lemma-b∧-ololo {false} {true} pa pb = pa
lemma-b∧-ololo {false} {false} pa pb = pb

lemma-b∧-left : ∀ {a b} → a b∧ b ≡ true → a ≡ true
lemma-b∧-left {true} p = refl
lemma-b∧-left {false} {true} p = p
lemma-b∧-left {false} {false} p = p

lemma-b∧-right : ∀ {a b} → a b∧ b ≡ true → b ≡ true
lemma-b∧-right {a} {true} p = refl
lemma-b∧-right {true} {false} p = p
lemma-b∧-right {false} {false} p = p

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_n+_ : ℕ → ℕ → ℕ
zero n+ b = b
(succ a) n+ b = succ (a n+ b)

lemma-zero-right : ∀ {a} → a ≡ (a n+ zero)
lemma-zero-right {zero} = refl
lemma-zero-right {succ a} = cong succ lemma-zero-right

lemma-succ-left : ∀ {a b} → a n+ succ b ≡ succ (a n+ b)
lemma-succ-left {zero} {b} = refl
lemma-succ-left {succ a} {b} = cong succ (lemma-succ-left {a = a} {b = b})

lemma-succ-right : ∀ {a b} → (succ a) n+ b ≡ succ (a n+ b)
lemma-succ-right {a} {b} = refl

lemma-n+-comm : ∀ {a} {b} → (a n+ b) ≡ (b n+ a)
lemma-n+-comm {zero} {zero} = refl
lemma-n+-comm {zero} {succ b} = cong succ lemma-zero-right
lemma-n+-comm {succ a} {zero} = cong succ (sym lemma-zero-right)
lemma-n+-comm {succ a} {succ b} = cong succ (lemma-succ-left {a = a} {b = b} ~ sym (lemma-n+-comm {a = b} {b = succ a} ~ lemma-succ-right {a = a} {b = b}))

lemma-n+-assoc : ∀ {a b c} → (a n+ (b n+ c)) ≡ ((a n+ b) n+ c)
lemma-n+-assoc {zero} {b} {c} = refl
lemma-n+-assoc {succ a} {b} {c} = cong succ (lemma-n+-assoc {a = a} {b = b} {c = c})

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)
