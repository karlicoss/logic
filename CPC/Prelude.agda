module Prelude where

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
