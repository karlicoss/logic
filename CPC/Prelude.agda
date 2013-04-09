module Prelude where

data ⊥ : Set where

bot-elim : (A : Set) → ⊥ → A
bot-elim a ()

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

data Dec (A : Set) : Set where
  yes : (a : A) → Dec A
  no  : (¬a : A → ⊥) → Dec A

infixr 40 _∷_
data List (A : Set) : Set where
  [] : List A                            -- an empty list
  _∷_ : (a : A) → (as : List A) → List A -- "cons" -- creates a new list with "a" in the head
                                           -- and "as" in the tail

-- appending two lists
_++_ : ∀ {A} → List A → List A → List A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

map : ∀ {A B} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

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

[]-reverseh : ∀ {A} → List A → List A → List A
[]-reverseh acc [] = acc
[]-reverseh acc (a ∷ l) = []-reverseh (a ∷ acc) l

[]-reverse : ∀ {A} → List A → List A
[]-reverse l = []-reverseh [] l

-- TODO prove reverse!

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infix 40 _×_

data _×_ (P : Set) (Q : Set) : Set where
  <_,_> : P → Q → P × Q

×fst : ∀ {P Q} → P × Q → P
×fst < p , q > = p

×snd : ∀ {P Q} → P × Q → Q
×snd < p , q > = q

infix 40 _∨_
data _∨_ (P Q : Set) : Set where
  injl : P → P ∨ Q
  injr : Q → P ∨ Q


data Bool : Set where
  true false : Bool

_b=?_ : (a b : Bool) → Dec (a ≡ b)
true b=? true = yes refl
true b=? false = no (λ ())
false b=? true = no (λ ())
false b=? false = yes refl

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

postulate Level : Set
postulate lzero : Level
postulate lsucc : Level → Level
postulate _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsucc #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

if_then_else : {α : Level} {A : Set α} → Bool → A → A → A
if true then t else e = t
if false then t else e = e

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- TODO make private
lemma-nozero-pred : ∀ {a : ℕ} → succ a ≡ zero → ⊥
lemma-nozero-pred ()

-- TODO make private
lemma-succ-qqq : ∀ {a b : ℕ} → (succ a ≡ succ b) → a ≡ b
lemma-succ-qqq refl = refl

-- TODO make private
lemma-qqq : ∀ {a b : ℕ} → (a ≡ b → ⊥) → ((succ a) ≡ (succ b) → ⊥)
lemma-qqq {a} {b} p ps = p (lemma-succ-qqq ps)


data _n>_ : ℕ → ℕ → Set where
  n>-zero : {a : ℕ} → (succ a) n> zero
  n>-succ : {a b : ℕ} → a n> b → (succ a) n> (succ b)

data _n<_ : ℕ → ℕ → Set where
  n<-zero : {b : ℕ} → zero n< succ (b)
  n<-succ : {a b : ℕ} → a n< b → (succ a) n< (succ b)
  
_gt_ : (a b : ℕ) → Bool
zero gt b = false
a gt zero = true
(succ a) gt (succ b) = a gt b

lemma-gt : ∀ {a b} → a n> b → a gt b ≡ true
lemma-gt n>-zero = refl
lemma-gt (n>-succ p) = lemma-gt p

lemma-gt-rev : ∀ {a b} → a gt b ≡ true → a n> b
lemma-gt-rev {zero} {zero} ()
lemma-gt-rev {succ a} {zero} p = n>-zero
lemma-gt-rev {zero} {succ b} ()
lemma-gt-rev {succ a} {succ b} p = n>-succ (lemma-gt-rev p)

lemma-n<-succ : ∀ {a} → a n< succ a
lemma-n<-succ {zero} = n<-zero
lemma-n<-succ {succ a} = n<-succ lemma-n<-succ

lemma-n<-elim-succ-left : ∀ {a b} → (succ a) n< b → a n< b
lemma-n<-elim-succ-left {zero} {zero} ()
lemma-n<-elim-succ-left {zero} {succ b} p = n<-zero
lemma-n<-elim-succ-left {succ a} {zero} ()
lemma-n<-elim-succ-left {succ a} {succ b} (n<-succ p) = n<-succ (lemma-n<-elim-succ-left p)

lemma-n<-elim-succ-both : ∀ {a b} → (succ a n< succ b) → a n< b
lemma-n<-elim-succ-both {zero} {zero} (n<-succ p) = p
lemma-n<-elim-succ-both {zero} {succ b} p = n<-zero
lemma-n<-elim-succ-both {succ a} {zero} (n<-succ ())
lemma-n<-elim-succ-both {succ a} {succ b} (n<-succ p) = p

_lt_ : (a b : ℕ) → Bool
a lt zero = false
zero lt b = true
(succ a) lt (succ b) = a lt b

lemma-lt : ∀ {a b} → a n< b → a lt b ≡ true
lemma-lt n<-zero = refl
lemma-lt (n<-succ p) = lemma-lt p

lemma-lt-rev : ∀ {a b} → a lt b ≡ true → a n< b
lemma-lt-rev {zero} {zero} ()
lemma-lt-rev {zero} {succ b} p = n<-zero
lemma-lt-rev {succ a} {zero} ()
lemma-lt-rev {succ a} {succ b} p = n<-succ (lemma-lt-rev p)

_n=?_ : (a b : ℕ) → Dec (a ≡ b)
zero n=? zero = yes refl
zero n=? succ b = no (λ ())
succ a n=? zero = no (λ ())
succ a n=? succ b with a n=? b
succ a n=? succ .a | yes refl = yes refl
succ a n=? succ b | no ¬a = no (lemma-qqq ¬a)

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

i1 : Fin (succ zero)
i1 = fzero {zero}

i2 : Fin (succ (succ zero))
i2 = fsucc {succ zero} i1

fmax : {n : ℕ} → Fin (succ n)
fmax {zero} = fzero
fmax {succ n} = fsucc (fmax {n})

femb : {n : ℕ} → Fin n → Fin (succ n)
femb fzero = fzero
femb (fsucc i) = fsucc (femb i)
