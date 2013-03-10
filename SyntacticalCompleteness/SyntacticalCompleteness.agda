module SyntacticalCompleteness where

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

data V : Set where
  varA varB varC varD varE : V

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
  H-EM : Γ hl⊢ []                                                 -- empty list is a valid
                                                                  -- proof sequence
  H-AΓ : ∀ {A pl} → A ∈ Γ → Γ hl⊢ pl → Γ hl⊢ (A ∷ pl)             -- assumption
  H-AK : ∀ {A B pl} → Γ hl⊢ pl       → Γ hl⊢ AK {A = A} {B = B} ∷ pl -- K
  H-AS : ∀ {A B C pl} → Γ hl⊢ pl     → Γ hl⊢ AS {A = A} {B = B} {C = C} ∷ pl -- S
  H-AN : ∀ {A B pl} → Γ hl⊢ pl       → Γ hl⊢ AN {A = A} {B = B} ∷ pl -- N
  H-IM : ∀ {A B pl} → (A ⊃ B) ∈ pl → A ∈ pl → Γ hl⊢ pl → Γ hl⊢ (B ∷ pl) -- modus ponens
  
_h⊢_ : (Γ : List CPC) → CPC → Set
Γ h⊢ A = Σ (List CPC) (λ pl → Γ hl⊢ (A ∷ pl))

T-AI : ∀ {Γ A} → Γ h⊢ (A ⊃ A)
T-AI {A = A} = {!!} , {!!} 

  
