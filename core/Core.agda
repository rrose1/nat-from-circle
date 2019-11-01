{-# OPTIONS --without-K #-}
module Core where

open import Agda.Primitive public

variable
  l1 l2 l3 l4 l5 l6 : Level


infix 4 _≡_
data _≡_ {X : Set l1} (x : X) : X → Set l1 where
  refl : x ≡ x

infixr 4 _,_
record Σ (X : Set l1) (P : X → Set l2) : Set (l1 ⊔ l2) where
  constructor _,_
  field
    fst : X
    snd : P fst
open Σ public

infixr 6 _×_
_×_ : (X : Set l1) → (Y : Set l2) → Set (l1 ⊔ l2)
X × Y = Σ X (λ _ → Y)

data ⊥ {l1} : Set l1 where

data ⊤ : Set where
  tt : ⊤

data Bool : Set where
  false : Bool
  true : Bool

--------------------

infixr 5 _⊎_
data _⊎_ {l1 l2} (X : Set l1) (Y : Set l2) : Set (l1 ⊔ l2) where
  inl : X → X ⊎ Y
  inr : Y → X ⊎ Y

infix 4 _≃_
record _≃_ (X : Set l1) (Y : Set l2) : Set (l1 ⊔ l2) where
  constructor biinv
  field
    f : X → Y
    g : Y → X
    η : (x : X) → g (f x) ≡ x
    h : Y → X
    ε : (y : Y) → f (h y) ≡ y

record Retraction (X : Set l1) (Y : Set l2) : Set (l1 ⊔ l2) where
  constructor retr
  field
    f : X → Y
    g : Y → X
    ε : (y : Y) → f (g y) ≡ y
