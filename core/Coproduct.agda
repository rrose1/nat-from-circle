{-# OPTIONS --without-K #-}
module Coproduct where

open import Core
open import Path
open import Function
open import Sigma
open import Empty
open import Bool

open _≃_


module EqualityInCoproduct (X Y : Set l1) where
  code : X ⊎ Y → X ⊎ Y → Set l1
  code (inl x) (inl x') = x ≡ x'
  code (inl x) (inr y)  = ⊥
  code (inr y) (inl x)  = ⊥
  code (inr y) (inr y') = y ≡ y'

  r : (a : X ⊎ Y) → code a a
  r (inl x) = refl
  r (inr y) = refl

  enc : (a b : X ⊎ Y) → a ≡ b → code a b
  enc a b p = tpt (code a) p (r a)

  dec : (a b : X ⊎ Y) → code a b → a ≡ b
  dec (inl x) (inl x') p = ap inl p
  dec (inl x) (inr y)  a = rec⊥ a
  dec (inr y) (inl x)  a = rec⊥ a
  dec (inr y) (inr y') p = ap inr p

module _ {X Y : Set l1} where
  open EqualityInCoproduct
  
  inl-eq : {x x' : X} → _≡_ {X = X ⊎ Y} (inl x) (inl x') → x ≡ x'
  inl-eq {x} {x'} = enc X Y (inl x) (inl x')

  inr-eq : {y y' : Y} → _≡_ {X = X ⊎ Y} (inr y) (inr y') → y ≡ y'
  inr-eq {y} {y'} = enc X Y (inr y) (inr y')

  inl-neq-inr : {x : X} → {y : Y} → _≡_ {X = X ⊎ Y} (inl x) (inr y) → ⊥
  inl-neq-inr {x} {y} = enc X Y (inl x) (inr y)

module _ {i j} {X : Set i} {P Q : X → Set j} where
  tpt-coprod-l : {x y : X} → (p : x ≡ y) → (px : P x)
                 → tpt (λ x → P x ⊎ Q x) p (inl px) ≡ inl (tpt P p px)
  tpt-coprod-l refl px = refl

  tpt-coprod-r : {x y : X} → (p : x ≡ y) → (qx : Q x)
                 → tpt (λ x → P x ⊎ Q x) p (inr qx) ≡ inr (tpt Q p qx)
  tpt-coprod-r refl qx = refl

module _ {X : Set l1} {Y : Set l2}
         (ϕ : is-prop X) (ψ : is-prop Y)
         (d : X → Y → ⊥ {l1 ⊔ l2}) where
  is-prop-coprod : is-prop (X ⊎ Y)
  is-prop-coprod (inl x) (inl x') = ap inl (ϕ x x')
  is-prop-coprod (inl x) (inr y) = rec⊥ (d x y)
  is-prop-coprod (inr y) (inl x) = rec⊥ (d x y)
  is-prop-coprod (inr y) (inr y') = ap inr (ψ y y')


module _ {l1} where
  is-dec : Set l1 → Set l1
  is-dec X = X ⊎ (X → ⊥ {l1})

module _ {X : Set l1} where
  dec-dne : is-dec X → has-dne X
  dec-dne (inl x)  nnx = x
  dec-dne (inr nx) nnx = rec⊥ (nnx nx)

has-dec-eq : Set l1 → Set l1
has-dec-eq X = (x1 x2 : X) → (x1 ≡ x2) ⊎ (x1 ≢ x2)

module _ {X : Set l1} (ϕ : has-dec-eq X) where
  has-dec-eq->is-set : is-set X
  has-dec-eq->is-set {x1} {x2} = aux _ refl
    module has-dec-eq->is-set where
    aux : (a : is-dec (x1 ≡ x1)) → ϕ x1 x1 ≡ a → is-prop (x1 ≡ x2)
    aux (inl e3) e4 e1 e2 =
      g lwhisk-eqv (inl-eq (ap inl (! (tpt-const-eq-var e1 e3)) ◾
                            ! (tpt-coprod-l e1 e3) ◾
                            ! (ap (tpt _ e1) e4) ◾
                            apd _ (ϕ x1) e1 ◾
                            ! (apd _ (ϕ x1) e2) ◾
                            ap (tpt _ e2) e4 ◾
                            tpt-coprod-l e2 e3 ◾
                            ap inl (tpt-const-eq-var e2 e3)))  
    aux (inr n) = rec⊥ (n refl)


⊎-eq : {X1 X2 : Set l1} → X1 ≡ X2 →
       {Y1 Y2 : Set l2} → Y1 ≡ Y2 →
       (X1 ⊎ Y1) ≡ (X2 ⊎ Y2)
⊎-eq refl refl = refl

module _ {X : Set l1} {Y : Set l2} (n : X → ⊥ {l1}) where
  ⊎-unitl : (X ⊎ Y) ≃ Y
  f ⊎-unitl (inl x) = rec⊥ (n x)
  f ⊎-unitl (inr y) = y
  g ⊎-unitl         = inr
  η ⊎-unitl (inl x) = rec⊥ (n x)
  η ⊎-unitl (inr y) = refl
  h ⊎-unitl         = g ⊎-unitl
  ε ⊎-unitl _       = refl

module _ {X : Set l1} {Y : Set l2} (n : Y → ⊥ {l2}) where
  ⊎-unitr : (X ⊎ Y) ≃ X
  f ⊎-unitr (inl x) = x
  f ⊎-unitr (inr y) = rec⊥ (n y)
  g ⊎-unitr         = inl
  η ⊎-unitr (inl x) = refl
  η ⊎-unitr (inr y) = rec⊥ (n y)
  h ⊎-unitr         = g ⊎-unitr
  ε ⊎-unitr _       = refl

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} where
  ⊎-assoc : ((X ⊎ Y) ⊎ Z) ≃ (X ⊎ Y ⊎ Z)
  f ⊎-assoc (inl (inl x)) = inl x
  f ⊎-assoc (inl (inr y)) = inr (inl y)
  f ⊎-assoc (inr z) = inr (inr z)
  g ⊎-assoc (inl x) = inl (inl x)
  g ⊎-assoc (inr (inl y)) = inl (inr y)
  g ⊎-assoc (inr (inr z)) = inr z
  η ⊎-assoc (inl (inl x)) = refl
  η ⊎-assoc (inl (inr y)) = refl
  η ⊎-assoc (inr z) = refl
  h ⊎-assoc = g ⊎-assoc
  ε ⊎-assoc (inl x) = refl
  ε ⊎-assoc (inr (inl y)) = refl
  ε ⊎-assoc (inr (inr z)) = refl

module _ {X : Set l1} {Y : Set l2} where
  ⊎-com : (X ⊎ Y) ≃ (Y ⊎ X)
  f ⊎-com (inl x) = inr x
  f ⊎-com (inr y) = inl y
  g ⊎-com (inl y) = inr y
  g ⊎-com (inr x) = inl x
  η ⊎-com (inl x) = refl
  η ⊎-com (inr y) = refl
  h ⊎-com = g ⊎-com
  ε ⊎-com (inl y) = refl
  ε ⊎-com (inr x) = refl

module _ {X1 : Set l1} {X2 : Set l2} {Y1 : Set l3} {Y2 : Set l4}
         (e1 : X1 ≃ Y1) (e2 : X2 ≃ Y2) where
  infixr 5 _⊎e_
  _⊎e_ : (X1 ⊎ X2) ≃ (Y1 ⊎ Y2)
  f _⊎e_ (inl x) = inl (f e1 x)
  f _⊎e_ (inr y) = inr (f e2 y)
  g _⊎e_ (inl x) = inl (g e1 x)
  g _⊎e_ (inr y) = inr (g e2 y)
  η _⊎e_ (inl x) = ap inl (η e1 x)
  η _⊎e_ (inr y) = ap inr (η e2 y)
  h _⊎e_ (inl x) = inl (h e1 x)
  h _⊎e_ (inr y) = inr (h e2 y)
  ε _⊎e_ (inl x) = ap inl (ε e1 x)
  ε _⊎e_ (inr y) = ap inr (ε e2 y)


module _ {X : Set l1} {Y : Set l2} {P : X ⊎ Y → Set l3}
         (y0 : Y) (p0 : P (inr y0)) where
  open Retraction
  sigma-coprod-retr-r : Retraction (Σ (X ⊎ Y) (λ w → P w))
                                   (Σ Y (λ y → P (inr y)))
  f sigma-coprod-retr-r (inl x , p) = y0 , p0
  f sigma-coprod-retr-r (inr y , p) = y , p
  g sigma-coprod-retr-r (y , p) = inr y , p
  ε sigma-coprod-retr-r (y , p) = refl

module _ {X : Set l1} {Y : Set l2} (r : Retraction X Y) where
  open Retraction
  
  is-prop-retr : is-prop X → is-prop Y
  is-prop-retr ϕ y1 y2 = ! (ε r y1) ◾ ap (f r) (ϕ (g r y1) (g r y2)) ◾ ε r y2

module _ {X : Set l1} {Y : Set l2} where
  coprod-fst : X ⊎ Y → Bool
  coprod-fst (inl x) = false
  coprod-fst (inr y) = true

module _ {X : Set l1} {P Q : X → Set l2}
         (s : (x : X) → P x ⊎ Q x)
         (x : X)
         where
  dec-subtype-eqv : (Σ (Q x) (λ q → s x ≡ inr q)) ≃
                    (coprod-fst (s x) ≡ true)
  f dec-subtype-eqv (q , e1) = aux _ refl
    module f-dec-subtype-eqv where
    aux : (a : P x ⊎ Q x) → s x ≡ a → coprod-fst a ≡ true
    aux (inl p) e2 = rec⊥ (inl-neq-inr (! e2 ◾ e1))
    aux (inr q) e = refl
    
  g dec-subtype-eqv e1 = aux _ refl e1
    module g-dec-subtype-eqv where
    aux : (a : P x ⊎ Q x) → s x ≡ a → coprod-fst a ≡ true →
          Σ (Q x) (λ q → s x ≡ inr q)
    aux (inl p) _ ()
    aux (inr q) e2 _ = q , e2
  
  η dec-subtype-eqv (q1 , e1) =
    is-prop-retr (sigma-coprod-retr-r q1 e1) (const-eq-var-is-prop (s x)) _ _
    
  h dec-subtype-eqv = g dec-subtype-eqv
  ε dec-subtype-eqv e2 = Bool-is-set (f dec-subtype-eqv (h dec-subtype-eqv e2)) e2
