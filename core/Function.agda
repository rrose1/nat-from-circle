{-# OPTIONS --without-K #-}
module Function where

open import Core
open import Path


module _ {l1} (X : Set l1) where
  type-of : X → X
  type-of x = x

module _ {X : Set l1} where
  id : X → X
  id x = x

module _ {X : Set l1} {P : X → Set l2} {f g : (x : X) → P x} where
  postulate
    funext : ((x : X) → f x ≡ g x) → f ≡ g
    funext-happly : (e : f ≡ g) → funext (λ x → ap (λ f → f x) e) ≡ e
    happly-funext : (ϕ : ((x : X) → f x ≡ g x)) →
                    (λ x → ap (λ f → f x) (funext ϕ)) ≡ ϕ

  happly-eqv : (f ≡ g) ≃ ((x : X) → f x ≡ g x)
  _≃_.f happly-eqv e x = ap (λ a → a x) e
  _≃_.g happly-eqv = funext 
  _≃_.η happly-eqv = funext-happly
  _≃_.h happly-eqv = _≃_.g happly-eqv
  _≃_.ε happly-eqv = happly-funext


module _ {X : Set l1} {P : X → Set l2} {f g : {x : X} → P x} where
  postulate
    funext' : ({x : X} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
    funext-happly' : (e : (λ {x} → f {x}) ≡ g) →
                     funext' (λ {x} → ap (λ f → f {x}) e) ≡ e
    happly-funext' : (ϕ : ({x : X} → f {x} ≡ g {x})) →
                     (λ {x} → ap (λ f → f {x}) (funext' ϕ)) ≡ ϕ

  happly'-eqv : ((λ {x} → f {x}) ≡ g) ≃ ({x : X} → f {x} ≡ g {x})
  _≃_.f happly'-eqv e {x} = ap (λ a → a {x}) e 
  _≃_.g happly'-eqv = funext'
  _≃_.η happly'-eqv = funext-happly'
  _≃_.h happly'-eqv = _≃_.g happly'-eqv
  _≃_.ε happly'-eqv = happly-funext'


module _ {X : Set l1} {P : X → Set l2} where
  is-prop-pi : ((x : X) → is-prop (P x)) → is-prop ((x : X) → P x)
  is-prop-pi ϕ f g = funext (λ x → ϕ x (f x) (g x))

  is-prop-pi' : ({x : X} → is-prop (P x)) → is-prop ({x : X} → P x)
  is-prop-pi' ϕ f g = funext' (λ {x} → ϕ {x} (f {x}) (g {x}))


module _ (X : Set l1) where
  is-prop-is-prop : is-prop (is-prop X)
  is-prop-is-prop ϕ ϕ' =
    funext (λ x →
    funext (λ x' →
      prop-is-set ϕ (ϕ x x') (ϕ' x x')))


module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  open _≃_
  open EquivCoh
  
  pi-eqv-1 : {Z : Set l3} → (Y → Z) ≃ (X → Z)
  f pi-eqv-1 k x = k (f e x)
  g pi-eqv-1 k y = k (g e y)
  η pi-eqv-1 k = funext (λ y → ap k (ε' e y))
  h pi-eqv-1 = g pi-eqv-1
  ε pi-eqv-1 k = funext (λ x → ap k (η e x))

  neg-eqv = pi-eqv-1 {Z = ⊥ {l1 ⊔ l2}}

module _ {X : Set l1}
         {P : X → Set l2} {Q : X → Set l3}
         (ϕ : (x : X) → (P x) ≃ (Q x)) where
  open _≃_
  pi-eqv-2 : ((x : X) → P x) ≃ ((x : X) → Q x)
  f pi-eqv-2 f1 x1 = f (ϕ x1) (f1 x1) 
  g pi-eqv-2 f1 x1 = g (ϕ x1) (f1 x1)
  η pi-eqv-2 f1    = funext (λ x1 → η (ϕ x1) (f1 x1))
  h pi-eqv-2 f1 x1 = h (ϕ x1) (f1 x1)
  ε pi-eqv-2 f1    = funext (λ x1 → ε (ϕ x1) (f1 x1))
