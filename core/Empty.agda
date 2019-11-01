{-# OPTIONS --without-K #-}
module Empty where

open import Core


module _ {Y : Set l2} where
  rec⊥ : ⊥ {l1} → Y
  rec⊥ ()

module _ (X : Set l1) where
  has-dne : Set l1
  has-dne = ((X → ⊥ {l1}) → ⊥ {l1}) → X

module _ {X Y : Set l1} where
  nn-map : (X → Y) → ((X → ⊥ {l1}) → ⊥ {l1}) → ((Y → ⊥ {l1}) → ⊥ {l1})
  nn-map f X n = X (λ x → n (f x))


module _ {X : Set l1} where
  infix 4 _≢_
  _≢_ : X → X → Set l1
  x ≢ x' = x ≡ x' → ⊥ {l1}

  infix 4 _≐_
  _≐_ : X → X → Set l1
  _≐_ x1 x2 = (x1 ≢ x2) → ⊥ {l1}
