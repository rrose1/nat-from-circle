{-# OPTIONS --without-K #-}
module Sigma where

open import Core
open import Path
open import Function

open _≃_


module _ {X : Set l1} {P : X → Set l2} where
  ap-snd : {x1 x2 : X} → {p1 : P x1} → {p2 : P x2} →
           (e : _≡_ {X = Σ X P} (x1 , p1) (x2 , p2)) →
           tpt P (ap fst e) p1 ≡ p2
  ap-snd refl = refl

  fst-tpt-sigma : {Q : (x : X) → (p : P x) → Set} →
                  {x1 x2 : X} → (e : x1 ≡ x2) →
                  (p1 : P x1) → {q1 : Q x1 p1} →
                  fst (tpt (λ x → Σ (P x) (Q x)) e (p1 , q1)) ≡ tpt P e p1
  fst-tpt-sigma refl p = refl


module _ {X : Set l1} {P : X → Set l2} where
  pair-eqv : {x1 x2 : X} → {p1 : P x1} → {p2 : P x2} →
             (Σ (x1 ≡ x2) (λ p → tpt P p p1 ≡ p2)) ≃
             ((x1 , p1) ≡ (x2 , p2))
  f pair-eqv (refl , refl)  = refl
  g pair-eqv e1             = ap fst e1 , ap-snd e1
  η pair-eqv (refl , refl)  = refl
  h pair-eqv                = g pair-eqv
  ε pair-eqv refl           = refl

  pair-eq = λ {x1} {x2} {p1} {p2} → f (pair-eqv {x1} {x2} {p1} {p2})

module _ {X : Set l1} {Y : Set l2} where
  cart-pair-eqv : {x1 x2 : X} → {y1 y2 : Y} →
                  ((x1 ≡ x2) × (y1 ≡ y2)) ≃ ((x1 , y1) ≡ (x2 , y2))
  f cart-pair-eqv (refl , refl)  = refl
  g cart-pair-eqv             e1 = ap fst e1 , ap snd e1
  η cart-pair-eqv (refl , refl)  = refl
  h cart-pair-eqv                = g cart-pair-eqv
  ε cart-pair-eqv refl           = refl

  cart-pair-eq = λ {x1} {x2} {y1} {y2} → f (cart-pair-eqv {x1} {x2} {y1} {y2})

module _ {X : Set l1} {P : X → Set l2} (ϕ : (x : X) → is-prop (P x)) where
  pair-prop-eqv : {x1 x2 : X} → {p1 : P x1} → {p2 : P x2} →
                  (x1 ≡ x2) ≃ ((x1 , p1) ≡ (x2 , p2))
  f (pair-prop-eqv {p1 = p1} {p2}) refl         = pair-eq (refl , ϕ _ p1 p2)
  g pair-prop-eqv                               = ap fst
  η (pair-prop-eqv {x2 = x2} {p1} {p2}) refl    =
    ap fst (η pair-eqv (refl , ϕ x2 p1 p2))
  h pair-prop-eqv                               = g pair-prop-eqv
  ε (pair-prop-eqv {x1} {x2} {p1} {p2}) refl    =
    ap (λ e → pair-eq (refl , e)) (prop-is-set (ϕ x2) (ϕ x1 p1 p1) refl)

  pair-prop-eq = λ {x1} {x2} {p1} {p2} → f (pair-prop-eqv {x1} {x2} {p1} {p2})

module _ {X : Set l1} {Y : Set l2} {P : Y → Set l3} (e : X ≃ Y) where
  open EquivCoh
  sigma-eqv-1 : (Σ X (λ x → P (f e x))) ≃ (Σ Y P)
  f sigma-eqv-1 (x , p) = f e x , p
  g sigma-eqv-1 (y , p) = h e y , g (tpt-eqv P (ε e y)) p
  η sigma-eqv-1 (x , p) =
    pair-eq
      (η' e x ,
       tpt-fn-comp P (η' e x) (g (tpt-eqv P (ε e (f e x))) p) ◾
       ! (tpt-comp P (! (ε e (f e x))) (ap (f e) (η' e x)) {p}) ◾
       ap (λ e → tpt P e p)
          ((! (ε e (f e x)) [1,0,2] τ e x) ◾ ◾invl))
  h sigma-eqv-1 (y , p) = h e y , g (tpt-eqv P (ε e y)) p
  ε sigma-eqv-1 (y , p) = pair-eq (ε e y , ε (tpt-eqv P (ε e y)) p)

module _ {X : Set l1}
         {P : X → Set l2} {Q : X → Set l3}
         (ϕ : (x : X) → P x ≃ Q x)
         where
  sigma-eqv-2 : (Σ X P) ≃ (Σ X Q)
  f sigma-eqv-2 (x , p) = x , f (ϕ x) p
  g sigma-eqv-2 (x , q) = x , g (ϕ x) q
  η sigma-eqv-2 (x , p) = pair-eq (refl , η (ϕ x) p)
  h sigma-eqv-2 (x , q) = x , h (ϕ x) q
  ε sigma-eqv-2 (x , q) = pair-eq (refl , ε (ϕ x) q)


module _ where
  is-contr : Set l1 → Set l1
  is-contr X = Σ X (λ x0 → (x : X) → x ≡ x0)

module _ {X : Set l1} where
  contr-is-prop : is-contr X → is-prop X
  contr-is-prop (x , ϕ) x1 x2 = ϕ x1 ◾ ! (ϕ x2)

module _ {X : Set l1} where
  is-contr-is-contr : is-contr X → is-contr (is-contr X)
  is-contr-is-contr (x0 , ϕ0) =
    (x0 , ϕ0) ,
    (λ {(x1 , ϕ1) →
        pair-eq
        (ϕ0 x1 ,
         funext (λ x2 →
           prop-is-set
             (contr-is-prop (x0 , ϕ0))
             (tpt (λ x3 → (x : X) → x ≡ x3) (ϕ0 x1) ϕ1 x2) (ϕ0 x2))) })

module _ {X : Set l1} (x0 : X) where 
  var-eq-const-is-prop : (w1 w2 : Σ X (λ x → x ≡ x0)) → w1 ≡ w2
  var-eq-const-is-prop (_ , refl) (_ , refl) = refl

  const-eq-var-is-prop : (w1 w2 : Σ X (λ x → x0 ≡ x)) → w1 ≡ w2
  const-eq-var-is-prop (_ , refl) (_ , refl) = refl
