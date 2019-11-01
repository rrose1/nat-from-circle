{-# OPTIONS --without-K #-}
module Equivalence where

open import Core
open import Path
open import Function
open import Sigma


module _ (X : Set l1) where
  open _≃_
  ide : X ≃ X
  f ide x = x
  g ide x = x
  η ide x = refl
  h ide = g ide
  ε ide x = refl

module _ {X : Set l1} {Y : Set l2} {Z : Set l3}
         (e1 : Y ≃ Z) (e2 : X ≃ Y)
         where
  open _≃_
  infixr 5 _∘e_
  _∘e_ : X ≃ Z
  f _∘e_ x = f e1 (f e2 x)
  g _∘e_ z = g e2 (g e1 z)
  η _∘e_ x = ap (g e2) (η e1 (f e2 x)) ◾ η e2 x
  h _∘e_ z = h e2 (h e1 z)
  ε _∘e_ z = ap (f e1) (ε e2 (h e1 z)) ◾ ε e1 z

module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  open _≃_
  open EquivCoh
  
  !e : Y ≃ X
  f !e = g e
  g !e = f e
  η !e = ε' e
  h !e = f e
  ε !e = η e


module _ {X : Set l1} {Y : Set l2} (e1 : X ≃ Y) where
  open _≃_
  open EquivCoh
  
  eqv-embed : {x1 x2 : X} → (x1 ≡ x2) ≃ (f e1 x1 ≡ f e1 x2)
  f eqv-embed                = ap (f e1)
  g (eqv-embed {x1} {x2}) e3 = ! (η e1 x1) ◾ ap (g e1) e3 ◾ η e1 x2
  η eqv-embed                = inv-sq (η e1)
  h eqv-embed                = g eqv-embed
  ε eqv-embed                = ap-qinv-sq (f e1) (g e1) (η e1) (ε' e1)

module _ {X : Set l1} {Y : Set l2} (e1 : X ≃ Y) where
  open _≃_
  open EquivCoh
  
  eqv-adj : {x1 : X} → {y1 : Y} → (f e1 x1 ≡ y1) ≃ (x1 ≡ h e1 y1)
  f (eqv-adj {x1}) e3       = ! (η' e1 x1) ◾ ap (h e1) e3
  g (eqv-adj {_} {y1}) e3   = ap (f e1) e3 ◾ ε e1 y1
  η (eqv-adj {x1}) refl     = coh _ (τ e1 x1)
    module η-eqv-adj where
    coh : {x1 x2 : X} → (e3 : x1 ≡ x2) →
          {e4 : f e1 x1 ≡ f e1 x2} → (α1 : ap (f e1) e3 ≡ e4) →
          ap (f e1) (! e3 ◾ refl) ◾ e4 ≡ refl
    coh refl refl = refl
  h eqv-adj                 = g eqv-adj
  ε (eqv-adj {_} {y1}) refl = coh _ (ν e1 y1)
    module ε-eqv-adj where
    coh : {y1 y2 : Y} → (e3 : y1 ≡ y2) →
          {e4 : h e1 y1 ≡ h e1 y2} → (α1 : ap (h e1) e3 ≡ e4) →
          ! e4 ◾ ap (h e1) (refl ◾ e3) ≡ refl
    coh refl refl = refl

module _ {X : Set l1} {P : X → Set l2}
         {Y : Set l3} {Q : Y → Set l4}
         (e : X ≃ Y)
         (ϕ : (x : X) → (P x) ≃ (Q (_≃_.f e x)))
         where
  sigma-eqv : (Σ X P) ≃ (Σ Y Q)
  sigma-eqv = sigma-eqv-1 e ∘e sigma-eqv-2 ϕ

module _ {X : Set l1} {P Q : X → Set l2} where
  fam-eqv : (P ≡ Q) ≃ ((x : X) → (P x) ≃ (Q x))
  fam-eqv = pi-eqv-2 (λ _ → tpt-id-eqv) ∘e happly-eqv

module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  open _≃_
  is-prop-eqv : (is-prop X) ≃ (is-prop Y)
  f is-prop-eqv ϕ y1 y2 = g (eqv-embed (!e e)) (ϕ (g e y1) (g e y2))
  g is-prop-eqv ϕ x1 x2 = g (eqv-embed e) (ϕ (f e x1) (f e x2))
  η is-prop-eqv ϕ = is-prop-is-prop X (g is-prop-eqv (f is-prop-eqv ϕ)) ϕ
  h is-prop-eqv = g is-prop-eqv
  ε is-prop-eqv ϕ = is-prop-is-prop Y (f is-prop-eqv (h is-prop-eqv ϕ)) ϕ
  
  is-contr-eqv : (is-contr X) ≃ (is-contr Y)
  f is-contr-eqv (x , ϕ) =
    f e x , (λ y → ! (g (eqv-adj e) (! (ϕ (h e y)))))
  g is-contr-eqv (y , ϕ) =
    g e y , (λ x → ! (g (eqv-adj (!e e)) (! (ϕ (h (!e e) x)))))
  η is-contr-eqv (x , ϕ) = snd (is-contr-is-contr (x , ϕ)) (_ , _)
  h is-contr-eqv = g is-contr-eqv
  ε is-contr-eqv (y , ϕ) = snd (is-contr-is-contr (y , ϕ)) (_ , _)

-----------

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} where
  open _≃_
  flip-eqv : (X → Y → Z) ≃ (Y → X → Z)
  f flip-eqv k y x = k x y
  g flip-eqv k x y = k y x
  η flip-eqv k = refl
  h flip-eqv = g flip-eqv
  ε flip-eqv k = refl

  flip : (X → Y → Z) → (Y → X → Z)
  flip = f flip-eqv

module _ {X : Set l1} {Y : Set l2}
         (f : X → Y) (g : Y → X)
         (η : (x : X) → g (f x) ≡ x)
         (ε : (y : Y) → f (g y) ≡ y)
         where
  qinv-is-cfn : (y : Y) → is-contr (Σ X (λ x → f x ≡ y))
  fst (qinv-is-cfn y) = g y , ε y
  snd (qinv-is-cfn y) (x , e) =
    pair-eq (! (η x) ◾ ! (ap g (ε (f x))) ◾ ap g (ap f (η x)) ◾ ap g e ,
             coh1 (η x) (ap g (ε (f x))) (ap g (ap f (η x))) (ap g e) e ◾
             coh2 e (η x))
    module qinv-is-cfn where
    coh1 : {x1 x2 x3 x4 x5 : X} → {y1 : Y} →
           (p1 : x1 ≡ x2) → (p2 : x3 ≡ x1) → (p3 : x3 ≡ x4) →
           (p4 : x4 ≡ x5) → (p5 : f x2 ≡ y1) →
           tpt (λ x → f x ≡ y1) (! p1 ◾ ! p2 ◾ p3 ◾ p4) p5 ≡
           ! (ap f p4) ◾ ! (ap f p3) ◾ ap f p2 ◾ ap f p1 ◾ p5
    coh1 refl refl refl refl refl = refl

    coh2 : {x1 x2 : X} → {y1 : Y} →
           (e1 : f x2 ≡ y1) →
           (e2 : g (f x1) ≡ x2) →
           ! (ap f (ap g e1)) ◾
           ! (ap f (ap g (ap f e2))) ◾
           ap f (ap g (ε (f x1))) ◾
           ap f e2 ◾
           e1 ≡ ε y1
    coh2 {x1} refl refl = ◾unitl ◾ ◾unitl ◾ ◾unitr ◾ inv-comm ε (f x1) 


module _ {W : Set l1} {X : Set l2} {Y : Set l3} where
  open _≃_
  qinv-is-cfn-2 : (k1 : W → X → Y) → (k2 : W → Y) →
                  (k3 : (W → Y) → X) →
                  (ϕ1 : (x : X) → k3 (λ w → k1 w x) ≡ x) →
                  (ϕ2 : (k2 : W → Y) → (λ w → k1 w (k3 k2)) ≡ k2) →
                  is-contr (Σ X (λ x → (w : W) → k1 w x ≡ k2 w))
  qinv-is-cfn-2 k1 k2 k3 ϕ1 ϕ2 =
    f (is-contr-eqv (sigma-eqv-2 (λ _ → happly-eqv)))
      (qinv-is-cfn (flip k1) k3 ϕ1 ϕ2 k2)


module _ {X : Set l1} {Y : Set l2} where
  open _≃_
  open EquivCoh
  
  biinv-eq : {e1 e2 : X ≃ Y} → f e1 ≡ f e2 → e1 ≡ e2
  biinv-eq {e1@(biinv _ g1 η1 h1 ε1)} {biinv f2 g2 η2 h2 ε2} refl =
    ap (λ w → biinv f2 (fst w) (snd w) h1 ε1)
      (contr-is-prop
        (qinv-is-cfn-2
          (λ x g → g (f2 x)) id (λ k y → k (h1 y))
          (λ g3 → funext (λ y → ap g3 (ε1 y)))
          (λ k → funext (λ x → ap k (η' e1 x)))) _ _) ◾
    ap (λ w → biinv f2 g2 η2 (fst w) (snd w))
      (contr-is-prop
        (qinv-is-cfn-2
          (λ y h → f2 (h y)) id (λ k y → g1 (k y))
          (λ g3 → funext (λ y → η1 (g3 y)))
          (λ k → funext (λ y → ε' e1 (k y)))) _ _)
      
----------

module _ {X : Set l1} {Y : Set l1} (ψ : is-prop Y) where
  open _≃_
  hprop-is-set : (e1 e2 : X ≡ Y) → e1 ≡ e2
  hprop-is-set e1 e2 =
    g (eqv-embed tpt-id-eqv) (biinv-eq (is-prop-pi (λ _ → ψ) _ _))

module _ {X : Set l1} {Y : Set l2} where
  open _≃_
  !e-eqv : (X ≃ Y) ≃ (Y ≃ X)
  f !e-eqv = !e
  g !e-eqv = !e
  η !e-eqv e = biinv-eq refl
  h !e-eqv = g !e-eqv
  ε !e-eqv e = biinv-eq refl

module _ {W : Set l1} {X : Set l2} {Y : Set l3} {Z : Set l4}
         (e1 : Y ≃ Z) (e2 : X ≃ Y) (e3 : W ≃ X) where
  open _≃_
  ∘e-assoc : (e1 ∘e e2) ∘e e3 ≡ e1 ∘e e2 ∘e e3
  ∘e-assoc = biinv-eq refl

module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  open _≃_
  open EquivCoh
  
  ∘e-unitl : ide Y ∘e e ≡ e
  ∘e-unitl = biinv-eq refl

  ∘e-unitr : e ∘e ide X ≡ e
  ∘e-unitr = biinv-eq refl

  ∘e-invl : !e e ∘e e ≡ ide X
  ∘e-invl = biinv-eq (funext (η e))
  
  ∘e-invr : e ∘e !e e ≡ ide Y
  ∘e-invr = biinv-eq (funext (ε' e))


module _ {X : Set l1} {Y : Set l2} {Z : Set l3} (e1 : X ≃ Y) where
  open _≃_ 
  ∘e-precomp-eqv : (Y ≃ Z) ≃ (X ≃ Z)
  f ∘e-precomp-eqv e2 = e2 ∘e e1
  g ∘e-precomp-eqv e2 = e2 ∘e !e e1
  η ∘e-precomp-eqv e2 =
    ∘e-assoc e2 e1 (!e e1) ◾
    ap (λ e → e2 ∘e e) (∘e-invr e1) ◾
    ∘e-unitr e2 
  h ∘e-precomp-eqv = g ∘e-precomp-eqv
  ε ∘e-precomp-eqv e2 =
    ∘e-assoc e2 (!e e1) e1 ◾
    ap (λ e → e2 ∘e e) (∘e-invl e1) ◾
    ∘e-unitr e2 

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} (e1 : Y ≃ Z) where
  open _≃_ 
  ∘e-postcomp-eqv : (X ≃ Y) ≃ (X ≃ Z)
  f ∘e-postcomp-eqv e2 = e1 ∘e e2
  g ∘e-postcomp-eqv e2 = !e e1 ∘e e2
  η ∘e-postcomp-eqv e2 =
    ! (∘e-assoc (!e e1) e1 e2) ◾
    ap (λ e → e ∘e e2) (∘e-invl e1) ◾
    ∘e-unitl e2
  h ∘e-postcomp-eqv = g ∘e-postcomp-eqv
  ε ∘e-postcomp-eqv e2 =
    ! (∘e-assoc e1 (!e e1) e2) ◾
    ap (λ e → e ∘e e2) (∘e-invr e1) ◾
    ∘e-unitl e2

module _ {W : Set l1} {X : Set l2} {Y : Set l3} {Z : Set l4}
         (e1 : W ≃ X) (e2 : Y ≃ Z)
         where
  open _≃_ 
  ∘e-bicomp-eqv : (X ≃ Y) ≃ (W ≃ Z)
  ∘e-bicomp-eqv = ∘e-postcomp-eqv e2 ∘e ∘e-precomp-eqv e1


  -- tpt-fp-eqv' : {x1 x2 x3 : X} → (P : x1 ≡ x2 → Set l2) →
  --               (e1 : x2 ≡ x3) → (e2 : x1 ≡ x3) →
  --               _≃_ (tpt (λ a → x1 ≡ a → Set l2) e1 P e2) (P (e2 ◾ ! e1))
  -- tpt-fp-eqv' {x1} P refl refl = ide _

module _ {X : Set l1} {P : X → Set l2} (ϕ : (x : X) → is-prop (P x))
         {Y : Set l3} {Q : Y → Set l4} (ψ : (y : Y) → is-prop (Q y))
         where
  record SubEqv : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4) where
    constructor subeqv
    field
      f : Σ X P → Σ Y Q
      g : Σ Y Q → Σ X P
      η : (p : Σ X P) → fst (g (f p)) ≡ fst p
      h : Σ Y Q → Σ X P
      ε : (q : Σ Y Q) → fst (f (h q)) ≡ fst q

    ε' : (q : Σ Y Q) → fst (f (g q)) ≡ fst q
    ε' q =
      ! (ap (λ q → fst (f (g q))) (pair-prop-eq ψ (ε q))) ◾
       ap (λ p → fst (f p)) (pair-prop-eq ϕ (η (h q))) ◾
      ε q

    η^ : (x : X) → (p : P x) → (q : Q (fst (f (x , p)))) →
         fst (g (fst (f (x , p)) , q)) ≡ x
    η^ x p q = ap (λ q → fst (g (_ , q))) (ψ _ _ _) ◾ η (x , p)

    ε^ : (y : Y) → (q : Q y) → (p : P (fst (h (y , q)))) →
         fst (f (fst (h (y , q)) , p)) ≡ y
    ε^ y q p = ap (λ p → fst (f (_ , p))) (ϕ _ _ _) ◾ ε (y , q)

    ε'^ : (y : Y) → (q : Q y) → (p : P (fst (g (y , q)))) →
          fst (f (fst (g (y , q)) , p)) ≡ y
    ε'^ y q p = ap (λ p → fst (f (_ , p))) (ϕ _ _ _) ◾ ε' (y , q)


module _ {X : Set l1} {P : X → Set l2} {ϕ : (x : X) → is-prop (P x)}
         {Y : Set l3} {Q : Y → Set l4} {ψ : (y : Y) → is-prop (Q y)}
         where
  open _≃_
  open SubEqv
  subeqv-eqv : ((Σ X P) ≃ (Σ Y Q)) ≃ (SubEqv ϕ ψ)
  f (f subeqv-eqv e) = f e
  g (f subeqv-eqv e) = g e
  η (f subeqv-eqv e) p = g (pair-prop-eqv ϕ) (η e p)
  h (f subeqv-eqv e) = h e
  ε (f subeqv-eqv e) p = g (pair-prop-eqv ψ) (ε e p)
  
  f (g subeqv-eqv e) = f e
  g (g subeqv-eqv e) = g e
  η (g subeqv-eqv e) p = f (pair-prop-eqv ϕ) (η e p)
  h (g subeqv-eqv e) = h e
  ε (g subeqv-eqv e) q = f (pair-prop-eqv ψ) (ε e q)
  
  η subeqv-eqv (biinv f1 g1 η1 h1 ε1) =
    ap (λ η → biinv f1 g1 η h1 _) (funext (λ p → ε (pair-prop-eqv ϕ) (η1 p))) ◾
    ap (biinv f1 g1 η1 h1) (funext (λ q → ε (pair-prop-eqv ψ) (ε1 q))) 
  
  h subeqv-eqv = g subeqv-eqv
  
  ε subeqv-eqv (subeqv f1 g1 η1 h1 ε1) =
    ap (subeqv f1 g1 _ h1) (funext (λ q → η (pair-prop-eqv ψ) (ε1 q))) ◾
    ap (λ η → subeqv f1 g1 η h1 ε1)
       (funext (λ q → η (pair-prop-eqv ϕ) (η1 q))) 

  subeqv-eq : {f1 f2 : Σ X P → Σ Y Q} →
              (e1 : (p : Σ X P) → fst (f1 p) ≡ fst (f2 p)) →
              {g1 g2 : Σ Y Q → Σ X P} →
              {η1 : (x : Σ X P) → fst (g1 (f1 x)) ≡ fst x} →
              {η2 : (x : Σ X P) → fst (g2 (f2 x)) ≡ fst x} →
              {h1 h2 : Σ Y Q → Σ X P} →
              {ε1 : (y : Σ Y Q) → fst (f1 (h1 y)) ≡ fst y} →
              {ε2 : (y : Σ Y Q) → fst (f2 (h2 y)) ≡ fst y} →
              subeqv f1 g1 η1 h1 ε1 ≡ subeqv f2 g2 η2 h2 ε2
  subeqv-eq e1 =
    ! (ε subeqv-eqv _) ◾
    f (eqv-embed subeqv-eqv)
      (biinv-eq (funext (λ p → pair-prop-eq ψ (e1 p)))) ◾
    ε subeqv-eqv _
    
module _ {X : Set l1} {P : X → Set l2} {ϕ : (x : X) → is-prop (P x)}
         {Y : Set l3} {Q : Y → Set l4} {χ : (y : Y) → is-prop (Q y)}
         {Z : Set l5} {R : Z → Set l6} {ψ : (z : Z) → is-prop (R z)}
         (e1 : SubEqv χ ψ) (e2 : SubEqv ϕ χ) where
  open SubEqv
  infixr 5 _∘s_
  _∘s_ : SubEqv ϕ ψ
  f _∘s_ p = f e1 (f e2 p)
  g _∘s_ r = g e2 (g e1 r)
  η _∘s_ p = ap (λ q → fst (g e2 q)) (pair-prop-eq χ (η e1 (f e2 p))) ◾ η e2 p
  h _∘s_ r = h e2 (h e1 r)
  ε _∘s_ r = ap (λ q → fst (f e1 q)) (pair-prop-eq χ (ε e2 (h e1 r))) ◾ ε e1 r

module _ {X : Set l1} {P : X → Set l2} (ϕ : (x : X) → is-prop (P x)) where
  open SubEqv
  ids : SubEqv ϕ ϕ
  f ids x = x
  g ids x = x
  η ids x = refl
  h ids x = x
  ε ids x = refl

module _ {X : Set l1} {P : X → Set l2} {ϕ : (x : X) → is-prop (P x)}
         {Y : Set l3} {Q : Y → Set l4} {χ : (y : Y) → is-prop (Q y)}
         (e : SubEqv ϕ χ) where
  open SubEqv
  !s : SubEqv χ ϕ
  f !s = g e
  g !s = f e
  η !s = ε' e
  h !s = f e
  ε !s = η e
