{-# OPTIONS --without-K #-}
module Path where

open import Core

open _≃_


module _ {X : Set l1} {Y : Set l2} (f : X → Y) where
  ap : {x1 x2 : X} → x1 ≡ x2 → f x1 ≡ f x2
  ap refl = refl

module _ {X : Set l1} where
  infix 10 !
  ! : {x1 x2 : X} → x1 ≡ x2 → x2 ≡ x1
  ! refl = refl

  !-eqv : {x1 x2 : X} → (x1 ≡ x2) ≃ (x2 ≡ x1)
  f !-eqv = !
  g !-eqv = !
  η !-eqv refl = refl
  h !-eqv = g !-eqv
  ε !-eqv = η !-eqv

  !! : {x1 x2 : X} → {e : x1 ≡ x2} → ! (! e) ≡ e
  !! {e = e} = η !-eqv e

module _ {X : Set l1} (P : X → Set l2) where
  tpt-eqv : {x1 x2 : X} → (e : x1 ≡ x2) → P x1 ≃ P x2
  f (tpt-eqv refl) p = p 
  g (tpt-eqv e)    p = f (tpt-eqv (! e)) p
  η (tpt-eqv refl) p = refl
  h (tpt-eqv e)      = g (tpt-eqv e)
  ε (tpt-eqv refl) p = refl

  tpt : {x1 x2 : X} → (e : x1 ≡ x2) → P x1 → P x2
  tpt e = f (tpt-eqv e)

module _ {X Y : Set l1} where
  open _≃_

  postulate
    ua : X ≃ Y → X ≡ Y
    ua-tpt-eqv-id : (e1 : X ≡ Y) → ua (tpt-eqv (λ X → X) e1) ≡ e1
    tpt-eqv-id-ua : (e1 : X ≃ Y) → tpt-eqv (λ X → X) (ua e1) ≡ e1
    
  tpt-id-eqv : (X ≡ Y) ≃ (X ≃ Y)
  f tpt-id-eqv = tpt-eqv (λ X → X)
  g tpt-id-eqv = ua
  η tpt-id-eqv = ua-tpt-eqv-id
  h tpt-id-eqv = g tpt-id-eqv
  ε tpt-id-eqv = tpt-eqv-id-ua

  module _ (e1 : X ≃ Y) where
    tpt-id-ua : tpt (λ X → X) (ua e1) ≡ f e1
    tpt-id-ua = ap f (tpt-eqv-id-ua e1)
  
    tpt-id-!-ua : tpt (λ X → X) (! (ua e1)) ≡ g e1
    tpt-id-!-ua = ap g (tpt-eqv-id-ua e1)

module _ {X : Set l1} (P : X → Set l2) (f : (x : X) → P x) where
  apd : {x1 x2 : X} → (e : x1 ≡ x2) → tpt P e (f x1) ≡ f x2
  apd refl = refl

module _ {X : Set l1} where
  infixr 8 _◾_
  _◾_ : {x1 x2 : X} → x1 ≡ x2 → {x3 : X} → x2 ≡ x3 → x1 ≡ x3
  refl ◾ refl = refl

  ◾unitr : {x1 x2 : X} → {e : x1 ≡ x2} → e ◾ refl ≡ e
  ◾unitr {e = refl} = refl

  ◾unitl : {x1 x2 : X} → {e : x1 ≡ x2} → refl ◾ e ≡ e
  ◾unitl {e = refl} = refl

  ◾assoc : {w x x2 x3 : X} → {p : w ≡ x} → {q : x ≡ x2} → {r : x2 ≡ x3}
           → (p ◾ q) ◾ r ≡ p ◾ q ◾ r
  ◾assoc {p = refl} {refl} {refl} = refl

  ◾invl : {x1 x2 : X} → {e : x1 ≡ x2} → ! e ◾ e ≡ refl
  ◾invl {e = refl} = refl

  ◾invr : {x1 x2 : X} → {e : x1 ≡ x2} → e ◾ ! e ≡ refl
  ◾invr {e = refl} = refl

  !-comp : {x y z : X} → {p : x ≡ y} → {q : y ≡ z} → ! (p ◾ q) ≡ ! q ◾ ! p
  !-comp {p = refl} {refl} = refl

module _ {X : Set l1} {Y : Set l2} (Q : X → Y → Set l3) where
  tpt2-cart-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) →
                  {y1 y2 : Y} → (e2 : y1 ≡ y2) →
                  Q x1 y1 ≃ Q x2 y2
  f (tpt2-cart-eqv refl refl) q = q
  g (tpt2-cart-eqv e1 e2)       = f (tpt2-cart-eqv (! e1) (! e2))
  η (tpt2-cart-eqv refl refl) q = refl
  h (tpt2-cart-eqv e1 e2)       = g (tpt2-cart-eqv e1 e2)
  ε (tpt2-cart-eqv refl refl) q = refl

module _ {X : Set l1} {P : X → Set l2} (Q : (x : X) → P x → Set l3) where
  tpt2-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) →
             {p1 : P x1} → {p2 : P x2} → (e2 : tpt P e1 p1 ≡ p2) →
             Q x1 p1 ≃ Q x2 p2
  f (tpt2-eqv refl refl) q = q
  g (tpt2-eqv refl refl) q = q
  η (tpt2-eqv refl refl) q = refl
  h (tpt2-eqv e1 e2)     = g (tpt2-eqv e1 e2)
  ε (tpt2-eqv refl refl) q = refl

  tpt2 = λ {x1} {x2} e1 {p1} {p2} e2 → f (tpt2-eqv {x1} {x2} e1 {p1} {p2} e2)

module _ {X : Set l1} where
  lcomp-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (x2 ≡ x3) ≃ (x1 ≡ x3)
  f (lcomp-eqv e1) e2 = e1 ◾ e2
  g (lcomp-eqv e1) e2 = ! e1 ◾ e2
  η (lcomp-eqv refl) refl = refl
  h (lcomp-eqv e1)     = g (lcomp-eqv e1)
  ε (lcomp-eqv refl) refl = refl

  lcomp-τ : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (e2 : x2 ≡ x3) →
            ap (f (lcomp-eqv e1)) (η (lcomp-eqv e1) e2) ≡
            ε (lcomp-eqv e1) (f (lcomp-eqv e1) e2)
  lcomp-τ refl refl = refl

  lcomp-ν : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (e2 : x1 ≡ x3) →
            ap (g (lcomp-eqv e1)) (ε (lcomp-eqv e1) e2) ≡
            η (lcomp-eqv e1) (g (lcomp-eqv e1) e2)
  lcomp-ν refl refl = refl

  lwhisk-coh : {x1 x2 : X} → {e1 e2 : x1 ≡ x2} → (e4 : e1 ≡ e2) →
         ap (λ e2 → refl ◾ e2) e4 ≡
         f (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl)) e4
  lwhisk-coh {e1 = refl} refl = refl

  lwhisk-eqv : {x1 x2 : X} → {e1 : x1 ≡ x2} →
               {x3 : X} → {e2 e3 : x2 ≡ x3} →
               (e2 ≡ e3) ≃ (e1 ◾ e2 ≡ e1 ◾ e3)
  f (lwhisk-eqv {e1 = e1}) = ap (f (lcomp-eqv e1))
  g (lwhisk-eqv {e1 = refl}) =
    g (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl))
  η (lwhisk-eqv {e1 = refl}) e4 =
    ap (f (tpt2-cart-eqv _≡_ (! (! ◾unitl)) (! (! ◾unitl)))) (lwhisk-coh e4) ◾
    η (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl)) e4
  h lwhisk-eqv               = g (lwhisk-eqv)
  ε (lwhisk-eqv {e1 = refl}) e4 =
    lwhisk-coh (f (tpt2-cart-eqv _≡_ (! (! ◾unitl)) (! (! ◾unitl))) e4) ◾
    ε (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl)) e4

  lwhisk-τ : {x1 x2 : X} → {e1 : x1 ≡ x2} →
             {x3 : X} → {e2 e3 : x2 ≡ x3} →
             (e4 : e2 ≡ e3) →
             ap (f (lwhisk-eqv {e1 = e1})) (η (lwhisk-eqv {e1 = e1}) e4) ≡
             ε lwhisk-eqv (f lwhisk-eqv e4)
  lwhisk-τ {e1 = refl} {e2 = refl} refl = refl

  infixr 8 _[1,0,2]_
  _[1,0,2]_ : {x1 x2 x3 : X} →
              (e1 : x1 ≡ x2) →
              {e2 e3 : x2 ≡ x3} → e2 ≡ e3 →
              e1 ◾ e2 ≡ e1 ◾ e3
  _[1,0,2]_ e1 = f (lwhisk-eqv {e1 = e1})

  rcomp-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (x3 ≡ x1) ≃ (x3 ≡ x2)
  f (rcomp-eqv e1) e2 = e2 ◾ e1
  g (rcomp-eqv e1) e2 = e2 ◾ ! e1
  η (rcomp-eqv refl) refl = refl
  h (rcomp-eqv e1)      = g (rcomp-eqv e1)
  ε (rcomp-eqv refl) refl = refl

  rwhisk-coh : {x1 x2 : X} → {e1 e2 : x1 ≡ x2} → (e4 : e1 ≡ e2) →
               ap (λ e2 → e2 ◾ refl) e4 ≡
               f (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr)) e4
  rwhisk-coh {e1 = refl} refl = refl

  rwhisk-eqv : {x1 x2 : X} → {e1 : x1 ≡ x2} →
               {x3 : X} → {e2 e3 : x3 ≡ x1} →
               (e2 ≡ e3) ≃ (e2 ◾ e1 ≡ e3 ◾ e1)
  f (rwhisk-eqv {e1 = e1}) = ap (f (rcomp-eqv e1))  
  g (rwhisk-eqv {e1 = refl}) =
    g (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr))
  η (rwhisk-eqv {e1 = refl}) e4 =
    ap (f (tpt2-cart-eqv _≡_ (! (! ◾unitr)) (! (! ◾unitr)))) (rwhisk-coh e4) ◾
    η (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr)) e4
  h rwhisk-eqv               = g (rwhisk-eqv)
  ε (rwhisk-eqv {e1 = refl}) e4 =
    rwhisk-coh (f (tpt2-cart-eqv _≡_ (! (! ◾unitr)) (! (! ◾unitr))) e4) ◾
    ε (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr)) e4

  infixr 8 _[2,0,1]_
  _[2,0,1]_ : {x1 x2 x3 : X} →
              {e1 e2 : x1 ≡ x2} → e1 ≡ e2 →
              (e3 : x2 ≡ x3) →
              e1 ◾ e3 ≡ e2 ◾ e3
  _[2,0,1]_ e4 e3 = f (rwhisk-eqv {e1 = e3}) e4

  infixr 8 _[2,0,2]_
  _[2,0,2]_ : {x1 x2 x3 : X} →
              {e1 e2 : x1 ≡ x2} → e1 ≡ e2 →
              {e3 e4 : x2 ≡ x3} → e3 ≡ e4 →
              e1 ◾ e3 ≡ e2 ◾ e4
  _[2,0,2]_ e5 e6 = (e5 [2,0,1] _) ◾ (_ [1,0,2] e6)

module _ {X : Set l1} {Y : Set l2} {Z : Set l3}
         (g : Y → Z) (f : X → Y) where
  ap-fn-comp : {x x2 : X} → (p : x ≡ x2) → ap (λ x → g (f x)) p ≡ ap g (ap f p)
  ap-fn-comp {x} {x2} refl = refl

module _ {X : Set l1} where
  ap-id : {x y : X} → (p : x ≡ y) → ap (λ x → x) p ≡ p
  ap-id refl = refl

module _ {X : Set l1} {Y : Set l2} where
  ap-! : {x y : X} → (f : X → Y) → (p : x ≡ y) → ap f (! p) ≡ ! (ap f p)
  ap-! f refl = refl

module _ {X : Set l1} {Y : Set l2} {f : X → Y} where
  ap-comp : {x x2 x2' : X} → (p : x ≡ x2) → (q : x2 ≡ x2') →
            ap f (p ◾ q) ≡ ap f p ◾ ap f q
  ap-comp refl refl = refl

  ap-comp3 : {x1 x2 x3 x4 : X} →
             (e1 : x1 ≡ x2) → (e2 : x1 ≡ x3) → (e3 : x3 ≡ x4) →
             ap f (! e1 ◾ e2 ◾ e3) ≡ ! (ap f e1) ◾ ap f e2 ◾ ap f e3
  ap-comp3 refl refl refl = refl

module _ {X : Set l1} {Y : Set l2} where
  tpt-const : {x1 x2 : X} → (e : x1 ≡ x2) →
              (y : Y) → tpt (λ _ → Y) e y ≡ y
  tpt-const refl y = refl

module _ {X : Set l1} {Y : Set l2} (f : X → Y) where
  tpt-fn-eq-const : (y : Y) →
                    {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : f x1 ≡ y) →
                    tpt (λ x → f x ≡ y) e1 e2 ≡ ! (ap f e1) ◾ e2
  tpt-fn-eq-const _ refl refl = refl

  tpt-const-eq-fn : (y : Y) →
                    {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : y ≡ f x1) →
                    tpt (λ x → y ≡ f x) e1 e2 ≡ e2 ◾ ap f e1
  tpt-const-eq-fn y refl refl = refl

module _ {X : Set l1} {Y : Set l2} (f g : X → Y) where
  tpt-fn-eq-fn : {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : f x1 ≡ g x1) →
                 tpt (λ x → f x ≡ g x) e1 e2 ≡ ! (ap f e1) ◾ e2 ◾ ap g e1
  tpt-fn-eq-fn refl e2 = ! ◾unitr ◾ ! ◾unitl

module _ {X : Set l1} {x0 : X} where
  tpt-const-eq-var : {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : x0 ≡ x1) →
                     tpt (λ x → x0 ≡ x) e1 e2 ≡ e2 ◾ e1
  tpt-const-eq-var refl refl = refl

  tpt-var-eq-const : {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : x1 ≡ x0) →
                     tpt (λ x → x ≡ x0) e1 e2 ≡ ! e1 ◾ e2
  tpt-var-eq-const refl refl = refl

module _ {X : Set l1} {P : X → Set l2} {Q : X → Set l3} where
  tpt-fn : {x1 x2 : X} → (e : x1 ≡ x2) →
           (f : P x1 → Q x1) → (p : P x2) →
           tpt (λ x → P x → Q x) e f p ≡ tpt Q e (f (tpt P (! e) p))
  tpt-fn refl f p = refl

module _ {X : Set l1} (P : X → Set l2) where
  tpt-comp : {x1 x2 x3 : X} → (e1 : x1 ≡ x2) → (e2 : x2 ≡ x3) →
             {p : P x1} → tpt P (e1 ◾ e2) p ≡ tpt P e2 (tpt P e1 p)
  tpt-comp refl refl = refl

module _ {X : Set l1} {Y : Set l2} {f : X → Y} (P : Y → Set l3) where
  tpt-fn-comp : {x1 x2 : X} → (e : x1 ≡ x2) →
                (p : P (f x1)) → tpt (λ x → P (f x)) e p ≡ tpt P (ap f e) p
  tpt-fn-comp refl p = refl


module _ where
  is-prop : Set l1 → Set l1
  is-prop X = (x x2 : X) → x ≡ x2

  is-set : Set l1 → Set l1
  is-set X = {x x2 : X} → (p q : x ≡ x2) → p ≡ q

module _ where
  prop-is-set : {X : Set l1} → is-prop X → is-set X
  prop-is-set ϕ {x1} {x2} e1 e2 =
    g lwhisk-eqv
      (! (tpt-const-eq-var e1 (ϕ x1 x1)) ◾
       apd _ (ϕ x1) e1 ◾
       ! (apd _ (ϕ x1) e2)
       ◾ tpt-const-eq-var e2 (ϕ x1 x1))

module _ {X : Set l1} (ϕ : is-set X) (P : X → Set l2) where
  tpt-loop : {x : X} → (e : x ≡ x) → (p : P x) → tpt P e p ≡ p
  tpt-loop e p = tpt (λ e → tpt P e p ≡ p) (ϕ refl e) refl

module _ {X : Set l1} (ϕ : is-set X)
         {P : X → Set l2} (ψ : (x : X) → is-set (P x))
         (Q : (x : X) → P x → Set l3) where
  tpt2-loop : {x : X} → (e1 : x ≡ x) →
              {p : P x} → (e2 : tpt P e1 p ≡ p) →
              (q : Q x p) → tpt2 Q e1 e2 q ≡ q
  tpt2-loop {x} e1 {p} e2 q =
    tpt2 (λ e1 e2 → tpt2 Q e1 e2 q ≡ q)
         (ϕ refl e1)
         (ψ x (tpt (λ e → tpt P e p ≡ p) (ϕ refl e1) refl) e2)
         refl

  tpt2-loop-β : {x : X} → {p : P x} → {q : Q x p} →
                tpt2-loop refl refl q ≡ refl
  tpt2-loop-β {x} {p} {q} =
    tpt2 (λ e3 e4 → tpt2 (λ e1 e2 → tpt2 Q e1 e2 q ≡ q) e3 e4 refl ≡ refl)
         (prop-is-set ϕ refl (ϕ refl refl))
         (prop-is-set (ψ x)
           (tpt (λ e → tpt (λ e → tpt P e p ≡ p) e refl ≡ refl)
                (prop-is-set ϕ refl (ϕ refl refl)) refl)
           _)
         refl


module _ {X : Set l1} {Y : Set l2}
         {f : X → Y} {g : Y → X}
         (η : (x : X) → g (f x) ≡ x)
         where
  inv-sq : {x1 x2 : X} → (e1 : x1 ≡ x2) →
           ! (η x1) ◾ ap g (ap f e1) ◾ η x2 ≡ e1
  inv-sq {x1} = coh2
    module inv-sq where
    coh1 : {x1 x2 : X} → (e : x1 ≡ x2) → ! e ◾ refl ◾ e ≡ refl
    coh1 refl = refl

    coh2 = λ { refl → coh1 (η _) }

  inv-comm : (x : X) → ap g (ap f (η x)) ≡ η (g (f x))
  inv-comm x1 = _≃_.g rwhisk-eqv (coh (η x1))
    module inv-comm where
    coh : {x1 x2 : X} → (e1 : x1 ≡ x2) → ap g (ap f e1) ◾ η x2 ≡ η x1 ◾ e1
    coh refl = ◾unitl ◾ ! ◾unitr

module _ {X : Set l1} {Y : Set l2}
         (f : X → Y) (g : Y → X)
         (η : (x : X) → g (f x) ≡ x)
         where
  ap-sect-eq : {x1 x2 : X} → {e1 e2 : x1 ≡ x2} →
               ap f e1 ≡ ap f e2 → e1 ≡ e2
  ap-sect-eq {x1} {x2} {e1} {e2} α =
    ! (inv-sq η e1) ◾
    (! (η x1) [1,0,2] ap (ap g) α [2,0,1] (η x2)) ◾
    inv-sq η e2

module _ {X : Set l1} {Y : Set l2}
         (f : X → Y) (g : Y → X)
         (ε : (y : Y) → f (g y) ≡ y)
         where
  ap-retr-eq : {y1 y2 : Y} → {e1 e2 : y1 ≡ y2} →
               ap g e1 ≡ ap g e2 → e1 ≡ e2
  ap-retr-eq {y1} {y2} {e1} {e2} α =
    ! (inv-sq ε e1) ◾
    (! (ε y1) [1,0,2] ap (ap f) α [2,0,1] (ε y2)) ◾
    inv-sq ε e2

module _ {X : Set l1} {Y : Set l2}
         (f : X → Y) (g : Y → X)
         (η : (x : X) → g (f x) ≡ x)
         (ε : (y : Y) → f (g y) ≡ y)
         where
  ap-qinv-sq : {x1 x2 : X} → (e1 : f x1 ≡ f x2) →
               ap f (! (η x1) ◾ ap g e1 ◾ η x2) ≡ e1
  ap-qinv-sq {x1} {x2} e1 = ap-retr-eq f g ε (coh e1)
    module ap-qinv-sq where
    coh : {x1 x2 : X} → (e1 : f x1 ≡ f x2) →
            ap g (ap f (! (η x1) ◾ ap g e1 ◾ η x2)) ≡ ap g e1
    coh {x1} {x2} e1 =
      ap (ap g) (ap-comp3 (η x1) (ap g e1) (η x2)) ◾
      ap-comp3 (ap f (η x1)) (ap f (ap g e1)) (ap f (η x2)) ◾
      (ap ! (inv-comm η x1) [2,0,2] ap g (ap f (ap g e1)) [1,0,2] inv-comm η x2) ◾
      inv-sq η (ap g e1)

module EquivCoh {X : Set l1} {Y : Set l2} where
  ε' : (e : X ≃ Y) → (y : Y) → f e (g e y) ≡ y
  ε' e y = ! (ap (λ y → f e (g e y)) (ε e y)) ◾ ap (f e) (η e (h e y)) ◾ ε e y

  η' : (e : X ≃ Y) → (x : X) → h e (f e x) ≡ x
  η' e x = ! (η e (h e (f e x))) ◾ ap (g e) (ε e (f e x)) ◾ η e x

  τ : (e : X ≃ Y) → (x : X) → ap (f e) (η' e x) ≡ ε e (f e x)
  τ e x = ap-qinv-sq (f e) (g e) (η e) (ε' e) (ε e (f e x))

  ν : (e : X ≃ Y) → (y : Y) → ap (h e) (ε e y) ≡ η' e (h e y)
  ν e y = ap-sect-eq _ (g e) (η e) (inv-comm (ε e) y ◾ ! (τ e (h e y)))
