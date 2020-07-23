{-# OPTIONS --without-K --rewriting #-}
module ZModel where

open import UTT


module Integers where

  {-# BUILTIN REWRITE _≡_ #-}

  postulate
    Z : Set
    zero : Z
    e : Z ≃ Z

  module _ {P : Z → Set l1} (z* : P zero) 
           (e* : (m : Z) → P m ≃ P (f e m)) where
    postulate
      indZ : (m : Z) → P m
      indZ-zero : indZ zero ≡ z*
    {-# REWRITE indZ-zero #-}

    postulate
      indZ-e : (m : Z) → indZ (f e m) ≡ f (e* m) (indZ m)

  -- import LoopS1

  -- Z : Set
  -- Z = LoopS1.Z

  -- zero : Z
  -- zero = LoopS1.zero

  -- e : Z ≃ Z
  -- e = LoopS1.e

  -- indZ : {P : Z → Set l1} → (z* : P zero) →
  --        (e* : (m : Z) → P m ≃ P (f e m)) →
  --        (m : Z) → P m
  -- indZ = LoopS1.indZ

  -- indZ-zero : {P : Z → Set l1} → (z* : P zero) →
  --             (e* : (m : Z) → P m ≃ P (f e m)) →
  --             indZ z* e* zero ≡ z*
  -- indZ-zero _ _ = refl

  -- indZ-e : {P : Z → Set l1} → (z* : P zero) →
  --          (e* : (m : Z) → P m ≃ P (f e m)) →
  --          (m : Z) → indZ z* e* (f e m) ≡ f (e* m) (indZ z* e* m)
  -- indZ-e = LoopS1.indZ-e

open Integers using (Z ; zero ; e ; indZ ; indZ-e) public


module Recursion where
  module _ {Y : Set l1} (z* : Y) (e* : Y ≃ Y) where
    recZ : Z → Y
    recZ = indZ {P = λ _ → Y} z* (λ _ → e*)
    
    recZ-zero : recZ zero ≡ z*
    recZ-zero = refl

    recZ-e : (m : Z) → recZ (f e m) ≡ f e* (recZ m)
    recZ-e = indZ-e z* (λ _ → e*)

    recZ-ε : (m : Z) → recZ m ≡ f e* (recZ (g e m))
    recZ-ε m = ap recZ (! (ε' e m)) ● recZ-e (g e m)

    recZ-!e : (m : Z) → recZ (g e m) ≡ g e* (recZ m)
    recZ-!e m = f (adj e*) (! (recZ-e (g e m))) ●
                ap (λ n → g e* (recZ n)) (ε' e m) 

    recZ-η : (m : Z) → recZ m ≡ g e* (recZ (f e m))
    recZ-η m = ap recZ (! (η e m)) ● recZ-!e (f e m)

open Recursion


module Arithmetic where
  infixl 6 _+_ 
  _+_ : Z → Z → Z
  _+_ m = recZ m e

  +e-r : (m n : Z) → m + f e n ≡ f e (m + n) -- m + (n + 1) = 1 + (m + n)
  +e-r m = recZ-e m e

  +unitr : (m : Z) → m + zero ≡ m
  +unitr m = refl

  +unitl : (m : Z) → zero + m ≡ m
  +unitl = indZ refl (λ m → lcomp-eqv (+e-r zero m) ∘e embed e)

  +e-l : (m n : Z) → f e m + n ≡ f e (m + n) -- m + (1 + n) = 1 + (m + n)
  +e-l m = indZ refl (λ n → rcomp-eqv (ap (f e) (! (+e-r m n))) ∘e
                            lcomp-eqv (+e-r (f e m) n) ∘e
                            embed e)

  +com : (m n : Z) → m + n ≡ n + m
  +com m = indZ (! (+unitl m)) (λ n → rcomp-eqv (! (+e-l n m)) ∘e
                                      lcomp-eqv (+e-r m n) ∘e
                                      embed e)

  +assoc : (k m n : Z) → (k + m) + n ≡ k + (m + n)
  +assoc k m n = indZ (λ _ _ → refl)
                      (λ n → pi-eqv-2
                      (λ m → pi-eqv-2
                      (λ k → rcomp-eqv (! (+e-r k (m + n)) ●
                                        ! (ap (_+_ k) (+e-r m n))) ∘e
                             lcomp-eqv (+e-r (k + m) n) ∘e
                             embed e)))
                      n m k

  infix 10 -_
  -_ : Z → Z
  -_ = recZ zero (!e e)

  +invl : (n : Z) → - n + n ≡ zero
  +invl = indZ refl
               (λ n → tpt-eqv (λ m → m ≡ zero)
                      (recZ-η (- n) e n ●
                       ap (g e) (+com (- n) (f e n)) ●
                       ! (recZ-!e (f e n) e (- n)) ●
                       +com (f e n) (g e (- n)) ●
                       ap (λ m → m + f e n)
                          (! (recZ-e zero (!e e) n))))

  +invr : (n : Z) → n + (- n) ≡ zero
  +invr = indZ refl
               (λ n → tpt-eqv (λ m → m ≡ zero)
                      (recZ-ε n e (- n) ●
                       ap (f e) (+com n (g e (- n))) ●
                       ! (recZ-e (g e (- n)) e n) ●
                       +com (g e (- n)) (f e n) ●
                       ap (λ m → f e n + m)
                          (! (recZ-e zero (!e e) n))))

  +eqv : Z → Z ≃ Z
  f (+eqv n) m = m + n
  g (+eqv n) m = m + (- n)
  η (+eqv n) m = +assoc m n (- n) ● ap (λ k → m + k) (+invr n)
  h (+eqv n) = g (+eqv n)
  ε (+eqv n) m = +assoc m (- n) n ● ap (λ k → m + k) (+invl n)


  div2 : (m : Z) → Σ Z (λ q → m ≡ q + q) ⊎ Σ Z (λ q → m ≡ f e (q + q))
  div2 = indZ (inl (zero , refl)) e*
    module div2 where
    e*-l-r : (m : Z) → Σ Z (λ q → m ≡ q + q) ≃ Σ Z (λ q → f e m ≡ f e (q + q))
    e*-l-r m = sigma-eqv-2 (λ q → embed e)

    e*-r-l : (m : Z) → Σ Z (λ q → m ≡ f e (q + q)) ≃ Σ Z (λ q → f e m ≡ q + q)
    e*-r-l m = sigma-eqv e (λ q → rcomp-eqv (! (ap (f e) (+e-r q q)) ●
                                             ! (+e-l q (f e q))) ∘e
                                  embed e)

    e* : (m : Z) →
         Σ Z (λ q → m ≡ q + q) ⊎ Σ Z (λ q → m ≡ f e (q + q)) ≃
         Σ Z (λ q → f e m ≡ q + q) ⊎ Σ Z (λ q → f e m ≡ f e (q + q))
    e* m = ⊎-com ∘e e*-l-r m ⊎e e*-r-l m

  div2-e : (m : Z) → div2 (f e m) ≡ f (div2.e* m) (div2 m)
  div2-e = indZ-e (inl (zero , refl)) div2.e*

  even-neq-odd : {x1 x2 : Z} →
                 {a1 : Σ Z (λ y → x1 ≡ y + y)} → div2 x1 ≡ inl a1 →
                 {a2 : Σ Z (λ y → x2 ≡ f e (y + y))} → div2 x2 ≡ inr a2 →
                 x1 ≢ x2
  even-neq-odd β1 β2 refl = inl-neq-inr (! β1 ● β2)

  div2-even-eqv : {x1 x2 y1 y2 : Z} →
                  {e1 : x1 ≡ y1 + y1} → {e2 : x2 ≡ y2 + y2} →
                  (e3 : x1 ≡ x2) → (e4 : y1 ≡ y2) →
                  e3 ≡ e1 ● ap (λ x → x + x) e4 ● ! e2 →
                  (div2 x1 ≡ inl (y1 , e1)) ≃ (div2 x2 ≡ inl (y2 , e2))
  div2-even-eqv {e1 = refl} {refl} refl refl refl = ide _

  div2-odd-eqv : {x1 x2 y1 y2 : Z} →
                 {e1 : x1 ≡ f e (y1 + y1)} → {e2 : x2 ≡ f e (y2 + y2)} →
                 (e3 : x1 ≡ x2) → (e4 : y1 ≡ y2) →
                 e3 ≡ e1 ● ap (λ x → f e (x + x)) e4 ● ! e2 →
                 (div2 x1 ≡ inr (y1 , e1)) ≃ (div2 x2 ≡ inr (y2 , e2))
  div2-odd-eqv {e1 = refl} {refl} refl refl refl = ide _

  div2-dbl : (m : Z) → div2 (m + m) ≡ inl (m , refl)
  div2-dbl = indZ refl (λ m →
                  div2-even-eqv (! (+e-l m (f e m))) refl
                                (! ●unitl ●
                                 ((! ●invr) [2,0,1] (! (+e-l m (f e m)))) ●
                                 ●assoc ●
                                 ! ●unitr) ∘e
                                lcomp-eqv (div2-e (m + f e m)) ∘e
                                embed (div2.e* (m + f e m)) ∘e
                                div2-odd-eqv (! (+e-r m m)) refl
                                             (! ●unitl ● ! ●unitl) ∘e
                                lcomp-eqv (div2-e (m + m)) ∘e
                                embed (div2.e* (m + m)))

  no-2tor : {m : Z} → m + m ≡ zero → m ≡ zero
  no-2tor {m} e =
    ! (ap fst (inl-eq (f (div2-even-eqv e refl (! !! ● ! ●unitl ● ! ●unitl))
                         (div2-dbl m))))

  anc1 : (n : Z) → - (f e n) ≡ g e (- n)
  anc1 n = recZ-e zero (!e e) n

  anc2 : (n : Z) → f e (- n) ≡ - (g e n)
  anc2 n = ! (recZ-!e zero (!e e) n)

  e≠i : (n : Z) → f e n ≢ - n
  e≠i n e1 =
    even-neq-odd (div2-dbl (- n)) (div2-e zero)
                 (! (ap (λ m → - n + m)
                        (+e-r n zero ● e1)) ●
                  ! (+assoc (- n) n (f e zero)) ●
                  ap (λ m → m + f e zero) (+invl n) ●
                  +unitl (f e zero))

  i0-inv : {n : Z} → - n ≡ n → n ≡ zero
  i0-inv {n} e1 = no-2tor (! (ap (λ m → m + n) e1) ● +invl n)

  i0 : - zero ≡ zero
  i0 = refl

open Arithmetic public
