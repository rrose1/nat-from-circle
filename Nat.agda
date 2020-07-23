{-# OPTIONS --without-K --rewriting #-}
module Nat where

open import UTT
open import ZModel
open import ZModelsHaveDecEq

module _ where
  import LessThan
  abstract
    _<_ : Z → Z → Set
    _<_ = LessThan._<_
    
    <-is-prop : {x1 x2 : Z} → is-prop (x1 < x2)
    <-is-prop = LessThan.<-is-prop
    
    <-irrefl : (x1 : Z) → ¬ (x1 < x1)
    <-irrefl = LessThan.<-irrefl
    
    <-ext : (x1 : Z) → x1 < f e x1
    <-ext = LessThan.<-ext
    
    <-trans : {x1 x2 x3 : Z} → x1 < x2 → x2 < x3 → x1 < x3
    <-trans = LessThan.<-trans
    
    <-trich : (x1 x2 : Z) → (x1 < x2) ⊎ (x2 ≡ x1) ⊎ (x2 < x1)
    <-trich = LessThan.<-trich
    
    <-disc : {x1 x2 : Z} → (x1 < f e x2) → (x1 ≡ x2) ⊎ (x1 < x2)
    <-disc = LessThan.<-disc
    
    <-disc' : {x1 x2 : Z} → (x1 < x2) → (x1 ≡ g e x2) ⊎ (x1 < g e x2)
    <-disc' = LessThan.<-disc'
    
    <-mono : {x1 x2 : Z} → (x1 < x2) ≃ (f e x1 < f e x2)
    <-mono = LessThan.<-mono
    
    <-adj : {x1 x2 : Z} → (f e x1 < x2) ≃ (x1 < g e x2)
    <-adj = LessThan.<-adj
    
    <-adj' : {x1 x2 : Z} → (x1 < f e x2) ≃ (g e x1 < x2)
    <-adj' = LessThan.<-adj'


is-one = <-ext zero

<-disc'' : {m n : Z} → m < n → n < f e m → ⊥
<-disc'' {m} {n} r1 r2 = aux (<-disc r2)
 module <-disc'' where
 aux : (n ≡ m) ⊎ (n < m) → ⊥
 aux (inl refl) = <-irrefl _ r1
 aux (inr r3) = <-irrefl _ (<-trans r1 r3)

is-nat : Z → Set
is-nat x = (zero ≡ x) ⊎ (zero < x)

is-nat-is-prop : {x : Z} → is-prop (is-nat x)
is-nat-is-prop (inl e1)   (inl e2)   = ap inl (Z-is-set e1 e2)
is-nat-is-prop (inl refl) (inr r2)   = rec⊥ (<-irrefl zero r2)
is-nat-is-prop (inr r1)   (inl refl) = rec⊥ (<-irrefl zero r1)
is-nat-is-prop (inr r1)   (inr r2)   = ap inr (<-is-prop r1 r2)

suc-is-nat : {x1 : Z} → is-nat x1 → is-nat (f e x1)
suc-is-nat {x1} (inl refl) = inr is-one
suc-is-nat {x1} (inr r1) = inr (<-trans r1 (<-ext x1))

module ZPartition where
 lem-prop : (x1 x2 : Z) →
            is-prop ((x1 < x2) ⊎ (x2 ≡ x1) ⊎ (x2 < x1))
 lem-prop x1 x2 (inl r1) (inl r2) = ap inl (<-is-prop r1 r2)
 lem-prop x1 _  (inl r1) (inr (inl refl)) = rec⊥ (<-irrefl x1 r1)
 lem-prop x1 x2 (inl r1) (inr (inr r2)) = rec⊥ (<-irrefl x1 (<-trans r1 r2))
 lem-prop x1 _  (inr (inl refl)) (inl r2) = rec⊥ (<-irrefl x1 r2)
 lem-prop x1 x2 (inr (inl refl)) (inr (inl r2)) =
   ap (λ r → inr (inl r)) (Z-is-set refl r2)
 lem-prop x1 _  (inr (inl refl)) (inr (inr r2)) = rec⊥ (<-irrefl x1 r2)
 lem-prop x1 x2 (inr (inr r1)) (inl r2) = rec⊥ (<-irrefl x2 (<-trans r1 r2))
 lem-prop x1 _  (inr (inr r1)) (inr (inl refl)) = rec⊥ (<-irrefl x1 r1)
 lem-prop x1 x2 (inr (inr r1)) (inr (inr r2)) =
   ap (λ r → inr (inr r)) (<-is-prop r1 r2)

 lem1 : (x2 : Z) →
        Z ≃ Σ Z (λ x1 → (x1 < x2) ⊎ (x2 ≡ x1) ⊎ (x2 < x1))
 f (lem1 x2) x1 = x1 , <-trich x1 x2
 g (lem1 x2) (x1 , _) = x1
 η (lem1 x2) x1 = refl
 h (lem1 x2) = g (lem1 x2)
 ε (lem1 x2) _ = pair-eq (refl , lem-prop _ _ _ _)

 Z-part : (x2 : Z) →
          Z ≃ Σ Z (λ x1 → x1 < x2) ⊎
              Σ Z (λ x1 → x2 ≡ x1) ⊎
              Σ Z (λ x1 → x2 < x1)
 Z-part x2 = (ide _ ⊎e
              sigma-distr (λ x1 → x2 ≡ x1) (λ x1 → x2 < x1)) ∘e
             (sigma-distr (λ x1 → x1 < x2)
                          (λ x1 → (x2 ≡ x1) ⊎ (x2 < x1))) ∘e
             lem1 x2

open ZPartition using (Z-part)

tpt-suc-is-nat : {x1 x2 : Z} →
                (e1 : x1 ≡ x2) → (e2 : f e x1 ≡ f e x2) → ap (f e) e1 ≡ e2 →
                {n1 : is-nat x1} → {n2 : is-nat x2} →
                (tpt is-nat e1 n1 ≡ n2) →
                (tpt is-nat e2 (suc-is-nat n1) ≡ suc-is-nat n2)
tpt-suc-is-nat refl refl refl {n1} = ap suc-is-nat

module Approximation
      (P  : (x : Z) → (n : is-nat x) → Set l1)
      (z* : P zero (inl refl))
      (s* : (x : Z) → (n : is-nat x) → P x n → P (f e x) (suc-is-nat n))
      where

 record approx-type (x1 : Z) : Set l1 where
   field
     a  : (x2 : Z) → (n2 : is-nat x2) → x2 < x1 → P x2 n2 
     rz : (r1 : zero < x1) → a zero (inl refl) r1 ≡ z*
     rs : (x2 : Z) → (n2 : is-nat x2) →
          (r1 : f e x2 < x1) → (r2 : x2 < x1) →
          a (f e x2) (suc-is-nat n2) r1 ≡ s* x2 n2 (a x2 n2 r2)

   a-coh1 : {x2 x3 : Z} → (e1 : x2 ≡ x3) →
            {n2 : is-nat x2} → {n3 : is-nat x3} →
            (e2 : tpt is-nat e1 n2 ≡ n3) →
            {r2 : x2 < x1} → {r3 : x3 < x1} →
            tpt (λ x → x < x1) e1 r2 ≡ r3 →
            tpt2 P e1 e2 (a x2 n2 r2) ≡ (a x3 n3 r3)
   a-coh1 refl refl refl = refl

   s*-a-coh1 : {x2 x3 : Z} →
               (e1 : x2 ≡ x3) → (e2 : f e x2 ≡ f e x3) → (e3 : ap (f e) e1 ≡ e2) →
               {n2 : is-nat x2} → {n3 : is-nat x3} →
               (e4 : tpt is-nat e1 n2 ≡ n3) →
               (e5 : tpt is-nat e2 (suc-is-nat n2) ≡ suc-is-nat n3) →
               (e6 : tpt-suc-is-nat e1 e2 e3 e4 ≡ e5) →
               {r2 : x2 < x1} → {r3 : x3 < x1} →
               tpt (λ x → x < x1) e1 r2 ≡ r3 →
               tpt2 P e2 e5 (s* x2 n2 (a x2 n2 r2)) ≡ s* x3 n3 (a x3 n3 r3)
   s*-a-coh1 refl refl refl refl refl refl refl = refl


 open approx-type

 record approx-eq-data {x1 : Z} (a1 a2 : approx-type x1) : Set l1 where
   field
     a-eq : (x2 : Z) → (n2 : is-nat x2) → (r : x2 < x1) →
            a a1 x2 n2 r ≡ a a2 x2 n2 r
     a-eq' : a a1 ≡ a a2
     a-eq-coh : funext (λ x2 → funext (λ n2 → funext (λ r → a-eq x2 n2 r))) ≡
                a-eq'

     rz-eq : (r : zero < x1) → ! (a-eq zero (inl refl) r) ● rz a1 r ≡ rz a2 r

     rs-eq : (x2 : Z) → (n2 : is-nat x2) →
             (r1 : f e x2 < x1) → (r2 : x2 < x1) →
             rs a1 x2 n2 r1 r2 ● ap (s* x2 n2) (a-eq x2 n2 r2) ≡
              a-eq (f e x2) (suc-is-nat n2) r1 ● rs a2 x2 n2 r1 r2

 open approx-eq-data

 module _ {x1 : Z} (a1 a2 : approx-type x1) where
   a-eq-coh' : {a-eq : (x2 : Z) → (n2 : is-nat x2) → (r : x2 < x1) →
                       a a1 x2 n2 r ≡ a a2 x2 n2 r} →
               {a-eq' : a a1 ≡ a a2} →
               (a-eq-coh : funext (λ x2 → funext (λ n2 → funext (λ r →
                             a-eq x2 n2 r))) ≡ a-eq') →
               (x2 : Z) → (n2 : is-nat x2) → (r2 : x2 < x1) →
               a-eq x2 n2 r2 ≡
               ap (λ f → f r2)
                  (ap (λ f → f n2)
                      (ap (λ f → f x2) a-eq'))
   a-eq-coh' a-eq-coh x2 n2 r =
     ap (λ f → f r)
        (g (adj' happly-eqv)
           (ap (λ f → f n2)
               (g (adj' happly-eqv)
                  (ap (λ f → f x2)
                      (g (adj' happly-eqv) a-eq-coh)))))

 module _ {x1 : Z} {a1 a2 : approx-type x1} where
   approx-eq : approx-eq-data a1 a2 → a1 ≡ a2
   approx-eq record { a-eq = a-eq ; a-eq' = refl ; a-eq-coh = a-eq-coh ;
                      rz-eq = rz-eq ; rs-eq = rs-eq } =
     ap (λ rz → record { a = a a2 ; rz = rz ; rs = rs a1 })
        {x2 = rz a2}
        (funext (λ r →
          ! ●unitl ●
          ! (f rwhisk-eqv (ap ! (a-eq-coh' a1 a2 a-eq-coh zero (inl refl) r))) ●
          rz-eq r)) ●
     ap (λ rs → record { a = a a2 ; rz = rz a2 ; rs = rs })
        (funext (λ x2 → funext (λ n2 → funext (λ r1 → funext (λ r2 →
          ! ●unitr ●
          ! (f lwhisk-eqv
               (ap (ap (s* x2 n2)) (a-eq-coh' a1 a2 a-eq-coh x2 n2 r2))) ●
          rs-eq x2 n2 r1 r2 ●
          f rwhisk-eqv
            (a-eq-coh' a1 a2 a-eq-coh (f e x2) (suc-is-nat n2) r1) ●
          ●unitl)))))


 module Approx<1IsContr (x1 : Z) (r1 : g e x1 < zero) where
   lem1 : (x2 : Z) → (n2 : is-nat x2) → x2 < x1 →
          (x2 ≡ g e x1) ⊎ (x2 < g e x1) → ⊥ {lzero}
   lem1 _ (inl refl) r3 (inl e4) = <-irrefl _ (tpt (λ x → g e x1 < x) e4 r1)
   lem1 _ (inl refl) r3 (inr r4) = <-irrefl _ (<-trans r4 r1)
   lem1 x2 (inr r2) r3 (inl refl) = <-irrefl _ (<-trans r1 r2)
   lem1 x2 (inr r2) r3 (inr r4) = <-irrefl _ (<-trans (<-trans r2 r4) r1)

   approx<1 : approx-type x1
   a approx<1 x2 n2 r3 = rec⊥ (lem1 x2 n2 r3 (<-disc' r3))
   rz approx<1 r2 = rec⊥ (lem1 zero (inl refl) r2 (<-disc' r2))
   rs approx<1 x2 n2 r3 r4 = rec⊥ (lem1 x2 n2 r4 (<-disc' r4))

   lem2 : (α1 α2 : approx-type x1) → approx-eq-data α1 α2
   a-eq (lem2 α1 α2) x2 n2 r3 = rec⊥ (lem1 x2 n2 r3 (<-disc' r3))
   a-eq' (lem2 α1 α2) = _
   a-eq-coh (lem2 α1 α2) = refl
   rz-eq (lem2 α1 α2) r2 = rec⊥ (lem1 zero (inl refl) r2 (<-disc' r2))
   rs-eq (lem2 α1 α2) x2 n2 r3 r4 = rec⊥ (lem1 x2 n2 r4 (<-disc' r4))

   approx<1-is-prop : is-prop (approx-type x1)
   approx<1-is-prop α1 α2 = approx-eq (lem2 α1 α2)

 open Approx<1IsContr using (approx<1 ; approx<1-is-prop)


 approx-eqv-type = λ x1 → approx-type x1 ≃ approx-type (f e x1)


 module ApproxEqv1 (x1 : Z) (r1 : x1 < zero) where
   approx-eqv-1 : approx-eqv-type x1
   f approx-eqv-1 _ = approx<1 (f e x1) (tpt (λ x → x < zero) (! (η e x1)) r1)
   g approx-eqv-1 _ = approx<1 x1 (<-trans (f <-adj' (<-ext x1)) r1)
   η approx-eqv-1 _ = approx<1-is-prop x1 (<-trans (f <-adj' (<-ext x1)) r1) _ _
   h approx-eqv-1 = g approx-eqv-1
   ε approx-eqv-1 _ =
     approx<1-is-prop (f e x1) (tpt (λ x → x < zero) (! (η e x1)) r1) _ _

 open ApproxEqv1 using (approx-eqv-1)


 module Approx1IsContr where
   approx1 : approx-type (f e zero)
   a approx1 x2 (inl refl) r3 = z*
   a approx1 x2 (inr r2) r3 = rec⊥ (<-disc'' r2 r3)
   rz approx1 _ = refl
   rs approx1 x2 (inl refl) r3 _ = rec⊥ (<-disc'' is-one r3)
   rs approx1 x2 (inr r2) _ r4 = rec⊥ (<-disc'' r2 r4)

   lem1 : (α : approx-type (f e zero)) →
          (x2 : Z) → (n2 : is-nat x2) → (r3 : x2 < f e zero) →
          a α x2 n2 r3 ≡ a approx1 x2 n2 r3
   lem1 α x2 (inl refl) r3 = rz α r3
   lem1 α x2 (inr r2) r3 = rec⊥ (<-disc'' r2 r3)

   lem2 : (α : approx-type (f e zero)) → approx-eq-data α approx1
   a-eq (lem2 α) = lem1 α
   a-eq' (lem2 α) = _
   a-eq-coh (lem2 α) = refl
   rz-eq (lem2 α) r3 = ●invl
   rs-eq (lem2 α) x2 (inl refl) r3 _ = rec⊥ (<-disc'' is-one r3)
   rs-eq (lem2 α) x2 (inr r2) _ r4 = rec⊥ (<-disc'' r2 r4)

   approx1-is-prop : is-prop (approx-type (f e zero))
   approx1-is-prop α1 α2 = approx-eq (lem2 α1) ● ! (approx-eq (lem2 α2))

 open Approx1IsContr using (approx1 ; approx1-is-prop)


 module ApproxEqv2 (x1 : Z) where
   approx-eqv-2 : (r1 : zero ≡ x1) → approx-eqv-type x1
   f (approx-eqv-2 refl) _ = approx1
   g (approx-eqv-2 refl) _ = approx<1 zero (f <-adj' is-one)
   η (approx-eqv-2 refl) _ = approx<1-is-prop zero (f <-adj' is-one) _ _
   h (approx-eqv-2 refl) = g (approx-eqv-2 refl)
   ε (approx-eqv-2 refl) = approx1-is-prop approx1

 open ApproxEqv2 using (approx-eqv-2)


 module ApproxEqv3 (x1 : Z) (r1 : zero < x1) where
   module _ (α : approx-type x1) where
     lem1 : (x2 : Z) → (n2 : is-nat x2) → (x2 ≡ x1) ⊎ (x2 < x1) → P x2 n2
     lem1 x2 n2 (inl refl) =
       tpt2 P (ε' e x2) (is-nat-is-prop _ _)
            (s* (g e x2) (<-disc' r1)
                (a α (g e x2) (<-disc' r1) (f <-adj' (<-ext x2))))
     lem1 x2 n2 (inr r4) = a α x2 n2 r4

     lem2 : (w : (zero ≡ x1) ⊎ (zero < x1)) → lem1 zero (inl refl) w ≡ z*
     lem2 (inl refl) = rec⊥ (<-irrefl zero r1)
     lem2 (inr r2) = rz α r2

     lem3 : (x2 : Z) → (n2 : is-nat x2) →
            (w1 : (f e x2 ≡ x1) ⊎ (f e x2 < x1)) →
            (w2 : (x2 ≡ x1) ⊎ (x2 < x1)) →
            lem1 (f e x2) (suc-is-nat n2) w1  ≡
            s* x2 n2 (lem1 x2 n2 w2)
     lem3 x2 n2 (inl e5) (inl refl) =
       rec⊥ (<-irrefl _ (tpt (λ x → x2 < x) e5 (<-ext x2)))
     lem3 x2 n2 (inl refl) (inr r6) = 
       s*-a-coh1 α (η e x2) (ε' e (f e x2)) (τ' e x2)
                 (is-nat-is-prop _ _) (is-nat-is-prop _ _)
                 (prop-is-set is-nat-is-prop _ _) (<-is-prop _ _)
     lem3 x2 n2 (inr r5) (inl refl) = rec⊥ (<-irrefl _ (<-trans r5 (<-ext x2)))
     lem3 x2 n2 (inr r5) (inr r6) = rs α x2 n2 r5 r6

     lem5 : approx-type (f e x1)
     a lem5 x2 n2 r3 = lem1 x2 n2 (<-disc r3)
     rz lem5 r2 = lem2 (<-disc r2)
     rs lem5 x2 n2 r3 r4 = lem3 x2 n2 (<-disc r3) (<-disc r4)

   lem6 : {x1 : Z} → (r1 : zero < x1) → approx-type (f e x1) → approx-type x1
   a (lem6 {x1} r1 α) x2 n2 r3 = a α x2 n2 (<-trans r3 (<-ext x1))
   rz (lem6 {x1} r1 α) r2 = rz α (<-trans r2 (<-ext x1))
   rs (lem6 {x1} r1 α) x2 n2 r3 r4 =
     rs α x2 n2 (<-trans r3 (<-ext x1)) (<-trans r4 (<-ext x1))

   module _ (α : approx-type x1) where
     lem7 : (x2 : Z) → (n2 : is-nat x2) → (r3 : x2 < x1) →
            (w : (x2 ≡ x1) ⊎ (x2 < x1)) →
            lem1 α x2 n2 w ≡ a α x2 n2 r3
     lem7 x2 n2 r3 (inl refl) = rec⊥ (<-irrefl _ r3)
     lem7 x2 n2 r3 (inr r4) = ap (a α x2 n2) (<-is-prop _ _)

     lem8 : (r2 : zero < x1) → (w : (zero ≡ x1) ⊎ (zero < x1)) →
            ! (lem7 zero (inl refl) r2 w) ● lem2 α w ≡ rz α r2
     lem8 r2 (inl refl) = rec⊥ (<-irrefl zero r2)
     lem8 r2 (inr r3) =
       tpt (λ r → ! (ap (a α zero (inl refl)) (<-is-prop r r2)) ● rz α r ≡ rz α r2)
           (<-is-prop r2 r3)
           (f rwhisk-eqv
              (ap (λ w → ! (ap (a α zero (inl refl)) w))
                  (prop-is-set <-is-prop _ refl)) ●
              ●unitl)

     lem10 : (x2 : Z) → (n2 : is-nat x2) → (r2 : f e x2 < x1) → (r3 : x2 < x1) →
             (w1 : (f e x2 ≡ x1) ⊎ (f e x2 < x1)) →
             (w2 : (x2 ≡ x1) ⊎ (x2 < x1)) →
             lem3 α x2 n2 w1 w2 ● ap (s* x2 n2) (lem7 x2 n2 r3 w2) ≡
             lem7 (f e x2) (suc-is-nat n2) r2 w1 ● rs α x2 n2 r2 r3
     lem10 x2 n2 r2 r3 (inl e4) (inl refl) = rec⊥ (<-irrefl x2 r3)
     lem10 x2 n2 r2 r3 (inl refl) (inr r6) = rec⊥ (<-irrefl (f e x2) r2)
     lem10 x2 n2 r2 r3 (inr r5) (inl refl) = rec⊥ (<-irrefl x2 r3)
     lem10 x2 n2 r2 r3 (inr r5) (inr r6) =
       tpt2-cart
         (λ r r' → rs α x2 n2 r r' ●
                   ap (s* x2 n2) (ap (a α x2 n2) (<-is-prop r' r3)) ≡
                   ap (a α (f e x2) (suc-is-nat n2)) (<-is-prop r r2) ●
                   rs α x2 n2 r2 r3)
         (<-is-prop r2 r5) (<-is-prop r3 r6)
         (f lwhisk-eqv (ap (λ w → ap (s* x2 n2) (ap (a α x2 n2) w))
                           (prop-is-set <-is-prop _ refl)) ●
          ●unitr ● ! ●unitl ●
          ! (f rwhisk-eqv (ap (ap (a α (f e x2) (suc-is-nat n2)))
                              (prop-is-set <-is-prop _ refl))))

     lem24 : approx-eq-data (lem6 r1 (lem5 α)) α
     a-eq lem24 x2 n2 r3 = lem7 x2 n2 r3 (<-disc (<-trans r3 (<-ext x1)))
     a-eq' lem24 = _
     a-eq-coh lem24 = refl
     rz-eq lem24 r2 = lem8 r2 (<-disc (<-trans r2 (<-ext x1)))
     rs-eq lem24 x2 n2 r2 r3 = lem10 x2 n2 r2 r3
                                     (<-disc (<-trans r2 (<-ext x1)))
                                     (<-disc (<-trans r3 (<-ext x1)))

   module _ (α : approx-type (f e x1)) where
     lem25 : (x2 : Z) → (n2 : is-nat x2) → (r3 : x2 < f e x1) →
             (w : (x2 ≡ x1) ⊎ (x2 < x1)) →
             lem1 (lem6 r1 α) x2 n2 w ≡ a α x2 n2 r3
     lem25 x2 n2 r3 (inl refl) =
       ap (tpt2 P (ε' e x2)
                (is-nat-is-prop
                  (tpt is-nat (ε' e x2) (suc-is-nat (<-disc' r1))) n2))
          (! (rs α (g e x2) (<-disc' r1)
                 (tpt (λ x → x < f e x2) (! (ε' e x2)) (<-ext x2))
                 (<-trans (f <-adj' (<-ext x2)) (<-ext x2)))) ●
       a-coh1 α (ε' e x2) (is-nat-is-prop _ _) (<-is-prop _ _)

     lem25 x2 n2 r3 (inr r4) = ap (a α x2 n2) (<-is-prop _ _)

     lem26 : (r2 : zero < f e x1) → (w : (zero ≡ x1) ⊎ (zero < x1)) →
             ! (lem25 zero (inl refl) r2 w) ● lem2 (lem6 r1 α) w ≡ rz α r2
     lem26 r2 (inl refl) = rec⊥ (<-irrefl zero r1)
     lem26 r2 (inr r3) =
       tpt (λ r → ! (ap (a α zero (inl refl)) (<-is-prop r r2)) ● rz α r ≡
                  rz α r2)
           (<-is-prop r2 (<-trans r3 (<-ext x1)))
           (f rwhisk-eqv
              (ap (λ w → ! (ap (a α zero (inl refl)) w))
                  (prop-is-set <-is-prop _ refl)) ●
            ●unitl)

     lem27 : (x2 : Z) → (α : approx-type (f e (f e x2))) →
             (n2 : is-nat x2) → (r1 : zero < f e x2) →
             (r3 : f e x2 < f e (f e x2)) →
             {x3 : Z} → (e1 : x3 ≡ x2) → (e2 : f e x3 ≡ f e x2) →
             (e3 : ap (f e) e1 ≡ e2) →
             {n3 : is-nat x3} →
             (e4 : tpt is-nat e1 n3 ≡ n2) →
             (e5 : tpt is-nat e2 (suc-is-nat n3) ≡ suc-is-nat n2) →
             (e6 : tpt-suc-is-nat e1 e2 e3 e4 ≡ e5) →
             (r4 : x3 < f e x2) →
             {r5 : f e x3 < f e (f e x2)} →
             (e7 : tpt (λ x → x < f e (f e x2)) e2 r5 ≡ r3) →
             s*-a-coh1 (lem6 r1 α) e1 e2 e3 e4 e5 e6 {r2 = r4} refl ≡
             (ap (tpt2 P e2 e5)
                 (! (rs α x3 n3 r5 (<-trans r4 (<-ext (f e x2))))) ●
             a-coh1 α e2 e5 e7) ●
             rs α x2 n2 r3
                (<-trans (tpt (λ x → x < f e x2) e1 r4) (<-ext (f e x2)))
     lem27 x2 α n2 r2 r3 refl e2 refl refl refl refl r4 refl =
       ! ●invl ● (f rwhisk-eqv (! (ap-id _) ● ! ●unitr))

     lem28 : (x2 : Z) → (α : approx-type (f e (f e x2))) →
             (n2 : is-nat x2) → (r1 : zero < f e x2) →
             (r3 : f e x2 < f e (f e x2)) →
             {r6 : x2 < f e x2} →
             (e3 : tpt (λ x → x < f e x2)
                       (η e x2) (f <-adj' (<-ext (f e x2))) ≡ r6) →
             {r4 : x2 < f e (f e x2)} → (e2 : <-trans r6 (<-ext (f e x2)) ≡ r4) →
             s*-a-coh1 (lem6 r1 α) (η e x2) (ε' e (f e x2)) (τ' e x2)
             (is-nat-is-prop (tpt is-nat (η e x2) (<-disc' r1)) n2)
             (is-nat-is-prop
              (tpt is-nat (ε' e (f e x2)) (suc-is-nat (<-disc' r1)))
              (suc-is-nat n2))
             (prop-is-set is-nat-is-prop
              (tpt-suc-is-nat (η e x2) (ε' e (f e x2)) (τ' e x2)
               (is-nat-is-prop (tpt is-nat (η e x2) (<-disc' r1)) n2))
              (is-nat-is-prop
               (tpt is-nat (ε' e (f e x2)) (suc-is-nat (<-disc' r1)))
               (suc-is-nat n2)))
             (<-is-prop
              (tpt (λ x → x < f e x2) (η e x2) (f <-adj' (<-ext (f e x2)))) r6)
             ●
             ap (s* x2 n2)
             (ap (a α x2 n2) (<-is-prop (<-trans r6 (<-ext (f e x2))) r4))
             ≡
             (ap
              (tpt2 P (ε' e (f e x2))
               (is-nat-is-prop
                (tpt is-nat (ε' e (f e x2)) (suc-is-nat (<-disc' r1)))
                (suc-is-nat n2)))
              (!
               (rs α (g e (f e x2)) (<-disc' r1)
                (tpt (λ x → x < f e (f e x2)) (! (ε' e (f e x2))) (<-ext (f e x2)))
                (<-trans (f <-adj' (<-ext (f e x2))) (<-ext (f e x2)))))
              ●
              a-coh1 α (ε' e (f e x2))
              (is-nat-is-prop
               (tpt is-nat (ε' e (f e x2)) (suc-is-nat (<-disc' r1)))
               (suc-is-nat n2))
              (<-is-prop
               (tpt (λ x → x < f e (f e x2)) (ε' e (f e x2))
                (tpt (λ x → x < f e (f e x2)) (! (ε' e (f e x2)))
                 (<-ext (f e x2))))
               r3))
             ● rs α x2 n2 r3 r4
     lem28 x2 α n2 r1 r3 refl refl =
       f lwhisk-eqv
         (ap (λ r → ap (s* x2 n2) (ap (a α x2 n2) r))
             (prop-is-set <-is-prop _ refl)) ●
       ●unitr ●
       ap (s*-a-coh1 (lem6 r1 α) (η e x2) (ε' e (f e x2)) (τ' e x2)
                     (is-nat-is-prop (tpt is-nat (η e x2) (<-disc' r1)) n2)
                     (is-nat-is-prop (tpt is-nat (ε' e (f e x2))
                                                 (suc-is-nat (<-disc' r1)))
                                     (suc-is-nat n2))
                     (prop-is-set is-nat-is-prop
                       _ _))
          (prop-is-set <-is-prop _ refl) ●
       lem27 x2 α n2 r1 r3 (η e x2) (ε' e (f e x2)) (τ' e x2)
             (is-nat-is-prop _ _) (is-nat-is-prop _ _)
             (prop-is-set is-nat-is-prop _ _)
             (f <-adj' (<-ext (f e x2)))
             (<-is-prop _ _)

     lem29 : (x2 : Z) → (n2 : is-nat x2) → (r3 : f e x2 < f e x1) →
             (r4 : x2 < f e x1) →
             (w1 : (f e x2 ≡ x1) ⊎ (f e x2 < x1)) →
             (w2 : (x2 ≡ x1) ⊎ (x2 < x1)) →
             lem3 (lem6 r1 α) x2 n2 w1 w2 ●
             ap (s* x2 n2) (lem25 x2 n2 r4 w2) ≡
             lem25 (f e x2) (suc-is-nat n2) r3 w1 ● rs α x2 n2 r3 r4
     lem29 x2 n2 r3 r4 (inl e5) (inl refl) =
       rec⊥ (<-irrefl x2 (tpt (_<_ x2) e5 (<-ext x2)))

     lem29 x2 n2 r3 r4 (inl refl) (inr r6) =
       lem28 x2 α n2 r1 r3 (<-is-prop _ _) (<-is-prop _ _)

     lem29 x2 n2 r3 r4 (inr r5) (inl refl) =
       rec⊥ (<-irrefl (f e x2) (<-trans r5 (<-ext x2)))
     lem29 x2 n2 r3 r4 (inr r5) (inr r6) =
       tpt2-cart
         (λ r r' → rs α x2 n2 r r' ●
                   ap (s* x2 n2) (ap (a α x2 n2) (<-is-prop r' r4)) ≡
                   ap (a α (f e x2) (suc-is-nat n2)) (<-is-prop r r3) ●
                   rs α x2 n2 r3 r4)
         (<-is-prop r3 _) (<-is-prop r4 _)
         (f lwhisk-eqv
            (ap (λ w → ap (s* x2 n2) (ap (a α x2 n2) w))
                (prop-is-set <-is-prop _ refl)) ●
          ●unitr ● ! ●unitl ●
          ! (f rwhisk-eqv
               (ap (ap (a α (f e x2) (suc-is-nat n2)))
                   (prop-is-set <-is-prop _ refl))))

     lem30 : approx-eq-data (lem5 (lem6 r1 α)) α
     a-eq lem30 x2 n2 r3 = lem25 x2 n2 r3 (<-disc r3)
     a-eq' lem30 = _
     a-eq-coh lem30 = refl
     rz-eq lem30 r2 = lem26 r2 (<-disc r2)
     rs-eq lem30 x2 n2 r3 r4 = lem29 x2 n2 r3 r4 (<-disc r3) (<-disc r4)

   approx-eqv-3 : approx-eqv-type x1
   f approx-eqv-3 = lem5
   g approx-eqv-3 = lem6 r1
   η approx-eqv-3 α = approx-eq (lem24 α)
   h approx-eqv-3 = g approx-eqv-3
   ε approx-eqv-3 α = approx-eq (lem30 α)

 open ApproxEqv3 using (approx-eqv-3) public

 --   approx-eqv : (x1 : Z) → approx-eqv-type x1
 --   approx-eqv =
 --     f (pi-eqv-1' (!e (Z-part zero)) {P = approx-eqv-type} ∘e
 --        !e (coprod-adj (λ w → approx-eqv-type (g (Z-part zero) w))) ∘e
 --        sigma-eqv-2 (λ _ →
 --        !e (coprod-adj (λ w → approx-eqv-type (g (Z-part zero) (inr w))))))
 --       ((λ w → approx-eqv-1 (fst w) (snd w)) ,
 --        (λ w → approx-eqv-2 (fst w) (snd w)) ,
 --        (λ w → approx-eqv-3 (fst w) (snd w)))

 approx-eqv : (x1 : Z) → approx-eqv-type x1
 approx-eqv x1 = aux (<-trich x1 zero)
   module approx-eqv where
   aux : (x1 < zero) ⊎ (zero ≡ x1) ⊎ (zero < x1) → approx-eqv-type x1
   aux (inl r) = approx-eqv-1 x1 r
   aux (inr (inl e)) = approx-eqv-2 x1 e
   aux (inr (inr r)) = approx-eqv-3 x1 r

 approx : (x : Z) → approx-type x
 approx = indZ (approx<1 zero (f <-adj' is-one)) approx-eqv

 approx-cmpt : (x : Z) → approx (f e x) ≡ f (approx-eqv x) (approx x)
 approx-cmpt = indZ-e (approx<1 zero (f <-adj' is-one)) approx-eqv

 indN : (x : Z) → (n : is-nat x) → P x n
 indN x n = a (approx (f e x)) x n (<-ext x)

 indN-0 : indN zero (inl refl) ≡ z*
 indN-0 = rz (approx (f e zero)) (<-ext zero)


 module NatIndCmpt where
   eext : (x : Z) → x < f e (f e x)
   eext x = <-trans (<-ext x) (<-ext (f e x))

   lem2 : (x1 : Z) → (r1 : zero < x1) → (r2 : zero < f e x1) →
          (w : (x1 ≡ f e x1) ⊎ (x1 < f e x1)) →
          ApproxEqv3.lem1 (f e x1) r2 (approx (f e x1)) x1 (inr r1) w ≡
          indN x1 (inr r1)
   lem2 x1 r1 r2 (inl e2) = rec⊥ (<-irrefl _ (tpt (λ y → y < f e x1) e2 (<-ext x1)))
   lem2 x1 r1 r2 (inr r3) = ap (a (approx (f e x1)) x1 (inr r1)) (<-is-prop _ _)

   lem3 : (x1 : Z) → (r1 : zero < x1) →
          (w : (f e x1 < zero) ⊎ (zero ≡ f e x1) ⊎ (zero < f e x1)) →
          a (f (approx-eqv.aux (f e x1) w) (approx (f e x1)))
            x1 (inr r1) (eext x1) ≡
          indN x1 (inr r1)
   lem3 x1 r1 (inl r2) = rec⊥ (<-irrefl _ (<-trans (<-trans r2 r1) (<-ext x1)))
   lem3 x1 r1 (inr (inl e2)) =
     rec⊥ (<-irrefl _ (<-trans (tpt (λ y → y < x1) e2 r1) (<-ext x1)))
   lem3 x1 r1 (inr (inr r2)) = lem2 x1 r1 r2 (<-disc (eext x1))

   indN-suc : (x : Z) → (n : is-nat x) →
              indN (f e x) (suc-is-nat n) ≡ s* x n (indN x n)
   indN-suc x (inl refl) =
     rs (approx (f e (f e zero))) zero (inl refl) (<-ext (f e zero)) (eext zero) ●
     ap (s* zero (inl refl))
        (rz (approx (f e (f e zero))) (eext zero) ● ! indN-0)
   indN-suc x (inr r1) =
     rs (approx (f e (f e x)))
        x (inr r1) (<-ext (f e x)) (eext x) ●
     ap (s* x (inr r1))
        (f happly-eqv
           (f happly-eqv
              (f happly-eqv (ap a (approx-cmpt (f e x))) x)
              (inr r1))
           (eext x) ●
         lem3 x r1 (<-trich (f e x) zero))

 open NatIndCmpt using (indN-suc) public

open Approximation using (indN ; indN-0 ; indN-suc)

module Test where
  open import Agda.Builtin.Nat using (Nat ; suc)
  f-test : Σ Z is-nat → Nat
  f-test (x , n) = indN (λ _ _ → Nat) 0 (λ _ _ → suc) x n

  g-test : Nat → Σ Z is-nat
  g-test 0 = zero , inl refl
  g-test (suc n) = f e (fst (g-test n)) , suc-is-nat (snd (g-test n))

  η-test-suc : (x1 : Z) → (n1 : is-nat x1) →
               g-test (f-test (x1 , n1)) ≡ (x1 , n1) →
               g-test (f-test (f e x1 , suc-is-nat n1)) ≡ (f e x1 , suc-is-nat n1)
  η-test-suc x1 n1 e1 =
    ap g-test (indN-suc (λ _ _ → Nat) 0 (λ _ _ → suc) x1 n1) ●
    ap (λ w → f e (fst w) , suc-is-nat (snd w)) e1

  η-test : (w : Σ Z is-nat) → g-test (f-test w) ≡ w
  η-test (x , n) =
    indN (λ x n → g-test (f-test (x , n)) ≡ (x , n))
         (ap g-test (indN-0 (λ _ _ → Nat) 0 (λ _ _ → suc)))
         η-test-suc x n

  ε-test : (m : Nat) → f-test (g-test m) ≡ m
  ε-test 0 = indN-0 (λ _ _ → Nat) 0 (λ _ _ → suc)
  ε-test (suc m) =
    indN-suc (λ _ _ → Nat) 0 (λ _ _ → suc) (fst (g-test m)) (snd (g-test m)) ●
    ap suc (ε-test m)

  test : Σ Z is-nat ≃ Nat
  f test = f-test
  g test = g-test
  η test = η-test
  h test = g test
  ε test = ε-test
