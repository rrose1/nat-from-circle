{-# OPTIONS --without-K --rewriting #-}
module Approximation where

open import S1TT
open import LoopS1HasDiv2Alg
open import Structure
open import Presegment
open import Asymmetry
open import Segment
open import LoopS1Segment
open import IncrementMin
open import IncrementMax
open import LoopS1HasDecEq
open import Nat
open import ApproximationDefinition
open import ApproximationCoherence


module _ (P  : (x : b ≡ b) → (n : is-nat x) → Set l1)
         (z* : P refl refl)
         (s* : (x : b ≡ b) → (n : is-nat x) → P x n → P (l ◾ x) (suc-is-nat n))
         where
         
  open SectionOnLoopS1 hiding (P)
  open ApproximationBase P z* s*
  open _≃_
  open is-approx
  open approx-eq-data

  
  approx : SectionOnLoopS1
  P-b approx x1 = (n1 : is-nat x1) → is-approx (x1 , n1)
  
  a (p0 approx n1) x2 n2 r1 = tpt2 P (! r1) (Bool-is-set _ _) z*
  rz (p0 approx n1) r1 =
    tpt2-loop path-s1-is-set (λ _ → prop-is-set Bool-is-set) P
              (! r1) (Bool-is-set _ _) z*
  rs (p0 approx n1) x2 n2 r1 =
    rec⊥ (lem8 (x2 , n2) (! (lem1 (tpt (λ n → suc (x2 , n2) ≤ (refl , n))
                                        (Bool-is-set n1 refl) r1))))
                                        
  -----
  f (P-l approx x1) = f-P-l-approx

  -----
  g (P-l approx x1) = g-P-l-approx

  -----
  η (P-l approx x1) ax = funext (λ n1 → approx-eq (eq n1))
    module η-P-l-approx where
    eq : (n1 : is-nat x1) →
         approx-eq-data (g (P-l approx x1) (f (P-l approx x1) ax) n1) (ax n1)
    a-eq (eq n1) x2 n2 r1 = aux1 (lem2 (suc-is-nat n1))
      module a-eq-eq where
      aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
             a-f-P-l-approx.aux1 ax (suc-is-nat n1) x2 n2
              (lem5 (x2 , n2) (x1 , n1) r1) a1 ≡
             a (ax n1) x2 n2 r1
      aux1 (inl e1) =
        a-coh1 (ax n1) (lem1' n2 e1 (lem5 (x2 , n2) (x1 , n1) r1))
               (Bool-is-set _ _) (leq-is-prop (x2 , n2) (x1 , n1) _ _)
               (rz (ax n1) (lem6 (x1 , n1))) refl
      
      aux1 (inr n3) = aux2 (lem4 _)
        module aux1 where
        aux2 : (a2 : ((x2 , n2) ≤ (x1 , n3)) ⊎ ((x2 , n2) ≡ suc (x1 , n3))) →
               a-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1) x2 n2
                                        (lem5 (x2 , n2) (x1 , n1) r1) n3 a2 ≡
               a (ax n1) x2 n2 r1
        aux2 (inl r2) =
          tpt2 (λ n r → a (ax n) x2 n2 r ≡ a (ax n1) x2 n2 r1)
               (Bool-is-set n1 n3) (leq-is-prop (x2 , n2) (x1 , n3) _ _) refl
        aux2 (inr e2) =
          rec⊥ (lem9 {m = _ , n2} {n = _ , n1} r1
                      (e2 ◾ tpt (λ n → suc (x1 , n) ≡ suc (x1 , n1))
                                (Bool-is-set n1 n3) refl))
    a-eq' (eq n1) = _
    a-eq-coh (eq n1) = refl

    rz-eq (eq n1) r1 = aux1 (lem2 (suc-is-nat n1))
      module rz-eq-eq where
      aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
             ! (a-eq-eq.aux1 n1 refl refl r1 a1) ◾
             rz-f-P-l-approx.aux1 ax (suc-is-nat n1)
              (lem5 z (x1 , n1) r1) a1 ≡
             rz (ax n1) r1
      aux1 (inl e1) = rec⊥ (lem8 (x1 , n1) (! (nat-eq e1)))
      aux1 (inr n2) = aux2 (lem4 _)
        module aux1 where
        aux2 : (a1 : (z ≤ (x1 , n2)) ⊎ (z ≡ suc (x1 , n2))) →
               ! (a-eq-eq.aux1.aux2 n1 refl refl r1 n2 a1) ◾
               rz-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1)
                (lem5 (refl , refl) (x1 , n1) r1) n2 a1 ≡
               rz (ax n1) r1
        aux2 (inl r2) =
          rz-coh-η-5 P z* s* ax n1 (Bool-is-set n1 n2) r1
                       (leq-is-prop z (x1 , n2) _ _)
        aux2 (inr e2) = rec⊥ (lem8 (x1 , n2) e2)

    rs-eq (eq n1) x2 n2 r1 r2 = aux1 (lem2 (suc-is-nat n1))
      module rs-eq-eq where
      aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
             rs-f-P-l-approx.aux1 ax (suc-is-nat n1) x2 n2 (lem5 (suc (x2 , n2))
                                  (x1 , n1) r1) (lem5 (x2 , n2) (x1 , n1) r2) a1 ◾
             ap (s* x2 n2) (a-eq-eq.aux1 n1 x2 n2 r2 a1) ≡
             a-eq-eq.aux1 n1 (l ◾ x2) (suc-is-nat n2) r1 a1 ◾
             rs (ax n1) x2 n2 r1 r2
      aux1 (inl e1) =
        rec⊥ (lem8 (x2 , n2)
                    (! (lem1 (tpt2 (λ x n → suc (x2 , n2) ≤ (x , n))
                                   e1 (Bool-is-set _ refl)
                                   (lem5 (suc (x2 , n2)) (x1 , n1) r1)))))
      aux1 (inr n3) = aux2 (lem4 _) (lem4 _)
        module aux1 where
        aux2 : (a2 : ((x2 , n2) ≤ (x1 , n3)) ⊎ ((x2 , n2) ≡ suc (x1 , n3))) →
               (a3 : ((l ◾ x2 , suc-is-nat n2) ≤ (x1 , n3)) ⊎
                       ((l ◾ x2 , suc-is-nat n2) ≡ suc (x1 , n3))) →
               rs-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1) x2 n2
                 (lem5 (suc (x2 , n2)) (x1 , n1) r1)
                 (lem5 (x2 , n2) (x1 , n1) r2) n3 a3 a2 ◾
               ap (s* x2 n2) (a-eq-eq.aux1.aux2 n1 x2 n2 r2 n3 a2) ≡
               a-eq-eq.aux1.aux2 n1 (l ◾ x2) (suc-is-nat n2) r1 n3 a3 ◾
               rs (ax n1) x2 n2 r1 r2
        aux2 (inl r3) (inl r4) =
          rs-coh-η-5 P z* s* ax n1 n3 (Bool-is-set n1 n3) n2
                     (leq-is-prop (x2 , n2) (x1 , n3) _ _)
                     (leq-is-prop (suc (x2 , n2)) (x1 , n3) _ _)
        aux2 (inl r3) (inr e2) =
          rec⊥ (lem9 r1 (e2 ◾ tpt (λ n → suc (x1 , n) ≡ suc (x1 , n1))
                                   (Bool-is-set n1 n3) refl))
        aux2 (inr e2) (inl r3) =
          rec⊥ (lem9 r2 (e2 ◾ tpt (λ n → suc (x1 , n) ≡ suc (x1 , n1))
                                   (Bool-is-set n1 n3) refl))
        aux2 (inr e2) (inr e3) =
          rec⊥ (lem9 r1 (e3 ◾ tpt (λ n → suc (x1 , n) ≡ suc (x1 , n1))
                                   (Bool-is-set n1 n3) refl))
      
  -----
  h (P-l approx x1) = g-P-l-approx

  -----
  ε (P-l approx x1) ax = funext (λ n1 → approx-eq (eq n1))
    module ε-P-l-approx where
    eq : (n1 : is-nat (l ◾ x1)) →
         approx-eq-data (f-P-l-approx (g-P-l-approx ax) n1) 
                        (ax n1)
    a-eq (eq n1) x2 n2 r1 = aux1 (lem2 n1)
      module a-eq-eq where
      aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
             a-f-P-l-approx.aux1 (g-P-l-approx ax) n1 x2 n2 r1 a1 ≡
             a (ax n1) x2 n2 r1
      aux1 (inl e1) =
        a-coh1 (ax n1) (lem1' n2 e1 r1) (Bool-is-set _ _)
               (leq-is-prop (x2 , n2) (l ◾ x1 , n1) _ _)
               (rz (ax n1) (lem6 (l ◾ x1 , n1))) refl
      
      aux1 (inr n3) = aux2 (lem4 _)
        module aux1 where
        aux2 : (a2 : ((x2 , n2) ≤ (x1 , n3)) ⊎ ((x2 , n2) ≡ suc (x1 , n3))) →
               a-f-P-l-approx.aux1.aux2 (g-P-l-approx ax)
                                        n1 x2 n2 r1 n3 a2 ≡
               a (ax n1) x2 n2 r1
        aux2 (inl r2) =
          a-coh2 ax _ _ (Bool-is-set _ _) x2 n2
                 (lem5 (x2 , n2) (x1 , n3) r2) r1
                 (leq-is-prop (x2 , n2) (l ◾ x1 , n1)_ _)
        aux2 (inr e2) =
          a-coh1 (ax n1) (ap fst (! e2)) (ap-snd (! e2))
                 (leq-is-prop (x2 , n2) (l ◾ x1 , n1) _ _)
                 (rs (ax n1) x1 n3
                     (tpt (λ n → suc (x1 , n3) ≤ (l ◾ x1 , n))
                          (Bool-is-set _ _)
                          (lem3 (suc (x1 , n3))))
                     (tpt (λ n → (x1 , n3) ≤ (l ◾ x1 , n))
                          (Bool-is-set _ _)
                          (lem5 (x1 , n3) (x1 , n3) (lem3 (x1 , n3)))) ◾
                  ap (s* x1 n3)
                     (a-coh2 ax _ _ (Bool-is-set _ _) x1 n3
                             (tpt (λ n → (x1 , n3) ≤ (l ◾ x1 , n))
                                  (Bool-is-set _ _)
                                  (lem5 (x1 , n3) (x1 , n3) (lem3 (x1 , n3))))
                             (lem5 (x1 , n3) (x1 , n3) (lem3 (x1 , n3)))
                             (leq-is-prop (x1 , n3) (suc (x1 , n3)) _ _))) refl
    a-eq' (eq n1) = _
    a-eq-coh (eq n1) = refl
    
    rz-eq (eq n1) r1 = aux1 (lem2 n1)
      module rz-eq-eq where
      aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
             ! (a-eq-eq.aux1 n1 refl refl r1 a1) ◾
             rz-f-P-l-approx.aux1 (g-P-l-approx ax) n1 r1 a1 ≡
             rz (ax n1) r1
      aux1 (inl e1) =
        rz-coh-ε-l-5 P z* s* ax e1 n1
                     (leq-is-prop z (l ◾ x1 , n1) _ _)
                     (path-s1-is-set _ _)
      aux1 (inr n2) = aux2 (lem4 _)
        module aux1 where
        aux2 : (a2 : (z ≤ (x1 , n2)) ⊎ (z ≡ suc (x1 , n2))) →
               ! (a-eq-eq.aux1.aux2 n1 refl refl r1 n2 a2) ◾
               rz-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) n1 r1 n2 a2 ≡
               rz (ax n1) r1
        aux2 (inl r2) =
          rz-coh-ε-r-5 P z* s* ax n2 (Bool-is-set (suc-is-nat n2) n1) r1 r2
        aux2 (inr e2) = rec⊥ (lem8 (x1 , n2) e2)
      
    rs-eq (eq n1) x2 n2 r1 r2 = aux1 (lem2 n1)
      module rs-eq-eq where
      aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
             rs-f-P-l-approx.aux1 (g-P-l-approx ax) n1 x2 n2 r1 r2 a1 ◾
             ap (s* x2 n2) (a-eq-eq.aux1 n1 x2 n2 r2 a1) ≡
             a-eq-eq.aux1 n1 (l ◾ x2) (suc-is-nat n2) r1 a1 ◾
             rs (ax n1) x2 n2 r1 r2
      aux1 (inl e1) =
        rec⊥ (lem8 (x2 , n2)
                    (! (lem1 (tpt2 (λ x n → suc (x2 , n2) ≤ (x , n))
                                   e1 (Bool-is-set _ refl) r1))))
      aux1 (inr n3) = aux2 (lem4 _) (lem4 _)
        module aux1 where
        aux2 : (a2 : ((l ◾ x2 , suc-is-nat n2) ≤ (x1 , n3)) ⊎
                     ((l ◾ x2 , suc-is-nat n2) ≡ suc (x1 , n3))) →
               (a3 : ((x2 , n2) ≤ (x1 , n3)) ⊎ ((x2 , n2) ≡ suc (x1 , n3))) →
               rs-f-P-l-approx.aux1.aux2 (g-P-l-approx ax)
                                         n1 x2 n2 r1 r2 n3 a2 a3 ◾
               ap (s* x2 n2) (a-eq-eq.aux1.aux2 n1 x2 n2 r2 n3 a3) ≡
               a-eq-eq.aux1.aux2 n1 (l ◾ x2) (suc-is-nat n2) r1 n3 a2 ◾
               rs (ax n1) x2 n2 r1 r2
        aux2 (inl r3) (inl r4) =
          rs-coh-ε-l-5 P z* s* ax n3 {n1} (Bool-is-set (suc-is-nat n3) n1)
                                  n2 r1 r2 r3 r4
        aux2 (inl e3) (inr r3) =
          rec⊥ (lem9 (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n3) e3) (ap suc r3))
        aux2 (inr e2) (inl r3) =
          rs-coh-ε-r-5 P z* s* ax n3 (g lwhisk-eqv (ap fst (! e2))) (ap fst (! e2))
                       (ε lwhisk-eqv (ap fst (! e2)))
                       (Bool-is-set _ _) (Bool-is-set _ _) (ap-snd (! e2))
                       (prop-is-set Bool-is-set _ _) r1 r2 r3
        aux2 (inr e2) (inr e3) = rec⊥ (lem9 (lem3 (x2 , n2)) (e3 ◾ ! e2))


module _ (P  : (n : N) → Set l1)
         (z* : P z)
         (s* : (n : N) → P n → P (suc n))
         where

  open ApproximationBase (λ x n → P (x , n)) z* (λ x n → s* (x , n))
  open is-approx
  open SectionOnLoopS1 (approx (λ x n → P (x , n)) z* (λ x n → s* (x , n)))
       hiding (P)

  indN : (n : N) → P n
  indN (x , n) = a (s x n) x n (lem3 (x , n))

  indN-z : indN z ≡ z*
  indN-z = rz (s refl refl) refl

  indN-s : (n : N) → indN (suc n) ≡ s* n (indN n)
  indN-s (x , n) = rs (s (l ◾ x) (suc-is-nat n)) x n
                      (lem3 (suc (x , n)))
                      (lem5 (x , n) (x , n) (lem3 (x , n))) ◾
                   ap (s* (x , n))
                      (ap (λ f → a (f (suc-is-nat n)) x n
                                    (lem5 (x , n) (x , n) (lem3 (x , n))))
                          (cmpt x) ◾
                      aux1 (lem2 (suc-is-nat n)))
    module indN-s where
    aux1 : (a1 : (l ◾ x ≡ refl) ⊎ is-nat x) →
           a-f-P-l-approx.aux1 (s x) (suc-is-nat n) x n
                               (lem5 (x , n) (x , n) (lem3 (x , n))) a1 ≡
           indN (x , n)
    aux1 (inl e) = rec⊥ (lem9 {m = _ , refl} (lem6 (x , n)) (nat-eq (! e)))
    aux1 (inr n2) =
      aux2 (lem4 {m = _ , n} {n = _ , n2}
           (tpt (λ n3 → (x , n) ≤ (l ◾ x , n3)) (Bool-is-set _ _)
           (lem5 (x , n) (x , n) (lem3 (x , n)))))
      module aux1 where
      aux2 : (a2 : ((x , n) ≤ (x , n2)) ⊎ ((x , n) ≡ suc (x , n2))) →
             a-f-P-l-approx.aux1.aux2 (s x) (suc-is-nat n) x n
               (lem5 (x , n) (x , n) (lem3 (x , n))) n2 a2 ≡ indN (x , n)
      aux2 (inl r) = a-coh2 (s x) n2 n (Bool-is-set _ _) x n
                            r (lem3 (x , n)) (leq-is-prop (x , n) (x , n) _ _)
      aux2 (inr e) =
        rec⊥ (lem9 (tpt (λ n3 → (x , n) ≤ (x , n3))
                         (Bool-is-set _ _) (lem3 (x , n))) e)
