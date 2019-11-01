{-# OPTIONS --without-K --rewriting #-}
module ApproximationCoherence where

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


open _≃_
open EquivCoh


{- TODO: Clean up formatting -}

module _ (P  : (x : b ≡ b) → (n : is-nat x) → Set l1)
         (z* : P refl refl)
         (s* : (x : b ≡ b) → (n : is-nat x) → P x n → P (l ◾ x) (suc-is-nat n))
         where
         
 open ApproximationBase P z* s*
 open is-approx

 module _ {x1 : b ≡ b}
          (ax : (n : is-nat (l ◾ x1)) → is-approx (l ◾ x1 , n))
          (n1 : is-nat x1)
          where
          
  rs-coh-ε-r-1 : {p : P (l ◾ x1) (suc-is-nat n1)} →
                 (e1 : a (ax (suc-is-nat n1)) (l ◾ x1)
                 (suc-is-nat n1) (lem3 (suc (x1 , n1))) ≡ p) →
                 refl ≡
                 a-coh1 (ax (suc-is-nat n1)) refl refl refl (e1 ◾ refl) refl ◾ e1
  rs-coh-ε-r-1 refl = refl
  
  rs-coh-ε-r-2 : (e1 : refl ≡ refl) → (e2 : e1 ≡ refl) →
            (e3 : lem3 (x1 , n1) ≡ lem3 (x1 , n1)) → (e4 : e3 ≡ refl) →
            (e5 : lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)) ≡
                  lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))) → (e6 : e5 ≡ refl) →
            (e6 : lem3 (suc (x1 , n1)) ≡ lem3 (suc (x1 , n1))) → (e7 : e6 ≡ refl) →
            s*-a-coh1 (g-P-l-approx ax n1) refl refl refl refl refl e1
              e3
              refl refl
              (a-coh1 (g-P-l-approx ax n1) refl refl
               e3
               refl refl)
              ◾
              ap (s* x1 n1)
              (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl x1 n1
               (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
               (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
               e5)
              ≡
              a-coh1 (ax (suc-is-nat n1)) refl refl
              e6
              (rs (ax (suc-is-nat n1)) x1 n1 (lem3 (suc (x1 , n1)))
               (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
               ◾
               ap (s* x1 n1)
               (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl x1 n1
                (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
                (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
                e5))
              refl
              ◾
              rs (ax (suc-is-nat n1)) x1 n1 (lem3 (suc (x1 , n1)))
              (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
  rs-coh-ε-r-2 e1 refl e3 refl e5 refl e6 refl =
    rs-coh-ε-r-1 (rs (ax (suc-is-nat n1)) x1 n1 (lem3 (suc (x1 , n1)))
                    (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
  
  rs-coh-ε-r-3 : (e1 : n1 ≡ n1) → (e2 : e1 ≡ refl) →
            (e3 : f (tpt-nat-suc refl refl refl) (! e1 ◾ refl ◾ e1) ≡ refl) →
            (e4 : suc-is-nat n1 ≡ suc-is-nat n1) → (e5 : e4 ≡ refl) →
            s*-a-coh1 (g-P-l-approx ax n1) refl refl refl
             (! e1 ◾ refl ◾ e1) refl e3
             (leq-is-prop (x1 , n1) (x1 , n1)
              (tpt2 (λ x n → (x , n) ≤ (x1 , n1)) refl
               (! e1 ◾ refl ◾ e1)
               (lem3 (x1 , n1)))
              (lem3 (x1 , n1)))
             refl refl
             (a-coh1 (g-P-l-approx ax n1) refl
              (! e1 ◾ refl ◾ e1)
              (leq-is-prop (x1 , n1) (x1 , n1)
               (tpt2 (λ x n → (x , n) ≤ (x1 , n1)) refl
                (! e1 ◾ refl ◾ e1)
                (lem3 (x1 , n1)))
               (lem3 (x1 , n1)))
              refl refl)
             ◾
             ap (s* x1 n1)
             (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
              e4 x1 n1
              (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
              (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
              (leq-is-prop (x1 , n1) (l ◾ x1 , suc-is-nat n1)
               (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                e4
                (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
               (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))))
             ≡
             a-coh1 (ax (suc-is-nat n1)) refl refl
             (leq-is-prop (l ◾ x1 , suc-is-nat n1) (l ◾ x1 , suc-is-nat n1)
              (tpt (λ n → suc (x1 , n1) ≤ (l ◾ x1 , n))
               e4
               (lem3 (suc (x1 , n1))))
              (lem3 (suc (x1 , n1))))
             (rs (ax (suc-is-nat n1)) x1 n1
              (tpt (λ n → suc (x1 , n1) ≤ (l ◾ x1 , n))
               e4
               (lem3 (suc (x1 , n1))))
              (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
               e4
               (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
              ◾
              ap (s* x1 n1)
              (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
               e4 x1 n1
               (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                e4
                (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
               (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
               (leq-is-prop (x1 , n1) (suc (x1 , n1))
                (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                 e4
                 (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                  e4
                  (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))))
                (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))))
             refl
             ◾
             rs (ax (suc-is-nat n1)) x1 n1 (lem3 (suc (x1 , n1)))
             (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
  rs-coh-ε-r-3 e1 refl e3 e4 refl =
    rs-coh-ε-r-2 e3 (prop-is-set (prop-is-set Bool-is-set) e3 refl)
            (leq-is-prop (x1 , n1) (x1 , n1) (lem3 (x1 , n1)) (lem3 (x1 , n1)))
            (prop-is-set (leq-is-prop (x1 , n1) (x1 , n1))
                         (leq-is-prop (x1 , n1) (x1 , n1)
                                      (lem3 (x1 , n1)) (lem3 (x1 , n1))) refl)
            (leq-is-prop (x1 , n1) (suc (x1 , n1))
                         (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
                         (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
            (prop-is-set (leq-is-prop (x1 , n1) (l ◾ x1 , suc-is-nat n1)) _ refl)
            (leq-is-prop (suc (x1 , n1)) (suc (x1 , n1))
                         (lem3 (suc (x1 , n1))) (lem3 (suc (x1 , n1))))
            (prop-is-set (leq-is-prop (suc (x1 , n1)) (suc (x1 , n1))) _ refl)
  
  rs-coh-ε-r-4 : (e1 : x1 ≡ x1) → (e2 : e1 ≡ refl) →
                 (e3 : ap fl e1 ≡ refl) →
                 (e4 : tpt (λ e → ap fl e ≡ refl) e2 e3 ≡ refl) →
                 (r1 : suc (x1 , n1) ≤ (l ◾ x1 , suc-is-nat n1)) →
                 lem3 (suc (x1 , n1)) ≡ r1 →
                 (r2 : (x1 , n1) ≤ (l ◾ x1 , suc-is-nat n1)) →
                 lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)) ≡ r2 →
                 (r3 : (x1 , n1) ≤ (x1 , n1)) → lem3 (x1 , n1) ≡ r3 →
                 s*-a-coh1
                   (g-P-l-approx ax n1) e1 refl e3
                   (g (tpt-nat-suc e1 refl e3) refl)
                   refl
                   (ε' (tpt-nat-suc e1 refl e3)
                    refl)
                   (leq-is-prop (x1 , n1) (x1 , n1)
                    (tpt2 (λ x n → (x , n) ≤ (x1 , n1)) e1
                     (g (tpt-nat-suc e1 refl e3) refl)
                     (lem3 (x1 , n1)))
                    r3)
                   refl refl
                   (a-coh1 (g-P-l-approx ax n1) e1
                    (g (tpt-nat-suc e1 refl e3) refl)
                    (leq-is-prop (x1 , n1) (x1 , n1)
                     (tpt2 (λ x n → (x , n) ≤ (x1 , n1)) e1
                      (g (tpt-nat-suc e1 refl e3) refl)
                      (lem3 (x1 , n1)))
                     r3)
                    refl refl) ◾
                   ap (s* x1 n1)
                   (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
                    (Bool-is-set (suc-is-nat n1) (suc-is-nat n1)) x1 n1
                    (lem5 (x1 , n1) (x1 , n1) r3) r2
                    (leq-is-prop (x1 , n1) (l ◾ x1 , suc-is-nat n1)
                     (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                      (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                      (lem5 (x1 , n1) (x1 , n1) r3))
                     r2))
                   ≡
                   a-coh1 (ax (suc-is-nat n1)) refl refl
                   (leq-is-prop (l ◾ x1 , suc-is-nat n1) (l ◾ x1 , suc-is-nat n1)
                    (tpt (λ n → suc (x1 , n1) ≤ (l ◾ x1 , n))
                     (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                     (lem3 (suc (x1 , n1))))
                    r1)
                   (rs (ax (suc-is-nat n1)) x1 n1
                    (tpt (λ n → suc (x1 , n1) ≤ (l ◾ x1 , n))
                     (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                     (lem3 (suc (x1 , n1))))
                    (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                     (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                     (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))) ◾
                    ap (s* x1 n1)
                    (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
                     (Bool-is-set (suc-is-nat n1) (suc-is-nat n1)) x1 n1
                     (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                      (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                      (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
                     (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
                     (leq-is-prop (x1 , n1) (suc (x1 , n1))
                      (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                       (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                       (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                        (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
                        (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))))
                      (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))))
                   refl
                   ◾ rs (ax (suc-is-nat n1)) x1 n1 r1 r2
  rs-coh-ε-r-4 e1 refl e3 refl r1 refl r2 refl r3 refl =
     rs-coh-ε-r-3 (Bool-is-set n1 n1) (prop-is-set Bool-is-set _ refl)
             (ε' (eqv-embed (is-nat-eqv n1)) refl)
             (Bool-is-set (suc-is-nat n1) (suc-is-nat n1))
             (prop-is-set Bool-is-set _ refl) 
    
  rs-coh-ε-r-5 : {x2 : b ≡ b} → (e1 : x1 ≡ x2) → (e2 : l ◾ x1 ≡ l ◾ x2) →
                 (e3 : ap fl e1 ≡ e2) →
                 {n3 : is-nat (l ◾ x1)} → 
                 {n2 : is-nat x2} → (e7 : suc-is-nat n1 ≡ n3) →
                 (e4 : tpt is-nat e1 n1 ≡ n2) →
                 (e5 : tpt is-nat e2 (suc-is-nat n1) ≡ suc-is-nat n2) →
                 (e6 : f (tpt-nat-suc e1 e2 e3) e4 ≡ e5) →
                 (r1 : suc (x2 , n2) ≤ (l ◾ x1 , n3)) →
                 (r2 : (x2 , n2) ≤ (l ◾ x1 , n3)) →
                 (r3 : (x2 , n2) ≤ (x1 , n1)) →
                 s*-a-coh1
                   (g-P-l-approx ax n1) (g lwhisk-eqv e2)
                   e2 (ε lwhisk-eqv e2)
                   (g (tpt-nat-suc (g lwhisk-eqv e2) e2 (ε lwhisk-eqv e2)) e5)
                   e5
                   (ε' (tpt-nat-suc (g lwhisk-eqv e2) e2 (ε lwhisk-eqv e2)) e5)
                   (leq-is-prop (x2 , n2) (x1 , n1)
                     (tpt2 (λ x n → (x , n) ≤ (x1 , n1))
                           (g lwhisk-eqv e2)
                           (g (tpt-nat-suc (g lwhisk-eqv e2) e2 (ε lwhisk-eqv e2)) e5)
                                           (lem3 (x1 , n1)))
                     r3)
                   refl
                   refl
                   (a-coh1
                     (g-P-l-approx ax n1) (g lwhisk-eqv e2)
                     (g (tpt-nat-suc (g lwhisk-eqv e2) e2 (ε lwhisk-eqv e2)) e5)
                     (leq-is-prop (x2 , n2) (x1 , n1)
                       (tpt2 (λ x n → (x , n) ≤ (x1 , n1)) (g lwhisk-eqv e2)
                             (g (tpt-nat-suc (g lwhisk-eqv e2) e2
                                             (ε lwhisk-eqv e2)) e5)
                             (lem3 (x1 , n1)))
                       r3)
                     refl
                     refl) ◾
                 ap (s* x2 n2)
                    (a-coh2 ax (suc-is-nat n1) n3 (Bool-is-set (suc-is-nat n1) n3) x2
                            n2 (lem5 (x2 , n2) (x1 , n1) r3) r2
                            (leq-is-prop (x2 , n2) (l ◾ x1 , n3)
                              (tpt (λ n → (x2 , n2) ≤ (l ◾ x1 , n))
                                   (Bool-is-set (suc-is-nat n1) n3)
                                   (lem5 (x2 , n2) (x1 , n1) r3))
                              r2))
                 ≡
                 a-coh1
                   (ax n3) e2 e5
                   (leq-is-prop (l ◾ x2 , suc-is-nat n2) (l ◾ x1 , n3)
                                (tpt2 (λ x n → (x , n) ≤ (l ◾ x1 , n3)) e2 e5
                                      (tpt (λ n → suc (x1 , n1) ≤ (l ◾ x1 , n))
                                      (Bool-is-set (suc-is-nat n1) n3)
                                      (lem3 (suc (x1 , n1)))))
                                r1)
                   (rs (ax n3) x1 n1
                       (tpt (λ n → suc (x1 , n1) ≤ (l ◾ x1 , n))
                            (Bool-is-set (suc-is-nat n1) n3) (lem3 (suc (x1 , n1))))
                       (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                            (Bool-is-set (suc-is-nat n1) n3)
                            (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))) ◾
                    ap (s* x1 n1)
                       (a-coh2
                         ax n3 (suc-is-nat n1)
                         (Bool-is-set n3 (suc-is-nat n1)) x1 n1
                         (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                              (Bool-is-set (suc-is-nat n1) n3)
                              (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))
                         (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))
                       (leq-is-prop (x1 , n1) (suc (x1 , n1))
                                    (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                                         (Bool-is-set n3 (suc-is-nat n1))
                                         (tpt (λ n → (x1 , n1) ≤ (l ◾ x1 , n))
                                              (Bool-is-set (suc-is-nat n1) n3)
                                    (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1)))))
                                    (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))))))
                   refl ◾
                   rs (ax n3) x2 n2 r1 r2
  rs-coh-ε-r-5 {x2} refl e2 refl {n3} refl refl e5 refl r1 r2 r3 =
    rs-coh-ε-r-4 (g (lwhisk-eqv {e1 = l}) refl)
                 (η (lwhisk-eqv {e1 = l}) refl) (ε lwhisk-eqv refl)
                 (tpt-fn-eq-const (ap fl) refl
                  (η (lwhisk-eqv {e1 = l}) refl) (ε lwhisk-eqv refl) ◾
                  g (eqv-adj (!e (lcomp-eqv _))) (! (lwhisk-τ refl) ◾ ! ◾unitr))
                 r1 (leq-is-prop (suc (x1 , n1)) (suc (x1 , n1))
                    (lem3 (suc (x1 , n1))) r1)
                 r2 (leq-is-prop (x1 , n1) (suc (x1 , n1))
                    (lem5 (x1 , n1) (x1 , n1) (lem3 (x1 , n1))) r2)
                 r3 (leq-is-prop (x1 , n1) (x1 , n1) (lem3 (x1 , n1)) r3)

  rs-coh-ε-l-2 : {x2 : b ≡ b} → (n2 : is-nat x2) →
                 (r3 : suc (x2 , n2) ≤ (x1 , n1)) →
                 (r4 : (x2 , n2) ≤ (x1 , n1)) →
                 {e1 : lem5 (x2 , n2) (x1 , n1) r4 ≡ lem5 (x2 , n2) (x1 , n1) r4} →
                 (e2 : e1 ≡ refl) →
                 {e3 : lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3 ≡
                       lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3} →
                 (e4 : e3 ≡ refl) →
                 rs-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) (suc-is-nat n1) x2 n2
                  (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3)
                  (lem5 (x2 , n2) (x1 , n1) r4) n1 (inl r3) (inl r4)
                  ◾
                  ap (s* x2 n2)
                  (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl x2 n2
                   (lem5 (x2 , n2) (x1 , n1) r4) (lem5 (x2 , n2) (x1 , n1) r4)
                   e1)
                  ≡
                  a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl (l ◾ x2)
                  (suc-is-nat n2) (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3)
                  (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3)
                  e3
                  ◾
                  rs (ax (suc-is-nat n1)) x2 n2
                  (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3)
                  (lem5 (x2 , n2) (x1 , n1) r4)
  rs-coh-ε-l-2 {x2} n2 r3 r4 refl refl = ◾unitr ◾ ! ◾unitl
  
  rs-coh-ε-l-3 : {x2 : b ≡ b} → (n2 : is-nat x2) →
                 (r3 : suc (x2 , n2) ≤ (x1 , n1)) →
                 {r1 : suc (x2 , n2) ≤ suc (x1 , n1)} →
                 (e1 : lem5 (suc (x2 , n2)) (x1 , n1) r3 ≡ r1) →
                 (r4 : (x2 , n2) ≤ (x1 , n1)) →
                 {r2 : (x2 , n2) ≤ suc (x1 , n1)} →
                 (e2 : lem5 (x2 , n2) (x1 , n1) r4 ≡ r2) →
                 rs-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) (suc-is-nat n1) x2 n2
                  r1 r2 n1 (inl r3) (inl r4)
                  ◾
                  ap (s* x2 n2)
                  (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl x2 n2
                   (lem5 (x2 , n2) (x1 , n1) r4) r2
                   (leq-is-prop (x2 , n2) (l ◾ x1 , suc-is-nat n1)
                    (lem5 (x2 , n2) (x1 , n1) r4) r2))
                  ≡
                  a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl (l ◾ x2)
                  (suc-is-nat n2) (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3) r1
                  (leq-is-prop (l ◾ x2 , suc-is-nat n2) (l ◾ x1 , suc-is-nat n1)
                   (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3) r1)
                  ◾ rs (ax (suc-is-nat n1)) x2 n2 r1 r2
  rs-coh-ε-l-3 {x2} n2 r3 refl r4 refl =
    rs-coh-ε-l-2 n2 r3 r4
                 (prop-is-set (leq-is-prop (x2 , n2) (suc (x1 , n1))) _ _)
                 (prop-is-set (leq-is-prop (suc (x2 , n2)) (suc (x1 , n1))) _ _)

  rs-coh-ε-l-4 : {x2 : b ≡ b} → (n2 : is-nat x2) →
                 (r1 : suc (x2 , n2) ≤ suc (x1 , n1)) →
                 (r2 : (x2 , n2) ≤ suc (x1 , n1)) →
                 (r3 : suc (x2 , n2) ≤ (x1 , n1)) →
                 (r4 : (x2 , n2) ≤ (x1 , n1)) →
                 (e1 : suc-is-nat n1 ≡ suc-is-nat n1) → (e2 : e1 ≡ refl) →
                 rs-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) (suc-is-nat n1) x2 n2
                  r1 r2 n1 (inl r3) (inl r4)
                  ◾
                  ap (s* x2 n2)
                  (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
                   e1 x2 n2
                   (lem5 (x2 , n2) (x1 , n1) r4) r2
                   (leq-is-prop (x2 , n2) (l ◾ x1 , suc-is-nat n1)
                    (tpt (λ n → (x2 , n2) ≤ (l ◾ x1 , n))
                     e1
                     (lem5 (x2 , n2) (x1 , n1) r4))
                    r2))
                  ≡
                  a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
                  e1 (l ◾ x2)
                  (suc-is-nat n2) (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3) r1
                  (leq-is-prop (l ◾ x2 , suc-is-nat n2) (l ◾ x1 , suc-is-nat n1)
                   (tpt (λ n → (l ◾ x2 , suc-is-nat n2) ≤ (l ◾ x1 , n))
                    e1
                    (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3))
                   r1)
                  ◾ rs (ax (suc-is-nat n1)) x2 n2 r1 r2
  rs-coh-ε-l-4 {x2} n2 r1 r2 r3 r4 _ refl =
    rs-coh-ε-l-3 n2 r3 (leq-is-prop (suc (x2 , n2)) (suc (x1 , n1)) _ _)
                    r4 (leq-is-prop (x2 , n2) (suc (x1 , n1)) _ _)

  rs-coh-ε-l-5 : {n3 : is-nat (l ◾ x1)} → (e1 : suc-is-nat n1 ≡ n3) →
                 {x2 : b ≡ b} → (n2 : is-nat x2) →
                 (r1 : suc (x2 , n2) ≤ (l ◾ x1 , n3)) →
                 (r2 : (x2 , n2) ≤ (l ◾ x1 , n3)) →
                 (r3 : suc (x2 , n2) ≤ (x1 , n1)) →
                 (r4 : (x2 , n2) ≤ (x1 , n1)) →
                 rs-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) n3 x2 n2 r1 r2 n1
                   (inl r3) (inl r4)
                   ◾
                   ap (s* x2 n2)
                   (a-coh2 ax (suc-is-nat n1) n3 (Bool-is-set (suc-is-nat n1) n3) x2
                    n2 (lem5 (x2 , n2) (x1 , n1) r4) r2
                    (leq-is-prop (x2 , n2) (l ◾ x1 , n3)
                     (tpt (λ n → (x2 , n2) ≤ (l ◾ x1 , n))
                      (Bool-is-set (suc-is-nat n1) n3) (lem5 (x2 , n2) (x1 , n1) r4))
                     r2))
                   ≡
                   a-coh2 ax (suc-is-nat n1) n3 (Bool-is-set (suc-is-nat n1) n3)
                   (l ◾ x2) (suc-is-nat n2)
                   (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3) r1
                   (leq-is-prop (l ◾ x2 , suc-is-nat n2) (l ◾ x1 , n3)
                    (tpt (λ n → (l ◾ x2 , suc-is-nat n2) ≤ (l ◾ x1 , n))
                     (Bool-is-set (suc-is-nat n1) n3)
                     (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n1) r3))
                    r1)
                   ◾ rs (ax n3) x2 n2 r1 r2
  rs-coh-ε-l-5 refl n2 r1 r2 r3 r4 =
    rs-coh-ε-l-4 n2 r1 r2 r3 r4 (Bool-is-set _ _) (prop-is-set Bool-is-set _ _)


  rz-coh-ε-r-2 : (r2 : z ≤ (x1 , n1)) →
                 {e1 : lem5 z (x1 , n1) r2 ≡ lem5 z (x1 , n1) r2} →
                 (e2 : e1 ≡ refl) →
                    !
                  (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl refl refl
                   (lem5 z (x1 , n1) r2) (lem5 z (x1 , n1) r2)
                   e1)
                  ◾
                  rz-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) (suc-is-nat n1)
                  (lem5 z (x1 , n1) r2) n1 (inl r2)
                  ≡ rz (ax (suc-is-nat n1)) (lem5 z (x1 , n1) r2)
  rz-coh-ε-r-2 r2 refl = ◾unitl

  rz-coh-ε-r-3 : (r2 : z ≤ (x1 , n1)) →
                 {r1 : z ≤ suc (x1 , n1)} → lem5 z (x1 , n1) r2 ≡ r1 →
                 !
                  (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1) refl refl refl
                   (lem5 z (x1 , n1) r2) r1
                   (leq-is-prop z (l ◾ x1 , suc-is-nat n1) (lem5 z (x1 , n1) r2) r1))
                  ◾
                  rz-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) (suc-is-nat n1) r1 n1
                  (inl r2)
                  ≡ rz (ax (suc-is-nat n1)) r1
  rz-coh-ε-r-3 r2 refl =
    rz-coh-ε-r-2 r2 (prop-is-set (leq-is-prop z (suc (x1 , n1))) _ _)
  
  rz-coh-ε-r-4 : (r1 : z ≤ suc (x1 , n1)) →
                 (r2 : z ≤ (x1 , n1)) →
                 {e1 : suc-is-nat n1 ≡ suc-is-nat n1} → (e2 : e1 ≡ refl) →
                 ! (a-coh2 ax (suc-is-nat n1) (suc-is-nat n1)
                    e1 refl refl
                    (lem5 z (x1 , n1) r2) r1
                    (leq-is-prop z (l ◾ x1 , suc-is-nat n1)
                     (tpt (λ n → z ≤ (l ◾ x1 , n))
                      e1
                      (lem5 z (x1 , n1) r2))
                     r1))
                   ◾
                   rz-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) (suc-is-nat n1) r1 n1
                   (inl r2)
                   ≡ rz (ax (suc-is-nat n1)) r1
  rz-coh-ε-r-4 r1 r2 refl = rz-coh-ε-r-3 r2 (leq-is-prop z (suc (x1 , n1)) _ _)

  rz-coh-ε-r-5 : {n2 : is-nat (l ◾ x1)} → (e1 : suc-is-nat n1 ≡ n2) →
                 (r1 : z ≤ (l ◾ x1 , n2)) →
                 (r2 : z ≤ (x1 , n1)) →
                 ! (a-coh2 ax (suc-is-nat n1) n2 (Bool-is-set (suc-is-nat n1) n2) refl
                   refl (lem5 z (x1 , n1) r2) r1
                   (leq-is-prop z (l ◾ x1 , n2)
                    (tpt (λ n → z ≤ (l ◾ x1 , n))
                     (Bool-is-set (suc-is-nat n1) n2) (lem5 z (x1 , n1) r2))
                    r1))
                  ◾ rz-f-P-l-approx.aux1.aux2 (g-P-l-approx ax) n2 r1 n1 (inl r2)
                  ≡ rz (ax n2) r1
  rz-coh-ε-r-5 refl r1 r2 = rz-coh-ε-r-4 r1 r2 (prop-is-set Bool-is-set _ _)
  
 module _ {x1 : b ≡ b}
          (ax : (n : is-nat (l ◾ x1)) → is-approx (l ◾ x1 , n))
          where

  rz-coh-ε-l-4 : (e1 : l ◾ x1 ≡ refl) → (n1 : is-nat (l ◾ x1)) →
                 {e2 : lem6 (l ◾ x1 , n1) ≡ lem6 (l ◾ x1 , n1)} →
                 (e3 : e2 ≡ refl) →
                 ! (a-coh1 (ax n1) refl refl
                    e2
                    (rz (ax n1) (lem6 (l ◾ x1 , n1))) refl)
                   ◾
                   tpt2-loop path-s1-is-set (λ z₁ → prop-is-set Bool-is-set) P refl
                   refl z*
                   ≡ rz (ax n1) (lem6 (l ◾ x1 , n1))
  rz-coh-ε-l-4 e1 n1 refl =
    (!-comp [2,0,1] _) ◾
    (◾unitl [2,0,1] _) ◾
    (!! [2,0,1] _) ◾
    (_ [1,0,2] tpt2-loop-β path-s1-is-set (λ z₁ → prop-is-set Bool-is-set) P) ◾
    ◾unitr
 
  rz-coh-ε-l-5 : (e1 : l ◾ x1 ≡ refl) →
                 (n1 : is-nat (l ◾ x1)) →
                   {r1 : z ≤ (l ◾ x1 , n1)} → (e2 : lem6 (l ◾ x1 , n1) ≡ r1) →
                   {e3 : refl ≡ refl} → (e4 : e3 ≡ refl) →
                   ! (a-coh1 (ax n1) e3
                     (! (BoolIsSet.enc-dec (tpt is-nat e3 refl)) ◾ refl)
                     (leq-is-prop z (l ◾ x1 , n1)
                      (tpt2 (λ x n → (x , n) ≤ (l ◾ x1 , n1)) e3
                       (! (BoolIsSet.enc-dec (tpt is-nat e3 refl)) ◾ refl)
                       (lem6 (l ◾ x1 , n1)))
                      r1)
                     (rz (ax n1) (lem6 (l ◾ x1 , n1))) refl)
                    ◾ tpt2-loop path-s1-is-set (λ _ → prop-is-set Bool-is-set) P
                                e3
                                (Bool-is-set (tpt is-nat e3 refl) refl)
                                z*
                    ≡ rz (ax n1) r1
  rz-coh-ε-l-5 e1 n1 refl refl =
    rz-coh-ε-l-4 e1 n1 (prop-is-set (leq-is-prop z (l ◾ x1 , n1))
                                    (leq-is-prop z (l ◾ x1 , n1) _ _) refl)



 module _ {x1 : b ≡ b}
          (ax : (n : is-nat x1) → is-approx (x1 , n))
          (n1 : is-nat x1)
          where

   rs-coh-η-3 : {x2 : b ≡ b} → (n2 : is-nat x2) →
                (r1 : suc (x2 , n2) ≤ (x1 , n1)) →
                (r2 : (x2 , n2) ≤ (x1 , n1)) →
                (e1 : r2 ≡ r2) → (e2 : e1 ≡ refl) →
                (e3 : r1 ≡ r1) → (e4 : e3 ≡ refl) →
                rs-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1) x2 n2
                 (lem5 (suc (x2 , n2)) (x1 , n1) r1) (lem5 (x2 , n2) (x1 , n1) r2)
                 n1 (inl r1) (inl r2)
                 ◾
                 ap (s* x2 n2)
                 (tpt2 (λ n r → a (ax n) x2 n2 r ≡ a (ax n1) x2 n2 r2) refl
                  e1 refl)
                 ≡
                 tpt2
                 (λ n r →
                    a (ax n) (l ◾ x2) (suc-is-nat n2) r ≡
                    a (ax n1) (l ◾ x2) (suc-is-nat n2) r1)
                 refl e3 refl
                 ◾ rs (ax n1) x2 n2 r1 r2
   rs-coh-η-3 {x2} n2 r1 r2 _ refl _ refl = ◾unitr ◾ ! ◾unitl

   rs-coh-η-4 : {x2 : b ≡ b} → (n2 : is-nat x2) →
                (r1 : suc (x2 , n2) ≤ (x1 , n1)) →
                (r2 : (x2 , n2) ≤ (x1 , n1)) →
                (e1 : n1 ≡ n1) → (e2 : e1 ≡ refl) →
                rs-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1) x2 n2
                 (lem5 (suc (x2 , n2)) (x1 , n1) r1) (lem5 (x2 , n2) (x1 , n1) r2)
                 n1 (inl r1) (inl r2)
                 ◾
                 ap (s* x2 n2)
                 (tpt2 (λ n r → a (ax n) x2 n2 r ≡ a (ax n1) x2 n2 r2)
                  e1
                  (leq-is-prop (x2 , n2) (x1 , n1)
                   (tpt (λ z₁ → (x2 , n2) ≤ (x1 , z₁)) e1 r2) r2)
                  refl)
                 ≡
                 tpt2
                 (λ n r →
                    a (ax n) (l ◾ x2) (suc-is-nat n2) r ≡
                    a (ax n1) (l ◾ x2) (suc-is-nat n2) r1)
                 e1
                 (leq-is-prop (l ◾ x2 , suc-is-nat n2) (x1 , n1)
                  (tpt (λ z₁ → (l ◾ x2 , suc-is-nat n2) ≤ (x1 , z₁))
                   e1 r1)
                  r1)
                 refl
                 ◾ rs (ax n1) x2 n2 r1 r2
   rs-coh-η-4 {x2} n2 r1 r2 e1 refl =
     rs-coh-η-3 n2 r1 r2
                (leq-is-prop (x2 , n2) (x1 , n1) r2 r2)
                (prop-is-set (leq-is-prop (x2 , n2) (x1 , n1)) _ _)
                (leq-is-prop (suc (x2 , n2)) (x1 , n1) r1 r1)
                (prop-is-set (leq-is-prop (suc (x2 , n2)) (x1 , n1)) _ _)

   rs-coh-η-5 : (n3 : is-nat x1) → (e1 : n1 ≡ n3) →
                {x2 : b ≡ b} → (n2 : is-nat x2) →
                {r2 : (x2 , n2) ≤ (x1 , n1)} →
                {r3 : (x2 , n2) ≤ (x1 , n3)} →
                tpt (λ n → (x2 , n2) ≤ (x1 , n)) e1 r2 ≡ r3 →
                {r1 : suc (x2 , n2) ≤ (x1 , n1)} →
                {r4 : suc (x2 , n2) ≤ (x1 , n3)} →
                tpt (λ n → suc (x2 , n2) ≤ (x1 , n)) e1 r1 ≡ r4 →
                rs-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1) x2 n2
                (lem5 (suc (x2 , n2)) (x1 , n1) r1) (lem5 (x2 , n2) (x1 , n1) r2)
                n3 (inl r4) (inl r3)
                ◾
                ap (s* x2 n2)
                (tpt2 (λ n r → a (ax n) x2 n2 r ≡ a (ax n1) x2 n2 r2)
                 (Bool-is-set n1 n3)
                 (leq-is-prop (x2 , n2) (x1 , n3)
                  (tpt (λ z₁ → (x2 , n2) ≤ (x1 , z₁)) (Bool-is-set n1 n3) r2) r3)
                 refl)
                ≡
                tpt2
                (λ n r →
                   a (ax n) (l ◾ x2) (suc-is-nat n2) r ≡
                   a (ax n1) (l ◾ x2) (suc-is-nat n2) r1)
                (Bool-is-set n1 n3)
                (leq-is-prop (l ◾ x2 , suc-is-nat n2) (x1 , n3)
                 (tpt (λ z₁ → (l ◾ x2 , suc-is-nat n2) ≤ (x1 , z₁))
                  (Bool-is-set n1 n3) r1)
                 r4)
                refl
                ◾ rs (ax n1) x2 n2 r1 r2
   rs-coh-η-5 _ refl n2 {r1} refl {r2} refl =
     rs-coh-η-4 n2 r2 r1 (Bool-is-set n1 n1) (prop-is-set Bool-is-set _ _)


   rz-coh-η-3 : (r1 : z ≤ (x1 , n1)) →
                {e1 : r1 ≡ r1} → (e2 : e1 ≡ refl) →
                    !
                 (tpt2 (λ n r → a (ax n) refl refl r ≡ a (ax n1) refl refl r1) refl
                  e1 refl)
                 ◾
                 rz-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1)
                 (lem5 z (x1 , n1) r1) n1 (inl r1)
                 ≡ rz (ax n1) r1
   rz-coh-η-3 r1 refl = ◾unitl

   rz-coh-η-4 : (r1 : z ≤ (x1 , n1)) →
                {e1 : n1 ≡ n1} → (e2 : e1 ≡ refl) →
                    !
                 (tpt2 (λ n r → a (ax n) refl refl r ≡ a (ax n1) refl refl r1)
                  e1
                  (leq-is-prop z (x1 , n1)
                   (tpt (λ z₁ → z ≤ (x1 , z₁)) e1 r1) r1)
                  refl)
                 ◾
                 rz-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1)
                 (lem5 z (x1 , n1) r1) n1 (inl r1)
                 ≡ rz (ax n1) r1
   rz-coh-η-4 r1 refl =
     rz-coh-η-3 r1 (prop-is-set (leq-is-prop z (x1 , n1))
                      (leq-is-prop z (x1 , n1) _ _) refl)
   
   rz-coh-η-5 : {n2 : is-nat x1} → (e1 : n1 ≡ n2) →
                (r1 : z ≤ (x1 , n1)) → 
                {r2 : z ≤ (x1 , n2)} → tpt (λ n → z ≤ (x1 , n)) e1 r1 ≡ r2 →
                !
                (tpt2 (λ n r → a (ax n) refl refl r ≡ a (ax n1) refl refl r1)
                 (Bool-is-set n1 n2)
                 (leq-is-prop z (x1 , n2)
                  (tpt (λ z₁ → z ≤ (x1 , z₁)) (Bool-is-set n1 n2) r1) r2)
                 refl)
                ◾
                rz-f-P-l-approx.aux1.aux2 ax (suc-is-nat n1)
                (lem5 z (x1 , n1) r1) n2 (inl r2)
                ≡ rz (ax n1) r1
   rz-coh-η-5 refl r1 refl =
     rz-coh-η-4 r1 (prop-is-set Bool-is-set (Bool-is-set _ _) refl)
