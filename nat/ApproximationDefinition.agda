{-# OPTIONS --without-K --rewriting #-}
module ApproximationDefinition where

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


open _≃_
open EquivCoh

module ApproximationBase
       (P  : (x : b ≡ b) → (n : is-nat x) → Set l1)
       (z* : P refl refl)
       (s* : (x : b ≡ b) → (n : is-nat x) → P x n → P (l ◾ x) (suc-is-nat n))
       where

  record is-approx (n1 : N) : Set l1 where
    field
      a  : (x2 : b ≡ b) → (n2 : is-nat x2) → (x2 , n2) ≤ n1 → P x2 n2 
      rz : (r : z ≤ n1) → a refl refl r ≡ z*
      rs : (x2 : b ≡ b) → (n2 : is-nat x2) →
           (r1 : suc (x2 , n2) ≤ n1) → (r2 : (x2 , n2) ≤ n1) →
           a (l ◾ x2) (suc-is-nat n2) r1 ≡ s* x2 n2 (a x2 n2 r2)

    a-coh1 : {x2 x3 : b ≡ b} → (e1 : x2 ≡ x3) →
             {n2 : is-nat x2} → {n3 : is-nat x3} →
             (e2 : tpt is-nat e1 n2 ≡ n3) →
             {r2 : (x2 , n2) ≤ n1} → {r3 : (x3 , n3) ≤ n1} →
             tpt2 (λ x n → (x , n) ≤ n1) e1 e2 r2 ≡ r3 →
             {p2 : P x2 n2} → a x2 n2 r2 ≡ p2 →
             {p3 : P x3 n3} → a x3 n3 r3 ≡ p3 →
             tpt2 P e1 e2 p2 ≡ p3
    a-coh1 refl {n2 = n2} refl refl {p2 = p2} e3 e4 = ! e3 ◾ e4

    s*-a-coh1 : {x2 x3 : b ≡ b} →
                (e1 : x2 ≡ x3) → (e2 : l ◾ x2 ≡ l ◾ x3) → (e3 : ap fl e1 ≡ e2) →
                {n2 : is-nat x2} → {n3 : is-nat x3} →
                (e4 : tpt is-nat e1 n2 ≡ n3) →
                (e5 : tpt is-nat e2 (suc-is-nat n2) ≡ suc-is-nat n3) →
                (e6 : f (tpt-nat-suc e1 e2 e3) e4 ≡ e5) →
                {r2 : (x2 , n2) ≤ n1} → {r3 : (x3 , n3) ≤ n1} →
                tpt2 (λ x n → (x , n) ≤ n1) e1 e4 r2 ≡ r3 →
                {p2 : P x2 n2} → a x2 n2 r2 ≡ p2 →
                {p3 : P x3 n3} → a x3 n3 r3 ≡ p3 →
                tpt2 P e1 e4 p2 ≡ p3 →
                tpt2 P e2 e5 (s* x2 n2 p2) ≡ s* x3 n3 p3
    s*-a-coh1 {x2} refl e2 refl {n2} refl e5 refl refl refl refl e7 = ap (s* x2 n2) e7

  open is-approx

  a-coh2 : {x1 : b ≡ b} → (ax : (n : is-nat x1) → is-approx (x1 , n)) →
           (n1 n2 : is-nat x1) → (e1 : n1 ≡ n2) →
           (x3 : b ≡ b) → (n3 : is-nat x3) →
           (r1 : (x3 , n3) ≤ (x1 , n1)) → (r2 : (x3 , n3) ≤ (x1 , n2)) →
           tpt (λ n → (x3 , n3) ≤ (x1 , n)) e1 r1 ≡ r2 →
           a (ax n1) x3 n3 r1 ≡ a (ax n2) x3 n3 r2
  a-coh2 {x1} ax n1 _ refl x3 n3 r1 _ refl = refl

  f-P-l-approx : {x1 : b ≡ b} →
                 ((n1 : is-nat x1) → is-approx (x1 , n1)) →
                 ((n1 : is-nat (l ◾ x1)) → is-approx (l ◾ x1 , n1))
  a (f-P-l-approx {x1} ax n1) x2 n2 r1 = aux1 (lem2 n1)
    module a-f-P-l-approx where
    aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) → P x2 n2
    aux1 (inl e1) = tpt2 P (lem1' n2 e1 r1) (Bool-is-set _ _) z*
    aux1 (inr n3) =
      aux2 (lem4 {m = _ , n2} {n = _ , n3}
                 (tpt (λ n → (x2 , n2) ≤ (l ◾ x1 , n)) (Bool-is-set _ _) r1))
      module aux1 where
      aux2 : (a2 : ((x2 , n2) ≤ (x1 , n3)) ⊎ ((x2 , n2) ≡ suc (x1 , n3))) → P x2 n2
      aux2 (inl r2) = a (ax n3) x2 n2 r2
      aux2 (inr e2) = tpt2 P (ap fst (! e2)) (ap-snd (! e2))
                           (s* x1 n3 (a (ax n3) x1 n3 (lem3 (x1 , n3))))
  
  rz (f-P-l-approx {x1} ax n1) r1 = aux1 (lem2 n1)
    module rz-f-P-l-approx where
    aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
           a-f-P-l-approx.aux1 ax n1 refl refl r1 a1 ≡ z*
    aux1 (inl e1) =
      tpt2-loop path-s1-is-set (λ _ → prop-is-set Bool-is-set) P
                (lem1' refl e1 r1)
                (Bool-is-set (tpt is-nat (lem1' refl e1 r1) refl) refl)
                z*
    
    aux1 (inr n2) = aux2 (lem4 _)
      module aux1 where
      aux2 : (a2 : ((refl , refl) ≤ (x1 , n2)) ⊎ ((refl , refl) ≡ suc (x1 , n2))) →
             a-f-P-l-approx.aux1.aux2 ax n1 refl refl r1 n2 a2 ≡ z*
      aux2 (inl r2) = rz (ax n2) r2
      aux2 (inr e2) = rec⊥ (lem8 (x1 , n2) e2)
  
  rs (f-P-l-approx {x1} ax n1) x2 n2 r1 r2 = aux1 (lem2 n1)
    module rs-f-P-l-approx where
    aux1 : (a1 : (l ◾ x1 ≡ refl) ⊎ is-nat x1) →
           a-f-P-l-approx.aux1 ax n1 (l ◾ x2) (suc-is-nat n2) r1 a1 ≡
           s* x2 n2 (a-f-P-l-approx.aux1 ax n1 x2 n2 r2 a1)
    aux1 (inl e1) = rec⊥ (lem8 (x2 , n2)
                                (! (lem1 (tpt2 (λ x n → suc (x2 , n2) ≤ (x , n))
                                               e1 (Bool-is-set _ refl) r1)))) 
    aux1 (inr n3) = aux2 (lem4 _) (lem4 _)
      module aux1 where
      aux2 : (a2 : (suc (x2 , n2) ≤ (x1 , n3)) ⊎ (suc (x2 , n2) ≡ suc (x1 , n3))) →
             (a3 : ((x2 , n2) ≤ (x1 , n3)) ⊎ ((x2 , n2) ≡ suc (x1 , n3))) →
             a-f-P-l-approx.aux1.aux2 ax n1 (l ◾ x2) (suc-is-nat n2) r1 n3 a2 ≡
             s* x2 n2 (a-f-P-l-approx.aux1.aux2 ax n1 x2 n2 r2 n3 a3)
      aux2 (inl r3) (inl r4) = rs (ax n3) x2 n2 r3 r4
      aux2 (inl r3) (inr e2) =
        rec⊥ (lem9 {m = _ , suc-is-nat n2} {n = _ , suc-is-nat n3}
                   (lem5 (l ◾ x2 , suc-is-nat n2) (x1 , n3) r3)
                   (ap suc e2))
      aux2 (inr e2) (inl r3) = 
        s*-a-coh1
          (ax n3) (g lwhisk-eqv (ap fst (! e2))) (ap fst (! e2))
          (ε lwhisk-eqv _)
          (g (tpt-nat-suc (g lwhisk-eqv (ap fst (! e2)))
                          (ap fst (! e2)) (ε lwhisk-eqv _))
             (ap-snd (! e2)))
          (ap-snd (! e2))
          (ε' (tpt-nat-suc (g lwhisk-eqv (ap fst (! e2)))
                           (ap fst (! e2)) (ε lwhisk-eqv (ap fst (! e2))))
              (ap-snd (! e2)))
          (leq-is-prop (x2 , n2) (x1 , n3) _ _)
          refl refl
          (a-coh1 (ax n3)
            (g lwhisk-eqv (ap fst (! e2)))
            (g (tpt-nat-suc (g lwhisk-eqv (ap fst (! e2)))
                            (ap fst (! e2)) (ε lwhisk-eqv _)) (ap-snd (! e2)))
            (leq-is-prop (x2 , n2) (x1 , n3) _ _) refl refl)
      aux2 (inr e2) (inr e3) = rec⊥ (lem9 (lem3 (x2 , n2)) (e3 ◾ ! e2))



  g-P-l-approx : {x1 : b ≡ b} →
                 ((n1 : is-nat (l ◾ x1)) → is-approx (l ◾ x1 , n1)) →
                 (n1 : is-nat x1) → is-approx (x1 , n1)                 
  a (g-P-l-approx {x1} ax n1) x2 n2 r1 =
    a (ax (suc-is-nat n1)) x2 n2 (lem5 (x2 , n2) (x1 , n1) r1)
  rz (g-P-l-approx {x1} ax n1) r1 = rz (ax (suc-is-nat n1)) (lem5 z (x1 , n1) r1)
  rs (g-P-l-approx {x1} ax n1) x2 n2 r1 r2 =
    rs (ax (suc-is-nat n1)) x2 n2 (lem5 (suc (x2 , n2)) (x1 , n1) r1)
                            (lem5 (x2 , n2) (x1 , n1) r2)


  record approx-eq-data {n1 : N} (a1 a2 : is-approx n1) : Set l1 where
    field
      a-eq : (x2 : b ≡ b) → (n2 : is-nat x2) → (r : (x2 , n2) ≤ n1) →
             a a1 x2 n2 r ≡ a a2 x2 n2 r
      a-eq' : a a1 ≡ a a2
      a-eq-coh : funext (λ x2 → funext (λ n2 → funext (λ r → a-eq x2 n2 r))) ≡
                 a-eq'

      rz-eq : (r : z ≤ n1) → ! (a-eq refl refl r) ◾ rz a1 r ≡ rz a2 r
              
      rs-eq : (x2 : b ≡ b) → (n2 : is-nat x2) →
              (r1 : suc (x2 , n2) ≤ n1) → (r2 : (x2 , n2) ≤ n1) →
              rs a1 x2 n2 r1 r2 ◾ ap (s* x2 n2) (a-eq x2 n2 r2) ≡
               a-eq (l ◾ x2) (suc-is-nat n2) r1 ◾ rs a2 x2 n2 r1 r2

  module _ {n1 : N} (a1 a2 : is-approx n1) where
    a-eq-coh' : {a-eq : (x2 : b ≡ b) → (n2 : is-nat x2) → (r : (x2 , n2) ≤ n1) →
                        a a1 x2 n2 r ≡ a a2 x2 n2 r} →
                {a-eq' : a a1 ≡ a a2} →
                (a-eq-coh : funext (λ x2 → funext (λ n2 → funext (λ r →
                              a-eq x2 n2 r))) ≡ a-eq') →
                (x2 : b ≡ b) → (n2 : is-nat x2) → (r2 : (x2 , n2) ≤ n1) →
                a-eq x2 n2 r2 ≡
                ap (λ f → f r2)
                   (ap (λ f → f n2)
                       (ap (λ f → f x2) a-eq'))
    a-eq-coh' a-eq-coh x2 n2 r =
      ap (λ f → f r)
         (f (eqv-adj (!e happly-eqv))
            (ap (λ f → f n2)
                (f (eqv-adj (!e happly-eqv))
                   (ap (λ f → f x2)
                       (f (eqv-adj (!e happly-eqv)) a-eq-coh)))))

  module _ {n1 : N} {a1 a2 : is-approx n1} where
    open approx-eq-data
    
    approx-eq : approx-eq-data a1 a2 → a1 ≡ a2
    approx-eq record { a-eq = a-eq ; a-eq' = refl ; a-eq-coh = a-eq-coh ;
                       rz-eq = rz-eq ; rs-eq = rs-eq } =
      ap (λ rz → record { a = a a2 ; rz = rz ; rs = rs a1 })
         {x2 = rz a2}
         (funext (λ r →
           ! ◾unitl ◾
           ! (f rwhisk-eqv (ap ! (a-eq-coh' a1 a2 a-eq-coh refl refl r))) ◾
           rz-eq r)) ◾
      ap (λ rs → record { a = a a2 ; rz = rz a2 ; rs = rs })
         (funext (λ x2 → funext (λ n2 → funext (λ r1 → funext (λ r2 →
           ! ◾unitr ◾
           ! (f lwhisk-eqv
                (ap (ap (s* x2 n2)) (a-eq-coh' a1 a2 a-eq-coh x2 n2 r2))) ◾
           rs-eq x2 n2 r1 r2 ◾
           f rwhisk-eqv
             (a-eq-coh' a1 a2 a-eq-coh (l ◾ x2) (suc-is-nat n2) r1) ◾
           ◾unitl)))))
