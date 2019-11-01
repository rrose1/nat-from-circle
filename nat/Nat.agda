{-# OPTIONS --without-K --rewriting #-}
module Nat where

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


open _≃_

is-nat : (x : b ≡ b) → Set
is-nat x = [ coprod-fst (seg x) ]

N : Set
N = Σ (b ≡ b) is-nat

nat-eq : {m n : N} → fst m ≡ fst n → m ≡ n
nat-eq e = pair-prop-eq (λ _ → Bool-is-set) e

N-eqv : (x : b ≡ b) → (Σ (Seg≥0 x) (λ s → seg x ≡ inr s)) ≃ (is-nat x)
N-eqv = dec-subtype-eqv seg

open Seg
D-seg-eqv : (x1 : b ≡ b) → (n1 : is-nat x1) → (x2 : b ≡ b) →
            D* (seg x1) x2 ≃ D (fst (g (N-eqv x1) n1)) x2
D-seg-eqv x1 n1 x2 = aux _ refl
  module D-seg-eqv where
  aux : (s1 : Seg<0 x1 ⊎ Seg≥0 x1) → seg x1 ≡ s1 →
        D* s1 x2 ≃ D (fst (g (N-eqv x1) n1)) x2
  aux (inl s1) e1 = rec⊥ (seg-excl x1 s1 (fst (g (N-eqv x1) n1)))
  aux (inr s1) e1 = tpt-eqv (λ s → D s x2) (inr-eq (! e1 ◾ (snd (g (N-eqv x1) n1))))

nat-out : {x : b ≡ b} → is-nat x → Σ (Seg≥0 x) (λ s → seg x ≡ inr s)
nat-out {x} = g (N-eqv x)

nat-in : {x : b ≡ b} → Seg≥0 x → is-nat x
nat-in {x} s1 = aux _ refl
  module nat-in where
  aux : (a : Seg<0 x ⊎ Seg≥0 x) → seg x ≡ a → is-nat x
  aux (inl s2) = rec⊥ (seg-excl x s2 s1)
  aux (inr s2) e = f (N-eqv x) (s2 , e)


suc-is-nat : {x : b ≡ b} → is-nat x → is-nat (l ◾ x)
suc-is-nat {x} n = aux _ refl
  module suc-is-nat where
  aux : (s : Seg<0 (l ◾ x) ⊎ Seg≥0 (l ◾ x)) → seg (l ◾ x) ≡ s → [ coprod-fst s ]
  aux (inl s2) = rec⊥ (seg-excl (l ◾ x) s2
                       (f (shift-seg≥0 (l ◾ x))
                          (inr (f (incr-max-eqv x) (fst (nat-out n))))))
  aux (inr _) _ = refl

is-nat-eqv : {x : b ≡ b} → is-nat x → is-nat x ≃ is-nat (l ◾ x)
f (is-nat-eqv {x} n) = suc-is-nat
g (is-nat-eqv {x} n) _ = n
η (is-nat-eqv {x} n) = Bool-is-set n
h (is-nat-eqv {x} n) = g (is-nat-eqv {x} n)
ε (is-nat-eqv {x} n) = Bool-is-set (suc-is-nat n)

module _ where
  tpt-nat-suc : {x1 x2 : b ≡ b} →
                (e1 : x1 ≡ x2) → (e2 : l ◾ x1 ≡ l ◾ x2) → ap fl e1 ≡ e2 →
                {n1 : is-nat x1} → {n2 : is-nat x2} →
                (tpt is-nat e1 n1 ≡ n2) ≃
                (tpt is-nat e2 (suc-is-nat n1) ≡ suc-is-nat n2)
  tpt-nat-suc refl e2 refl {n1} = eqv-embed (is-nat-eqv n1)

suc : N → N
suc (x , n) = (l ◾ x , suc-is-nat n)

z : N
z = refl , refl


module _ {x1 : b ≡ b} where
  open Seg
  
  D-suc : {n1 : is-nat x1} → {x2 : b ≡ b} →
            D (fst (nat-out n1)) x2 → D (fst (nat-out (suc-is-nat n1))) x2
  D-suc {n1} {x2} d = aux _ refl
    module D-suc where
    aux : (s1 : Seg≠ (l ◾ x1) refl (lcomp-eqv l) ⊎ Seg refl (l ◾ x1) (lcomp-eqv l)) →
          (β1 : seg (l ◾ x1) ≡ s1) →
          D (fst (g-dec-subtype-eqv.aux seg (l ◾ x1) (suc-is-nat n1) s1 β1 (suc-is-nat.aux n1 s1 β1))) x2 
    aux (inl s1) _ = rec⊥ (seg-excl (l ◾ x1) s1 (f (shift-seg≥0 (l ◾ x1)) (inr (f (incr-max-eqv x1) (fst (nat-out n1))))))
    aux (inr s1) β1 = tpt (λ s → D* s x2) (! (seg-cmpt x1) ◾ β1) (D*-incr {x1} {seg x1} {fst (nat-out n1)} {x2} (tpt (λ s → D* s x2) (! (snd (nat-out n1))) d))

  D-pred : {n1 : is-nat x1} → {x2 : b ≡ b} →
           D (fst (nat-out (suc-is-nat n1))) x2 →
           D (fst (nat-out n1)) x2 ⊎ (x2 ≡ l ◾ x1)
  D-pred {n1} {x2} = aux1 _ refl
    module D-pred where
    aux1 : (s1 : Seg<0 (l ◾ x1) ⊎ Seg≥0 (l ◾ x1)) → (β1 : seg (l ◾ x1) ≡ s1) →
          D (fst (g-dec-subtype-eqv.aux seg (l ◾ x1) (suc-is-nat n1) s1 β1 (suc-is-nat.aux n1 s1 β1))) x2 →
          D (fst (nat-out n1)) x2 ⊎ (x2 ≡ l ◾ x1)
    aux1 (inl s1) β1 = rec⊥ (seg-excl (l ◾ x1) s1 (f (shift-seg≥0 (l ◾ x1)) (inr (f (incr-max-eqv x1) (fst (nat-out n1))))))
    aux1 (inr s1) β1 d1 = aux2 _ refl n1 (tpt (λ s → D* s x2) (! β1 ◾ seg-cmpt x1) d1)
      module aux1 where
      aux2 : (s2 : Seg<0 x1 ⊎ Seg≥0 x1) → seg x1 ≡ s2 → [ coprod-fst s2 ] →
             D* (incr s2) x2 → D (fst (nat-out n1)) x2 ⊎ (x2 ≡ l ◾ x1)
      aux2 (inl s2) β2 ()
      aux2 (inr s2) β2 _ (inl d2) = inl (tpt (λ s → D* s x2) (! β2 ◾ snd (nat-out n1)) d2)
      aux2 (inr s2) β2 _ (inr (_ , e1)) = inr (dec-dne (path-s1-has-dec-eq x2 (l ◾ x1)) (nn-map (f (eqv-adj (!e leqv))) e1))



module _ where

  open SubEqv
  open Seg
  open SectionOnLoopS1
  
  infix 4 _≤_
  _≤_ : (m n : N) → Set
  (x , m) ≤ (y , n) = D (fst (nat-out n)) x

  leq-is-prop : (m n : N) → is-prop (m ≤ n)
  leq-is-prop (x1 , n1) (x2 , n2) =
    is-prop-retr (retr (f (D-seg-eqv x2 n2 x1))
                       (h (D-seg-eqv x2 n2 x1))
                       (ε (D-seg-eqv x2 n2 x1)))
                 (s D-seg-is-prop x2 x1)

  lem1 : {n : N} → n ≤ z → n ≡ z
  lem1 {x , n} d = nat-eq d

  lem1' : {x1 : b ≡ b} → (n1 : is-nat x1) → {n2 : N} → fst n2 ≡ refl →
          (x1 , n1) ≤ n2 → refl ≡ x1
  lem1' n1 refl d = ! d

  lem2 : {x : b ≡ b} → is-nat (l ◾ x) → (l ◾ x ≡ refl) ⊎ is-nat x
  lem2 {x} n = aux1 (seg x)
    module lem2 where
    aux1 : (a1 : Seg<0 x ⊎ Seg≥0 x) → (l ◾ x ≡ refl) ⊎ is-nat x
    aux1 (inl s1) = aux2 (g (shift-seg≥0 (l ◾ x)) (fst (nat-out n)))
      module aux1 where
      open Seg=
      aux2 : Seg+0 (l ◾ x) ⊎ Seg>0 (l ◾ x) → (l ◾ x ≡ refl) ⊎ is-nat x
      aux2 (inl s3) =
        inl (dec-dne (path-s1-has-dec-eq (l ◾ x) refl) (nn-map ! (nx s3)))
      aux2 (inr s3) = rec⊥ (seg-excl x s1 (g (incr-max-eqv x) s3))
    aux1 (inr s1) = inr (nat-in s1)

  lem3 : (n : N) → n ≤ n
  lem3 (x , n) = Seg.dmax (fst (nat-out n))

  lem4 : {m n : N} → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
  lem4 {x1 , n1} {x2 , n2} d =
    f (ide _ ⊎e pair-prop-eqv (λ _ → Bool-is-set)) (D-pred {x2} {n2} {x1} d)

  lem5 : (m n : N) → m ≤ n → m ≤ suc n
  lem5 (x1 , _) (x2 , n2) d = aux _ refl
    module lem5 where
    aux : (s1 : Seg<0 (l ◾ x2) ⊎ Seg≥0 (l ◾ x2)) → (β1 : seg (l ◾ x2) ≡ s1) →
          D (fst (g-dec-subtype-eqv.aux seg (l ◾ x2)
                   (suc-is-nat n2) s1 β1 (suc-is-nat.aux n2 s1 β1))) x1
    aux (inl s1) _ =
      rec⊥ (seg-excl (l ◾ x2) s1 (f (shift-seg≥0 (l ◾ x2))
                                     (inr (f (incr-max-eqv x2) (fst (nat-out n2))))))
    aux (inr s1) β1 = tpt (λ s → D* s x1)
                          (! (seg-cmpt x2) ◾ β1)
                          (D*-incr {x2} {seg x2} {fst (nat-out n2)} {x1}
                                   (tpt (λ s → D* s x1) (! (snd (nat-out n2))) d))

  lem6 : (n : N) → z ≤ n
  lem6 (x , n) = dmin (fst (nat-out n))

  lem7 : {m n : N} → suc m ≤ n → m ≤ n
  lem7 {x1 , n1} {x2 , n2} d =
    fst (g (up (fst (nat-out n2))) (d ,
      mn (fst (nat-out n2)) d (λ e →
        Seg.bm1 (fst (nat-out n1))
                (tpt (D (fst (nat-out n1)))
                     (f (eqv-adj leqv) (! e))
                     (dmax (fst (nat-out n1)))))))


  lem8 : (n : N) → z ≢ suc n
  lem8 (x , n) e =
    Seg≠.st (f (incr-max-eqv x) (fst (nat-out n)))
            {d1 = Seg≠.dmin (f (incr-max-eqv x) (fst (nat-out n)))}
            {d2 = Seg≠.dmax (f (incr-max-eqv x) (fst (nat-out n)))}
            (Seg≠.r0 (f (incr-max-eqv x) (fst (nat-out n)))) (ap fst e)

  lem9 : {m n : N} → m ≤ n → m ≢ suc n
  lem9 {x1 , n1} {x2 , n2} d e =
    Seg.om1 (fst (nat-out n2)) (tpt (D (fst (nat-out n2))) (ap fst e) d)
