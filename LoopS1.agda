{-# OPTIONS --without-K --rewriting #-}
module LoopS1 where

open import UTT
open import S1


module TransportOverLoop {X : Set l1} where
  tpt-fp-eqv : {x1 x2 x3 : X} → (P : x1 ≡ x2 → Set l2) →
               (e1 : x1 ≡ x3) → (e2 : x3 ≡ x2) →
               (tpt (λ a → a ≡ x2 → Set l2) e1 P e2) ≃ (P (e1 ● e2))
  tpt-fp-eqv {x1} P refl refl = ide _

  tpt-loop-eqv : {x0 : X} → (l : x0 ≡ x0) →
                 (P : x0 ≡ x0 → Set l2) → ((e : x0 ≡ x0) → P e ≃ P (l ● e)) ≃
                 (tpt (λ a → a ≡ x0 → Set l2) l P ≡ P)
  tpt-loop-eqv l P = !e fam-eqv ∘e
                     pi-eqv-2 (λ x → ∘e-precomp-eqv (tpt-fp-eqv P l x) ∘e !e-eqv)

open TransportOverLoop public


module LoopS1IsAZModel where

  Z = (b ≡ b)
  
  zero : Z
  zero = refl

  e : Z ≃ Z
  e = lcomp-eqv l

  module _ {P : Z → Set l1} (z* : P zero) (e* : (m : Z) → P m ≃ P (f e m)) where
    P^ : {a : S1} → (a ≡ b) → Set l1
    P^ {a} = ind-s1 (λ a → a ≡ b → Set l1) P (f (tpt-loop-eqv l P) e*) a

    indZ : (m : Z) → P m
    indZ = aux {b}
      module indZ where
      aux : {a : S1} → (e : a ≡ b) → P^ {a} e
      aux refl = z*
      
    indZ-zero : indZ zero ≡ z*
    indZ-zero = refl

    indZ-e : (m : Z) → indZ (f e m) ≡ f (e* m) (indZ m)
    indZ-e m =
      coh l m (ap (λ f → f m) (f (tpt-loop-eqv l P) e*))
            (ap (ap (λ f → f m))
            (ind-s1-l (λ a → a ≡ b → Set l1) P (f (tpt-loop-eqv l P) e*))) ●
      ap (λ w → f (tpt-fp-eqv P l m) (tpt (λ M → M) (! (w m)) (indZ m)))
         (ε happly-eqv (λ m → ua (!e (e* m) ∘e tpt-fp-eqv P l m))) ●
      ap (λ w → f (tpt-fp-eqv P l m) (w (indZ m)))
         (tpt-id-!-ua (!e (e* m) ∘e tpt-fp-eqv P l m)) ●
      ε' (tpt-fp-eqv P l m) (f (e* m) (indZ m))
      module indZ-e where
        coh : {m2 m1 : S1} → (e1 : m1 ≡ m2) → (e2 : m2 ≡ b) →
              (e1* : tpt (λ m → m ≡ b → Set l1) e1 P^ e2 ≡ P^ e2) →
              (e3 : ap (λ f → f e2)
                       (apd (λ m → m ≡ b → Set l1) (λ a → P^ {a}) e1) ≡ e1*) →
              indZ.aux (e1 ● e2) ≡
              f (tpt-fp-eqv P^ e1 e2)
                (tpt (λ M → M) (! e1*) (indZ.aux e2))
        coh refl refl l* refl = refl

open LoopS1IsAZModel using (Z ; zero ; e ; indZ ; indZ-e) public
