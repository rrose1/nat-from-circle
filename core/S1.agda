{-# OPTIONS --without-K --rewriting #-}
module S1 where

open import Core
open import Rewrite
open import Path
open import Sigma
open import Function
open import Equivalence
open import Empty


postulate
  S1 : Set
  b : S1
  l : b ≡ b

postulate
  ind-s1 : (P : S1 → Set l1) → (b* : P b) → (l* : tpt P l b* ≡ b*) →
           (x : S1) → P x

postulate
  ind-s1-b : (P : S1 → Set l1) → (b* : P b) → (l* : tpt P l b* ≡ b*) →
             ind-s1 P b* l* b ↦ b*
{-# REWRITE ind-s1-b #-}

postulate
  ind-s1-l : (P : S1 → Set l1) → (b* : P b) → (l* : tpt P l b* ≡ b*) →
             apd P (ind-s1 P b* l*) l ≡ l*

----------

module _ {X : Set l1} where
  tpt-fp-eqv : {x1 x2 x3 : X} → (P : x1 ≡ x2 → Set l2) →
               (e1 : x1 ≡ x3) → (e2 : x3 ≡ x2) →
               (tpt (λ a → a ≡ x2 → Set l2) e1 P e2) ≃ (P (e1 ◾ e2))
  tpt-fp-eqv {x1} P refl refl = ide _

module _ (P-b : b ≡ b → Set l1) where
  path-s1-eqv : ((x : b ≡ b) → P-b x ≃ P-b (l ◾ x)) ≃
                (tpt (λ a → a ≡ b → Set l1) l P-b ≡ P-b)
  path-s1-eqv = !e fam-eqv ∘e
                pi-eqv-2 (λ x → ∘e-precomp-eqv (tpt-fp-eqv P-b l x) ∘e !e-eqv)

open _≃_
open EquivCoh

record SectionOnLoopS1 : Set (lsuc l1) where
  field
    P-b : (b ≡ b) → Set l1
    P-l  : (x : b ≡ b) → P-b x ≃ P-b (l ◾ x)
    p0 : P-b refl

  P : {a : S1} → (a ≡ b) → Set l1
  P {a} = ind-s1 (λ a → a ≡ b → Set l1) P-b (f (path-s1-eqv P-b) P-l) a
  
  s : {a : S1} → (e : a ≡ b) → P {a} e
  s refl = p0

  cmpt : (x : b ≡ b) → s (l ◾ x) ≡ f (P-l x) (s x)
  cmpt x =
    coh l x (ap (λ f → f x) (f (path-s1-eqv P-b) P-l))
     (ap (ap (λ f → f x))
         (ind-s1-l (λ a → a ≡ b → Set l1) P-b (f (path-s1-eqv P-b) P-l))) ◾
     ap (λ w → f (tpt-fp-eqv P-b l x) (tpt (λ X → X) (! (w x)) (s x)))
        (ε happly-eqv (λ x → ua (!e (P-l x) ∘e tpt-fp-eqv P-b l x))) ◾
     ap (λ w → f (tpt-fp-eqv P-b l x) (w (s x)))
        (tpt-id-!-ua (!e (P-l x) ∘e tpt-fp-eqv P-b l x)) ◾
     ε' (tpt-fp-eqv P-b l x) (f (P-l x) (s x))
    module cmpt where
    coh : {x2 x1 : S1} → (e1 : x1 ≡ x2) → (e2 : x2 ≡ b) →
          (e1* : tpt (λ x → x ≡ b → Set l1) e1 P e2 ≡ P e2) →
          (e3 : ap (λ f → f e2)
                   (apd (λ x → x ≡ b → Set l1) (λ a → P {a}) e1) ≡ e1*) →
          s (e1 ◾ e2) ≡
          f (tpt-fp-eqv P e1 e2)
            (tpt (λ X → X) (! e1*) (s e2))
    coh refl refl l* refl = refl
