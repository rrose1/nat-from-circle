{-# OPTIONS --without-K --rewriting #-}
module LoopS1HasDiv2Alg where

open import S1TT
open import LoopS1LoopIsCentral


open _≃_
open SectionOnLoopS1

div2-alg-lem : (x : b ≡ b) → l ◾ l ◾ x ◾ x ≡ (l ◾ x) ◾ l ◾ x
div2-alg-lem x =
  f lwhisk-eqv (! ◾assoc ◾ f rwhisk-eqv (! (com-l x)) ◾ ◾assoc) ◾ ! ◾assoc


div2-alg : SectionOnLoopS1
P-b div2-alg x = Σ (b ≡ b) (λ y → x ≡ y ◾ y) ⊎
                 Σ (b ≡ b) (λ y → x ≡ l ◾ y ◾ y)
p0  div2-alg = inl (refl , refl)

P-l div2-alg x =
  (sigma-eqv (lcomp-eqv l) (λ y → rcomp-eqv (div2-alg-lem y) ∘e lwhisk-eqv) ⊎e
   sigma-eqv (ide _) (λ y → lwhisk-eqv)) ∘e
  ⊎-com

div2 = s (div2-alg)
div2-cmpt = cmpt (div2-alg)


div2-coh-even : {x1 x2 y1 y2 : b ≡ b} →
                (e1 : x1 ≡ y1 ◾ y1) → (e2 : x2 ≡ y2 ◾ y2) →
                (e3 : x1 ≡ x2) → (e4 : y1 ≡ y2) →
                e3 ≡ e1 ◾ ap (λ x → x ◾ x) e4 ◾ ! e2 →
                (div2 x1 ≡ inl (y1 , e1)) ≃ (div2 x2 ≡ inl (y2 , e2))
div2-coh-even refl refl e3 refl refl = ide _

div2-coh-odd : {x1 x2 y1 y2 : b ≡ b} → (e1 : x1 ≡ l ◾ y1 ◾ y1) →
               (e2 : x2 ≡ l ◾ y2 ◾ y2) →
               (e3 : x1 ≡ x2) → (e4 : y1 ≡ y2) →
               e3 ≡ e1 ◾ ap (λ x → l ◾ x ◾ x) e4 ◾ ! e2 →
               (div2 x1 ≡ inr (y1 , e1)) ≃ (div2 x2 ≡ inr (y2 , e2))
div2-coh-odd refl refl e3 refl refl = ide _


div2-alg-dbl : SectionOnLoopS1
P-b div2-alg-dbl x = div2 (x ◾ x) ≡ inl (x , refl)
p0  div2-alg-dbl = refl

P-l div2-alg-dbl x =
  div2-coh-even _ refl (div2-alg-lem x) refl (! ◾unitl ◾ ! ◾unitr) ∘e
  lcomp-eqv (div2-cmpt (l ◾ x ◾ x)) ∘e
  lcomp-eqv (ap (λ z → f (P-l div2-alg (l ◾ x ◾ x)) z) (div2-cmpt (x ◾ x))) ∘e
  eqv-embed (P-l div2-alg (l ◾ x ◾ x) ∘e (P-l div2-alg (x ◾ x)))

div2-dbl = s div2-alg-dbl


no-2tor : {x : b ≡ b} → x ◾ x ≡ refl → x ≡ refl
no-2tor {x} e =
  ! (ap fst (inl-eq (f (div2-coh-even refl (! e) e refl
                                      (! !! ◾ ! ◾unitl ◾ ! ◾unitl))
                       (div2-dbl x))))

even-neq-odd : {x1 x2 : b ≡ b} →
               {a1 : Σ (b ≡ b) (λ y → x1 ≡ y ◾ y)} → div2 x1 ≡ inl a1 →
               {a2 : Σ (b ≡ b) (λ y → x2 ≡ l ◾ y ◾ y)} → div2 x2 ≡ inr a2 →
               x1 ≢ x2
even-neq-odd β1 β2 refl = inl-neq-inr (! β1 ◾ β2)

div2-!l : div2 (! l) ≡ inr (_ , _)
div2-!l = ! (η (P-l div2-alg (! l)) _) ◾
          ! (ap (g (P-l div2-alg (! l))) (div2-cmpt (! l))) ◾
          ap (g (P-l div2-alg (! l)))
             (f (div2-coh-even refl ◾invr (! ◾invr) refl (! ◾unitl ◾ ! ◾unitl)) refl)

div2-l : div2 l ≡ inr (refl , ! ◾unitr)
div2-l = f (div2-coh-odd refl (! ◾unitr) ◾unitr refl
                         (! !! ◾ ! ◾unitl ◾ ! ◾unitl))
           (div2-cmpt refl)

div2-lll : div2 (l ◾ l ◾ l) ≡ inr (_ , _)
div2-lll =
  div2-cmpt (l ◾ l) ◾
  ap (f (P-l div2-alg (l ◾ l))) (div2-cmpt l) ◾
  ap (f (P-l div2-alg (l ◾ l) ∘e P-l div2-alg l)) div2-l


l-neq-refl : l ≢ refl
l-neq-refl e = even-neq-odd refl div2-l (! e)

ll-neq-refl : l ◾ l ≢ refl
ll-neq-refl e = l-neq-refl (no-2tor e)

lll-neq-refl : l ◾ l ◾ l ≢ refl
lll-neq-refl e = even-neq-odd refl div2-lll (! e)
