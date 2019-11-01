{-# OPTIONS --without-K --rewriting #-}
module LoopS1HasDecEq where

open import S1TT
open import LoopS1HasDiv2Alg
open import Structure
open import Presegment
open import Asymmetry
open import Segment
open import LoopS1Segment
open import IncrementMin
open import IncrementMax


open _≃_
open SubEqv
open SectionOnLoopS1

module _ where

  open Seg
  open Seg≠
  
  has-seg : SectionOnLoopS1
  P-b has-seg x = Seg<0 x ⊎ Seg≥0 x
  p0 has-seg = inr seg-refl

  {-
    (Seg<0 x ⊎ Seg≥0 x) ≃
    (Seg≤0 x ⊎ Seg>0 x) ≃
    (Seg<0 (l ◾ x) ⊎ Seg>0 x) ≃
    (Seg<0 (l ◾ x) ⊎ Seg≥0 (l ◾ x))
  -}
  P-l has-seg x = (ide (Seg<0 (l ◾ x)) ⊎e shift-seg≥0 (l ◾ x)) ∘e
                  (ide (Seg<0 (l ◾ x)) ⊎e seg0-eqv (l ◾ x) ⊎e ide (Seg>0 (l ◾ x))) ∘e
                  ⊎-assoc ∘e
                  !e (shift-seg≤0 (l ◾ x) ⊎e ide (Seg>0 (l ◾ x))) ∘e
                  incr-min-eqv x ⊎e incr-max-eqv x

  seg : {a : S1} → (e : a ≡ b) → P has-seg e
  seg = s has-seg

  incr : {x : b ≡ b} → (Seg<0 x ⊎ Seg≥0 x) → (Seg<0 (l ◾ x) ⊎ Seg≥0 (l ◾ x))
  incr {x} = f (P-l has-seg x)

  seg-cmpt : (x : b ≡ b) → seg (l ◾ x) ≡ incr (seg x)
  seg-cmpt = cmpt has-seg

  D* : {x : b ≡ b} → P-b has-seg x → b ≡ b → Set
  D* (inl s) = D s
  D* (inr s) = D s

module _ where
  open Seg
  open Seg≠
  open Seg=

  has-seg-excl : SectionOnLoopS1
  P-b has-seg-excl x = Seg<0 x → Seg≥0 x → ⊥ {lzero}
  p0 has-seg-excl s1 s2 = Seg≠.st s1 (r0 s1) refl

  f (P-l has-seg-excl x) u s1 s2 =
    aux1 (g (shift-seg≥0 (l ◾ x)) s2)
    module f-P-l-has-seg-excl where
    aux1 : Seg+0 (l ◾ x) ⊎ Seg>0 (l ◾ x) → ⊥
    aux1 (inl s3) = nx s3 (λ e → Seg≠.st s1 (r0 s1) (! e))    
    aux1 (inr s3) = u (incr-min-eqv.g-eqv x (shift-seg≤0.f-eqv (l ◾ x) (inl s1)))
                      (g (incr-max-eqv x) s3)
  
  g (P-l has-seg-excl x) u s1 s2 =
    aux1 (g (shift-seg≤0 (l ◾ x)) (f (incr-min-eqv x) s1))
    module g-P-l-has-seg-excl where
    aux1 : Seg<0 (l ◾ x) ⊎ Seg-0 (l ◾ x) → ⊥
    aux1 (inl s3) = u s3 (shift-seg≥0.f-eqv (l ◾ x) (inr (incr-max-eqv.f-eqv x s2)))
    aux1 (inr s3) =
      nx s3 (λ e → Seg.bm1 s2 (tpt (D s2) (f (eqv-adj leqv) e) (dmax s2)))

  η (P-l has-seg-excl x) _ = is-prop-pi (λ _ → is-prop-pi (λ _ ())) _ _
  h (P-l has-seg-excl x) = g (P-l has-seg-excl x)
  ε (P-l has-seg-excl x) _ = is-prop-pi (λ _ → is-prop-pi (λ _ ())) _ _

  seg-excl : {a : S1} → (e : a ≡ b) → P has-seg-excl e
  seg-excl = s has-seg-excl
  
module _ {x1 : b ≡ b} where
  D*-incr : {s1 : Seg<0 x1 ⊎ Seg≥0 x1} → {s2 : Seg≥0 x1} →
            {x2 : b ≡ b} → D* s1 x2 → D* (incr s1) x2
  D*-incr {inl s1} {s2} _ = rec⊥ (seg-excl x1 s1 s2)
  D*-incr {inr s1} d = inl d


module _ (X : Set l1) where
  taut1 : (X × ((X → ⊥ {l1}) → ⊥ {l1})) ≃ X
  f taut1 (x , _) = x
  g taut1 x = x , (λ k → k x)
  η taut1 (x , _) = pair-prop-eq (λ _ → is-prop-pi (λ _ ())) refl
  h taut1 = g taut1
  ε taut1 x = refl

module _ where

  module _ where
    open Seg
    open Seg≠

  path-s1-has-dne : SectionOnLoopS1
  P-b path-s1-has-dne x =
    (y : b ≡ b) → (D* (seg x) (! l ◾ y) × (! l ◾ y ≐ x)) ≃ (! l ◾ y ≡ x)
  p0 path-s1-has-dne y = taut1 (D* (seg refl) (! l ◾ y))
  
  P-l path-s1-has-dne x =
    tpt-eqv (λ s → (y : b ≡ b) → (D* s (! l ◾ y) × (! l ◾ y ≐ l ◾ x)) ≃
                                   (! l ◾ y ≡ l ◾ x)) (! (seg-cmpt x)) ∘e
    aux1 _ refl
    module P-l-path-s1-has-dne where
    aux1 : (a1 : Seg<0 x ⊎ Seg≥0 x) → seg x ≡ a1 →
           ((y : b ≡ b) → (D* a1 (! l ◾ y) × (! l ◾ y ≐ x)) ≃ (! l ◾ y ≡ x)) ≃
           ((y : b ≡ b) → D* (incr a1) (! l ◾ y) × (! l ◾ y ≐ l ◾ x) ≃
                           (! l ◾ y ≡ l ◾ x))
    aux1 (inr s) _ = pi-eqv-2 (λ y → ∘e-precomp-eqv (e1 y)) ∘e e2
      module aux1-r where
      open Seg
      open Seg≠
    
      e1 : (y : b ≡ b) →
           ((D s (! l ◾ y) ⊎
             D s (! l ◾ ! l ◾ y) × (! l ◾ ! l ◾ y ≐ x)) ×
            (! l ◾ y ≐ l ◾ x)) ≃
           (D s (! l ◾ ! l ◾ y) × (! l ◾ ! l ◾ y ≐ x))
      f (e1 y) (inl d , e2) = rec⊥ (e2 (λ e2 → (Seg.om1 s (tpt (D s) e2 d))))
      f (e1 y) (inr d , e2) = d
      
      g (e1 y) (d , e2) = inr (d , e2) , nn-map (f (eqv-adj (!e leqv))) e2
      η (e1 y) (inl d , e2) = rec⊥ (e2 (λ e2 → Seg.om1 s (tpt (D s) e2 d)))
      η (e1 y) (inr d , e2) = pair-prop-eq (λ _ → is-prop-pi λ _ ()) refl
      h (e1 y) = g (e1 y)
      ε (e1 y) (d , e2) = refl
    
      e2 : ((y : b ≡ b) → D s (! l ◾ y) × (! l ◾ y ≐ x) ≃ (! l ◾ y ≡ x)) ≃
           ((y : b ≡ b) → D s (! l ◾ ! l ◾ y) × (! l ◾ ! l ◾ y ≐ x) ≃
                            (! l ◾ y ≡ l ◾ x))
      f e2 e1 y = eqv-adj (!e leqv) ∘e e1 (! l ◾ y)
      g e2 e1 y = !e (eqv-adj (!e leqv)) ∘e
                  tpt-eqv (λ y → y ≡ l ◾ x) (ηl y) ∘e e1 (l ◾ y) ∘e
                  tpt-eqv (λ y → (D s (! l ◾ y) × (! l ◾ y ≐ x))) (! (ηl y))
      η e2 e1 = funext (λ y → biinv-eq (funext (λ d → coh d (ηl y))))
        module η-e2 where
        coh : {y y2 : b ≡ b} →
              (d : Σ (D s (! l ◾ y2)) (λ _ → ! l ◾ y2 ≐ x)) →
              (e2 : ! l ◾ l ◾ y ≡ y2) →
              g (eqv-adj (!e leqv))
                  (tpt (λ y₁ → y₁ ≡ l ◾ x) e2
                       (f (eqv-adj (!e leqv))
                            (f (e1 (! l ◾ l ◾ y))
                               (tpt (λ y₁ → D s (! l ◾ y₁) × (! l ◾ y₁ ≐ x))
                                    (! e2) d)))) ≡
              f (e1 y2) d
        coh d refl = η (eqv-adj (!e leqv)) _

      h e2 = g e2
      ε e2 e1 = funext (λ y → biinv-eq (funext (λ d →
                 coh (ηl (! l ◾ y)) (εl y) (νl y) d)))
        module ε-e2 where
        coh : {y y2 : b ≡ b} → (e2 : ! l ◾ l ◾ ! l ◾ y ≡ ! l ◾ y2) →
              (e3 : l ◾ ! l ◾ y ≡ y2) → ap gl e3 ≡ e2 →
              (d : D s (! l ◾ ! l ◾ y2) × (! l ◾ ! l ◾ y2 ≐ x)) →
              f (eqv-adj (!e leqv))
                  (g (eqv-adj (!e leqv))
                       (tpt (λ y → y ≡ l ◾ x) e2
                            (f (e1 (l ◾ ! l ◾ y))
                               (tpt (λ y → D s (! l ◾ y) × (! l ◾ y ≐ x))
                                    (! e2) d)))) ≡
              f (e1 y2) d
        coh e2 refl refl d = ε (eqv-adj (!e leqv)) _

    aux1 (inl s) β1 =
      aux2 (Seg.dimx (incr-min-eqv.f-eqv x s) (dmin (incr-min-eqv.f-eqv x s)))
      module aux1-l where
      
      module _ (x : b ≡ b) (s : Seg<0 x) where
        open Seg≠ s

        e2 : (y : b ≡ b) → D (! l ◾ y) × (! l ◾ y ≐ x) ≃ D y × (y ≐ l ◾ x)
        f (e2 y) (d , e) =
          fst (f su (d , ri (λ k → e (λ e → k (! e))) (λ k → k refl) r0)) ,
          nn-map (f (eqv-adj (!e leqv))) e
        g (e2 y) (d , e) =
          fst (g su (d , rd (λ k → e (λ e →
                             k (ri (λ k → k refl)
                                   (λ k → k (! e))
                                   (gn dmin (tpt D e d))))))) ,
          nn-map (g (eqv-adj (!e leqv))) e
        η (e2 y) (d , e) = pair-prop-eq (λ _ → is-prop-pi (λ _ ())) (η^ su d _ _)
        h (e2 y) = g (e2 y)
        ε (e2 y) (d , e) = pair-prop-eq (λ _ → is-prop-pi (λ _ ())) (ε'^ su d _ _)

        e3 : ((y : b ≡ b) → D (! l ◾ y) × (! l ◾ y ≐ x) ≃ (! l ◾ y ≡ x)) ≃
             ((y : b ≡ b) → D (! l ◾ y) × (! l ◾ y ≐ l ◾ x) ≃ (! l ◾ y ≡ l ◾ x))
        f e3 e1 y = eqv-adj (!e leqv) ∘e e1 (! l ◾ y) ∘e !e (e2 (! l ◾ y))
        g e3 e1 y = !e (eqv-adj (!e leqv)) ∘e
                      tpt-eqv (λ y → y ≡ l ◾ x) (ηl y) ∘e
                      e1 (l ◾ y) ∘e
                      !e (tpt-eqv (λ y → D y × (y ≐ l ◾ x)) (ηl y)) ∘e
                      e2 y
        η e3 e1 =
          funext (λ y → biinv-eq (funext (λ d → aux (ηl y) (fst d) (snd d))))
          module η-e3 where
          aux : {y y2 : b ≡ b} → (e5 : ! l ◾ l ◾ y ≡ y2) →
                (d : D (! l ◾ y2)) → (e6 : ! l ◾ y2 ≐ x) →
                g (eqv-adj (!e leqv))
                (tpt (λ y → y ≡ l ◾ x) e5
                 (f (eqv-adj (!e leqv))
                  (f (e1 (! l ◾ l ◾ y))
                   (fst (g su
                     (fst (tpt (λ y → D y × (y ≐ l ◾ x)) (! e5)
                               (fst (f su (d , ri (λ k → e6 (λ e → k (! e)))
                                                  (λ k → k refl) r0)) ,
                                (λ k → e6 (λ e6 →
                                      k (f (eqv-adj (!e leqv)) e6))))) ,
                      rd (λ k → snd
                         (tpt (λ y → D y × (y ≐ l ◾ x))
                              (! e5)
                              (fst (f su (d , ri (λ k → e6 (λ e6 → k (! e6)))
                                                 (λ k → k refl)
                                                 r0)) ,
                               (λ k → e6 (λ e6 → k (f (eqv-adj (!e leqv)) e6)))))
                         (λ e → k
                          (ri (λ k → k refl)
                              (λ k → k (! e))
                              (gn dmin
                                  (tpt D e (fst
                                   (tpt (λ y → D y × (y ≐ l ◾ x))
                                        (! e5)
                                        (fst (f su
                                          (d , ri (λ k → e6 (λ e6 → k (! e6)))
                                                  (λ k → k refl) r0)) ,
                                         (λ k → e6 (λ e6 →
                                            k (f (eqv-adj (!e leqv)) e6))))))))))))) ,
                    (λ k → snd
                     (tpt (λ y → D y × (y ≐ l ◾ x))
                          (! e5)
                          (fst (f su
                           (d , ri (λ k → e6 (λ e → k (! e)))
                                   (λ k → k refl)
                                   r0)) ,
                      (λ k → e6 (λ e6 → k (f (eqv-adj (!e leqv)) e6)))))
                     (λ e → k (g (eqv-adj (!e leqv)) e))))))) ≡
                f (e1 y2) (d , e6)
          aux {y} refl d e6 =
            η (eqv-adj (!e leqv)) _ ◾
            ap (f (e1 (! l ◾ l ◾ y)))
               (pair-prop-eq (λ _ → is-prop-pi (λ _ ())) (η^ su d _ _))

        h e3 = g e3

        ε e3 e1 =
          funext (λ y → biinv-eq (funext (λ d →
            aux {y} {y} (ηl (! l ◾ y)) (εl y) (νl y) (fst d) (snd d))))
          module ε-e3 where
          aux : {y y2 : b ≡ b} → (e2 : ! l ◾ l ◾ ! l ◾ y ≡ ! l ◾ y2) →
                (e3 : l ◾ ! l ◾ y ≡ y2) → ap gl e3 ≡ e2 →
                (d : D (! l ◾ y2)) → (e4 : ! l ◾ y2 ≐ l ◾ x) →
                f (eqv-adj (!e leqv))
                (g (eqv-adj (!e leqv))
                 (tpt (λ y → y ≡ l ◾ x) e2
                  (f (e1 (l ◾ ! l ◾ y))
                     (tpt (λ y → D y × (y ≐ l ◾ x)) (! e2)
                      (fst (f su
                        (fst (g su
                          (d , rd (λ k → e4 (λ e →
                                     k (ri (λ k → k refl)
                                           (λ k → k (! e))
                                           (gn dmin (tpt D e d))))))) ,
                         ri (λ k → e4 (λ e4 → k (! (g (eqv-adj (!e leqv)) e4))))
                            (λ k → k refl)
                            r0)) ,
                       (λ k → e4 (λ e4 →
                          k (f (eqv-adj (!e leqv))
                               (g (eqv-adj (!e leqv)) e4))))))))) ≡
                f (e1 y2) (d , e4)
          aux {y} e2 refl refl d e4 =
            ε (eqv-adj (!e leqv)) _ ◾
            ap (f (e1 (l ◾ ! l ◾ y)))
               (pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                             (ε'^ su d _ _))

      open Seg
      open Seg≠
      e4 : (y : b ≡ b) →
           ((D s (! l ◾ y) × (x ≢ ! l ◾ y)) × (! l ◾ y ≐ l ◾ x)) ≃
           (D s (! l ◾ y) × (! l ◾ y ≐ l ◾ x))
      f (e4 y) ((d , n) , e5) = d , e5
      g (e4 y) (d , e5) =
        (d , (λ e4 → e5 (λ e5 →
                l-neq-refl (g rwhisk-eqv (! e5 ◾ ! e4 ◾ ! ◾unitl))))) ,
        e5
      η (e4 y) ((d , n) , e5) =
        pair-prop-eq
          (λ _ → is-prop-pi λ _ ())
          (pair-prop-eq (λ _ → is-prop-pi λ _ ()) refl)
      h (e4 y) = g (e4 y)
      ε (e4 y) (d , e) = refl

      aux2 : (a2 : R (incr-min-eqv.f-eqv x s) (dmin (incr-min-eqv.f-eqv x s))
                     (dmax (incr-min-eqv.f-eqv x s))
                     ⊎ (l ◾ x ≐ refl)) →
             ((y : b ≡ b) → D s (! l ◾ y) × (! l ◾ y ≐ x) ≃ (! l ◾ y ≡ x)) ≃
             ((y : b ≡ b) →
              D* ((f (ide (Seg≠ (l ◾ x) refl (lcomp-eqv l)) ⊎e
                      shift-seg≥0 (l ◾ x))
                     (f (ide (Seg≠ (l ◾ x) refl (lcomp-eqv l)) ⊎e
                         seg0-eqv (l ◾ x) ⊎e
                         ide (Seg≠ refl (l ◾ x) (lcomp-eqv l)))
                      (f ⊎-assoc (inl (shift-seg≤0.g-eqv
                                        (l ◾ x)
                                        (incr-min-eqv.f-eqv x s)
                                        a2)))))) (! l ◾ y) ×
              (! l ◾ y ≐ l ◾ x) ≃
              (! l ◾ y ≡ l ◾ x))
      aux2 (inl _) = pi-eqv-2 (λ y → ∘e-precomp-eqv (e4 y)) ∘e e3 x s
      aux2 (inr _) = pi-eqv-2 (λ y → ∘e-precomp-eqv (e4 y)) ∘e e3 x s


  path-s1-has-dec-eq : (x y : b ≡ b) → is-dec (x ≡ y)
  path-s1-has-dec-eq x y = aux1 (s has-seg (x ◾ ! y)) (s path-s1-has-dne (x ◾ ! y) l)
    module path-s1-has-dec-eq where
    open Seg
    open Seg≠
    aux1 : (a1 : Seg<0 (x ◾ ! y) ⊎ Seg≥0 (x ◾ ! y)) →
           D* a1 (! l ◾ l) × (! l ◾ l ≐ x ◾ ! y) ≃ (! l ◾ l ≡ x ◾ ! y) →
           is-dec (x ≡ y)
    aux1 (inl s) _  =
      inr (λ e → Seg≠.stnn s (r0 s)
           (λ k → k (g (eqv-adj (!e (rcomp-eqv y))) (e ◾ ! ◾unitl))))
    aux1 (inr s) e1 = aux2 (Seg.dimx s (Seg.dmin s))
      module aux1 where
      aux2 : R s (dmin s) (dmax s) ⊎ (refl ≐ x ◾ ! y) → is-dec (x ≡ y)
      aux2 (inl r) = inr (λ e → Seg.stnn s r (λ k →
                          k (! (g (eqv-adj (!e (rcomp-eqv y))) (e ◾ ! ◾unitl)))))
      aux2 (inr e2) =
        inl (! (g (eqv-adj (rcomp-eqv y))
                  (! ◾invl ◾
                   f e1 (tpt (λ y → D* (inr s) y) (! ◾invl) (dmin s) ,
                         (λ k → e2 (λ e2 → k (◾invl ◾ e2)))))) ◾
             ◾unitl)

  path-s1-is-set = has-dec-eq->is-set path-s1-has-dec-eq

module _ where
  open Seg
  open Seg≠

  D-seg-is-prop : SectionOnLoopS1
  P-b D-seg-is-prop x1 = (x2 : b ≡ b) → is-prop (D* (seg x1) x2)
  
  P-l D-seg-is-prop x1 =
    tpt-eqv (λ s → (x2 : b ≡ b) → is-prop (D* s x2)) (! (seg-cmpt x1)) ∘e
    aux1 (seg x1)
    module P-l-D-seg-is-prop where
    aux1 : (a1 : Seg<0 x1 ⊎ Seg≥0 x1) →
           ((x2 : b ≡ b) → is-prop (D* a1 x2)) ≃
           ((x2 : b ≡ b) → is-prop (D* (incr a1) x2))
    f (aux1 (inr s1)) ϕ x2 (inl d1) (inl d2) = ap inl (ϕ x2 d1 d2)
    f (aux1 (inr s1)) ϕ x2 (inl d1) (inr (d2 , e2)) =
      rec⊥ (e2 (λ e2 → (Seg.om1 s1 (tpt (D s1) (f (eqv-adj (!e leqv)) e2) d1))))
    f (aux1 (inr s1)) ϕ x2 (inr (d1 , e1)) (inl d2) =
      rec⊥ (e1 (λ e1 → (Seg.om1 s1 (tpt (D s1) (f (eqv-adj (!e leqv)) e1) d2))))
    f (aux1 (inr s1)) ϕ x2 (inr (d1 , e1)) (inr (d2 , e2)) =
      ap inr (pair-prop-eq (λ _ → is-prop-pi λ _ ()) (ϕ (! l ◾ x2) d1 d2))
    g (aux1 (inr s1)) ϕ x2 d1 d2 = inl-eq (ϕ x2 (inl d1) (inl d2))
    η (aux1 (inr s1)) ϕ = funext (λ _ → is-prop-is-prop _ _ _)
    h (aux1 (inr s1)) = g (aux1 (inr s1))
    ε (aux1 (inr s1)) ϕ = funext (λ _ → is-prop-is-prop _ _ _)

    aux1 (inl s1) =
      aux2 (di-max.aux (R (incr-min-eqv.f-eqv x1 s1)) (ir s1) (tr s1)
                          (tc (incr-min-eqv.f-eqv x1 s1))
                          (mx (incr-min-eqv.f-eqv x1 s1))
                          (fst (f (up s1) (dmin s1 , r0 s1)) ,
                           strict (R s1) (ir s1) (snd (f (up s1) (dmin s1 , r0 s1))))
                          (tc s1 (fst (f (up s1) (dmin s1 , r0 s1))) (dmax s1)))
      module aux1-l where
      e3 : ((x2 : b ≡ b) → is-prop (D s1 x2)) ≃
           ((x2 : b ≡ b) → is-prop (D s1 x2 × (x1 ≢ x2)))
      f e3 ϕ x2 (d1 , _) (d2 , _) =
        pair-prop-eq (λ _ → is-prop-pi (λ _ ())) (ϕ x2 d1 d2)
      g e3 ϕ x2 d1 = aux3 (Seg≠.dimn s1 d1)
        module e3 where
        r : (e : x1 ≐ x2) → (d : D s1 x2) → R s1 d (dmax s1)
        r e d = Seg≠.ri s1 e (λ k → k refl) (r0 s1)

        n : (d : D s1 x2) → x1 ≢ l ◾ x2
        n d e = Seg≠.bm1 s1 (tpt (D s1) (! (g (eqv-adj (!e leqv)) e)) d)

        aux3 : R s1 (dmin s1) d1 ⊎ (x1 ≐ x2) → (d2 : D s1 x2) → d1 ≡ d2
        aux3 (inl r1) d2 = ap fst (ϕ x2 (d1 , Seg≠.st s1 r1) (d2 , Seg≠.st s1 r1))
        aux3 (inr e4) d2 =
          ! (η^ (up s1) d1 (r e4 d1)
                           (snd (f (up s1) (d1 , r e4 d1)))) ◾
          ap (λ d → fst (g (up s1) d))
             (pair-prop-eq (λ _ → rp s1)
                           (ap fst (ϕ (l ◾ x2)
                                      (fst (f (up s1) (d1 , r e4 d1)) , n d1)
                                      (fst (f (up s1) (d2 , r e4 d2)) , n d2)))) ◾
          η^ (up s1) d2 (r e4 d2) (snd (f (up s1) (d2 , r e4 d2)))

      η e3 ϕ = funext (λ x2 → is-prop-is-prop _ (g e3 (f e3 ϕ) x2) (ϕ x2))
      h e3 = g e3
      ε e3 ϕ = funext (λ x2 → is-prop-is-prop _ (f e3 (h e3 ϕ) x2) (ϕ x2))

      aux2 : (a2 : R (incr-min-eqv.f-eqv x1 s1)
                     (dmin (incr-min-eqv.f-eqv x1 s1))
                     (dmax (incr-min-eqv.f-eqv x1 s1)) ⊎
                   (l ◾ x1 ≐ refl)) →
             ((x2 : b ≡ b) → is-prop (D s1 x2)) ≃
             ((x2 : b ≡ b) →
              is-prop (D* (f (ide (Seg≠ (l ◾ x1) refl (lcomp-eqv l)) ⊎e
                             shift-seg≥0.eqv (l ◾ x1))
                            (f (ide (Seg≠ (l ◾ x1) refl (lcomp-eqv l)) ⊎e
                                seg0-eqv (l ◾ x1) ⊎e
                                ide (Seg≠ refl (l ◾ x1) (lcomp-eqv l)))
                               (f ⊎-assoc (inl (shift-seg≤0.g-eqv (l ◾ x1)
                                          (incr-min-eqv.f-eqv x1 s1) a2))))) x2))
      aux2 (inl _) = e3
      aux2 (inr _) = e3
  
  p0 D-seg-is-prop x2 = path-s1-is-set
