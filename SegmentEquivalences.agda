{-# OPTIONS --without-K #-}
module SegmentEquivalences where

open import UTT
open import SegmentProperties
open import Segment using (module SegmentDefinitions ; PresegEqData ; seg=-eq)
open import SegmentExtension


module _ {X : Set} (x0 : X) (e : X ≃ X) (i : X → X) where

  open SegmentDefinitions x0 e i
  
  module MinSegEqv (x : X) where
    open Seg=
    open PresegEqData

    f-min-seg-eqv : Seg-0 x → Seg+0 x
    D (f-min-seg-eqv s) = D s
    d0 (f-min-seg-eqv s) = d0 s
    dmin (f-min-seg-eqv s) = dmax s
    dmax (f-min-seg-eqv s) = dmin s
    ac (f-min-seg-eqv s) = ac s
    R (f-min-seg-eqv s) = R s
    pr (f-min-seg-eqv s) = pr s
    ir (f-min-seg-eqv s) = ir s
    tr (f-min-seg-eqv s) = tr s
    tc (f-min-seg-eqv s) = tc s
    mn (f-min-seg-eqv s) d1 n1 = rec⊥ (R-⊥ s (mx s d1 (λ e1 → n1 (! e1))))
    mx (f-min-seg-eqv s) d1 n1 = rec⊥ (R-⊥ s (mn s d1 (λ e1 → n1 (! e1))))
    ex (f-min-seg-eqv s) = ex s
    ds (f-min-seg-eqv s) = ds s

    f (cl (f-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
    g (cl (f-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
    η (cl (f-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
    h (cl (f-min-seg-eqv s))         = g (cl (f-min-seg-eqv s))
    ε (cl (f-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)

    nr (f-min-seg-eqv s) = R-⊥ s

    g-min-seg-eqv : Seg+0 x → Seg-0 x
    D (g-min-seg-eqv s) = D s
    d0 (g-min-seg-eqv s) = d0 s 
    dmin (g-min-seg-eqv s) = dmax s
    dmax (g-min-seg-eqv s) = dmin s
    ac (g-min-seg-eqv s) = ac s
    R (g-min-seg-eqv s) = R s
    pr (g-min-seg-eqv s) = pr s
    ir (g-min-seg-eqv s) = ir s
    tr (g-min-seg-eqv s) = tr s
    tc (g-min-seg-eqv s) = tc s
    mn (g-min-seg-eqv s) d1 n1 = rec⊥ (R-⊥ s (mx s d1 (λ e1 → n1 (! e1))))
    mx (g-min-seg-eqv s) d1 n1 = rec⊥ (R-⊥ s (mn s d1 (λ e1 → n1 (! e1))))
    ex (g-min-seg-eqv s) = ex s
    ds (g-min-seg-eqv s) = ds s

    f (cl (g-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
    g (cl (g-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
    η (cl (g-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
    h (cl (g-min-seg-eqv s))         = g (cl (g-min-seg-eqv s))
    ε (cl (g-min-seg-eqv s)) (d , r) = rec⊥ (R-⊥ s r)

    nr (g-min-seg-eqv s) = R-⊥ s

    η-min-seg-eqv : (s : Seg-0 x) → g-min-seg-eqv (f-min-seg-eqv s) ≡ s
    η-min-seg-eqv s = seg=-eq p where
      p : PresegEqData
            (record { Seg= (g-min-seg-eqv (f-min-seg-eqv s)) })
            (record { Seg= s })
      Deq p x = ide (D s x)
      Deq' p = _
      Deqcoh p = refl
      d0eq p = refl
      d0eq' p = _
      d0eqcoh p = refl
      dmineq p = refl
      dmineq' p = _
      dmineqcoh p = refl
      dmaxeq p = refl
      dmaxeq' p = _
      dmaxeqcoh p = refl
      Req p = id , id
      Req' p = _
      Reqcoh p = refl
      preq' p = rel-is-prop-eq (Deq p) (Deqcoh p) (Req p) (Reqcoh p)
      cleq p d r _ = rec⊥ (R-⊥ s r)

    ε-min-seg-eqv : (s : Seg+0 x) → f-min-seg-eqv (g-min-seg-eqv s) ≡ s
    ε-min-seg-eqv s = seg=-eq p where
      p : PresegEqData
            (record { Seg= (f-min-seg-eqv (g-min-seg-eqv s)) })
            (record { Seg= s })
      Deq p x = ide (D s x)
      Deq' p = _
      Deqcoh p = refl
      d0eq p = refl
      d0eq' p = _
      d0eqcoh p = refl
      dmineq p = refl
      dmineq' p = _
      dmineqcoh p = refl
      dmaxeq p = refl
      dmaxeq' p = _
      dmaxeqcoh p = refl
      Req p = id , id
      Req' p = _
      Reqcoh p = refl
      preq' p = rel-is-prop-eq (Deq p) (Deqcoh p) (Req p) (Reqcoh p)
      cleq p d r _ = rec⊥ (R-⊥ s r)

    min-seg-eqv : Seg-0 x ≃ Seg+0 x
    f min-seg-eqv = f-min-seg-eqv
    g min-seg-eqv = g-min-seg-eqv
    η min-seg-eqv = η-min-seg-eqv
    h min-seg-eqv = g-min-seg-eqv
    ε min-seg-eqv = ε-min-seg-eqv

  open MinSegEqv using (min-seg-eqv) public


  module NonnegativePartEqv (x : X) where
    open Seg
    open Seg≠
    open Seg=

    nneg-part-eqv : (Seg+0 x ⊎ Seg>0 x) ≃ Seg≥0 x
    nneg-part-eqv = eqv
      module nneg-part-eqv where
      f-eqv : (Seg+0 x ⊎ Seg>0 x) → Seg≥0 x
      f-eqv (inl s) = record { Seg= s }
      f-eqv (inr s) = record { Seg≠ s }

      g-eqv : (s : Seg≥0 x) →
              R s (dmin s) (dmax s) ⊎ (x0 ≐ x) →
              (Seg+0 x ⊎ Seg>0 x)
      g-eqv s (inl r) = inr record { Seg s ; r0 = r }
      g-eqv s (inr e1) =
        inl record { Seg s ; nr = (λ r → e1 (λ e1 → Seg.st s r e1)) }

      η-eqv-l : (s : Seg+0 x) →
                (a : R s (dmin s) (dmax s) ⊎ (x0 ≐ x)) →
                g-eqv (f-eqv (inl s)) a ≡ inl s
      η-eqv-l s (inl r) = rec⊥ (nr s r)
      η-eqv-l s (inr e) =
        ap (λ n → inl (record { Seg= s hiding (nr) ; nr = n }))
           (is-prop-pi (λ _ ()) _ _)

      η-eqv-r : (s : Seg>0 x) →
                (a1 : R (f-eqv (inr s)) (dmin s) (dmax s) ⊎ (x0 ≐ x)) →
                g-eqv (f-eqv (inr s)) a1 ≡ inr s
      η-eqv-r s (inl r) =
        ap (λ r0 → inr (record { Seg≠ s hiding (r0) ; r0 = r0}))
           (pr s r (r0 s))
      η-eqv-r s (inr e1) = rec⊥ (e1 (λ e1 → Seg≠.st s (r0 s) e1))

      ε-eqv : (s : Seg≥0 x) → (a : R s (dmin s) (dmax s) ⊎ (x0 ≐ x)) →
              f-eqv (g-eqv s a) ≡ s
      ε-eqv s (inl r) = refl
      ε-eqv s (inr e) = refl

      eqv : (Seg+0 x ⊎ Seg>0 x) ≃ Seg≥0 x
      f eqv = f-eqv
      g eqv s = g-eqv s (Seg.dimx s (dmin s))
      η eqv (inl s) = η-eqv-l s (Seg.dimx (f-eqv (inl s)) (dmin s))
      η eqv (inr s) = η-eqv-r s (Seg≠.dimx s (dmin s))
      h eqv = g eqv
      ε eqv s = ε-eqv s (Seg.dimx s (dmin s))
      
  open NonnegativePartEqv public


  module NonpositivePartEqv (x : X) where
    open Seg
    open Seg≠
    open Seg=

    npos-part-eqv : (Seg<0 x ⊎ Seg-0 x) ≃ Seg≤0 x
    npos-part-eqv = eqv
      module npos-part-eqv where
      f-eqv : Seg<0 x ⊎ Seg-0 x → Seg≤0 x
      f-eqv (inl s) = record { Seg≠ s }
      f-eqv (inr s) = record { Seg= s }

      g-eqv : (s : Seg≤0 x) → R s (dmin s) (dmax s) ⊎ (x ≐ x0) → Seg<0 x ⊎ Seg-0 x
      g-eqv s (inl r) = inl (record { Seg s ; r0 = r })
      g-eqv s (inr e1) = inr (record { Seg s ; nr = λ r → e1 (λ e1 → Seg.st s r e1)})

      η-eqv-l : (s : Seg<0 x) → (a : R (f-eqv (inl s)) (dmin (f-eqv (inl s)))
                               (dmax (f-eqv (inl s))) ⊎ (x ≐ x0)) →
                 g-eqv (f-eqv (inl s)) a ≡ inl s
      η-eqv-l s (inl r) =
        ap (λ r → inl (record { Seg≠ s hiding (r0) ; r0 = r})) (pr s _ _)
      η-eqv-l s (inr e1) = rec⊥ (e1 (λ e1 → Seg≠.st s (r0 s) e1))

      η-eqv-r : (s : Seg-0 x) →
                (a : R (f-eqv (inr s)) (dmin (f-eqv (inr s)))
                       (dmax (f-eqv (inr s))) ⊎
                       (x ≐ x0)) →
                g-eqv (f-eqv (inr s)) a ≡ inr s
      η-eqv-r s (inl r) = rec⊥ (nr s r)
      η-eqv-r s (inr e) =
        ap (λ r → inr (record { Seg= s hiding (nr) ; nr = r})) 
           (is-prop-pi (λ _ ()) _ _)

      ε-eqv : (s : Seg≤0 x) → (a : R s (dmin s) (dmax s) ⊎ (x ≐ x0)) →
              f-eqv (g-eqv s a) ≡ s
      ε-eqv s (inl r) = refl
      ε-eqv s (inr e) = refl

      eqv : (Seg<0 x ⊎ Seg-0 x) ≃ Seg≤0 x
      f eqv = f-eqv
      g eqv s = g-eqv s (Seg.dimx s (dmin s))
      η eqv (inl s) = η-eqv-l s (Seg.dimx (f-eqv (inl s)) (dmin (f-eqv (inl s))))
      η eqv (inr s) = η-eqv-r s (Seg.dimx (f-eqv (inr s)) (dmin (f-eqv (inr s))))
      h eqv = g eqv
      ε eqv s = ε-eqv s (Seg.dimx s (dmin s))
  open NonpositivePartEqv public


  module Seg0Eqv
         (i0 : i x0 ≡ x0)
         (i0-inv : {x : X} → i x ≡ x → x ≡ x0)
         (anc1 : (x : X) → i (f e x) ≡ g e (i x))
         (anc2 : (x : X) → f e (i x) ≡ i (g e x))
         (e≠i : (x : X) → f e x ≢ i x)
         where

    open IncrementMaxEqv e i0 i0-inv anc1 anc2 e≠i
    open IncrementMinEqv e i0 i0-inv anc1 anc2 e≠i
    incr-min = λ {x1} → f (incr-min-eqv x1)
    incr-max = λ {x1} → f (incr-max-eqv x1)


    seg0-eqv : (x1 : X) → Seg0 x1 ≃ Seg0 (f e x1)
    seg0-eqv x1 = (ide (Seg<0 (f e x1)) ⊎e nneg-part-eqv (f e x1)) ∘e
                  (ide (Seg<0 (f e x1)) ⊎e min-seg-eqv (f e x1) ⊎e
                   ide (Seg>0 (f e x1))) ∘e
                  ⊎-assoc ∘e
                  !e (npos-part-eqv (f e x1) ⊎e ide (Seg>0 (f e x1))) ∘e
                  (incr-min-eqv x1 ⊎e incr-max-eqv x1)    

    dom0-eqv : {x1 : X} → (s1 : Seg0 x1) → (x2 : X) →
             D0 (f (seg0-eqv x1) s1) x2 × (x2 ≐ f e x1) ≃
             D0 s1 (g e x2) × (g e x2 ≐ x1)
    dom0-eqv {x1} (inl s1) x2 = aux (dimx' dmin')
      module dom0-eqv-l where
      open Seg≠ s1
      open Seg (f (incr-min-eqv _) s1)
           renaming (D to D'; R to R';
                     dmin to dmin'; dmax to dmax';
                     dimx to dimx')
           using ()

      eqv : (D x2 × (x1 ≢ x2)) × (x2 ≐ f e x1)
            ≃ D (g e x2) × (g e x2 ≐ x1)
      f eqv ((d2 , n2) , e2) =
        fst (g sc (d2 , mn d2 n2)) ,
        (λ k → e2 (λ e2 → k (! (f (adj e) (! e2)))))
      g eqv (d2 , e2) =
        (fst (f sc (d2 , mx d2 (λ e3 → e2 (λ e2 → st r0 (! e2 ● e3))))) ,
         (λ e3 → un1 (tpt D (! (ap (g e) e3)) d2))) ,
        (λ k → e2 (λ e2 → k (! (g (adj e) (! e2)))))
      η eqv ((d2 , n2) , e2) =
        pair-eq
          (pair-eq
            (εs pr sc d2 _ _ , is-prop-pi (λ _ ()) _ _) ,
           is-prop-pi (λ _ ()) _ _)
      h eqv = g eqv
      ε eqv (d2 , e2) =
        pair-eq (ηs pr sc d2 _ _ , is-prop-pi (λ _ ()) _ _)

      aux : (a : R' dmin' dmax' ⊎ (f e x1 ≐ x0)) →
            D0 (f (ide _ ⊎e nneg-part-eqv.eqv _)
                  (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                     (f ⊎-assoc (inl (npos-part-eqv.g-eqv _
                                       (incr-min s1) a))))) x2 ×
               (x2 ≐ f e x1)
            ≃ D (g e x2) × (g e x2 ≐ x1)
      aux (inl _) = eqv
      aux (inr _) = eqv

    dom0-eqv {x1} (inr s1) x2 = eqv
      module dom0-eqv-r where
      open Seg s1
      eqv : (D x2 ⊎ (D (g e x2) × (g e x2 ≐ x1))) × (x2 ≐ f e x1)
            ≃ D (g e x2) × (g e x2 ≐ x1)
      f eqv (inl d2 , e2) = rec⊥ (e2 (λ e2 → ov1 (tpt D e2 d2)))
      f eqv (inr (d2 , e2) , e3) = d2 , e2
      g eqv (d2 , e2) =
        inr (d2 , e2) , (λ k → e2 (λ e2 → k (! (g (adj e) (! e2)))))
      η eqv (inl d2 , e2) = rec⊥ (e2 (λ e2 → ov1 (tpt D e2 d2)))
      η eqv (inr (d2 , e2) , e3) =
        ap (λ e1 → inr (d2 , e2) , e1)
           (is-prop-pi (λ _ ()) _ e3)
      h eqv = g eqv
      ε eqv (d2 , e2) = refl

    stab-lem1-type : (x1 : X) → (s1 : Seg0 x1) → Set
    stab-lem1-type x1 s1 = (x2 : X) → D0 s1 x2 × (x2 ≐ x1) ≃ (x2 ≡ x1)

    stab-lem1-eqv : (x1 : X) → (s1 : Seg0 x1) →
                    stab-lem1-type x1 s1 ≃
                    stab-lem1-type (f e x1) (f (seg0-eqv x1) s1)
    stab-lem1-eqv x1 s1 =
      pi-eqv-2 (λ x2 → ∘e-bicomp-eqv (dom0-eqv s1 x2)
                                     (adj (!e e))) ∘e
                       !e (pi-eqv-1' (!e e))

  open Seg0Eqv public
