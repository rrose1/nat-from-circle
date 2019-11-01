{-# OPTIONS --without-K #-}
module Segment where

open import TT
open import Structure
open import Presegment
open import Asymmetry


module _ {B : Set} {b : B} where
  module _ {xmin xmax : b ≡ b} {s : b ≡ b → b ≡ b}
           (p : Preseg xmin xmax s) where
   open Preseg p

   record is-seg : Set where
     constructor isseg
     field
       as : asym D
       rd : rel-has-dne R
       ir : is-irrefl R
       tr : is-trans R
       tc : is-trich R
       mn : is-min R dmin
       mx : is-max R dmax
       gn : gen-rel s R
       ds : is-disc s R

   record is-seg≠ : Set where
     constructor isseg≠
     field
       as : asym D
       rd : rel-has-dne R
       ir : is-irrefl R
       tr : is-trans R
       tc : is-trich R
       mn : is-min R dmin
       mx : is-max R dmax
       gn : gen-rel s R
       ds : is-disc s R
       r0 : R dmin dmax

   record is-seg= : Set where
     constructor isseg=
     field
       as : asym D
       rd : rel-has-dne R
       ir : is-irrefl R
       tr : is-trans R
       tc : is-trich R
       mn : is-min R dmin
       mx : is-max R dmax
       gn : gen-rel s R
       ds : is-disc s R
       nr : R dmin dmax → ⊥

   open is-seg
   is-seg-is-prop : is-prop is-seg
   is-seg-is-prop s1 s2 =
     ap (λ w → isseg (λ {x} → w {x}) (rd s1) (ir s1) (tr s1) (tc s1) (mn s1)
                      (mx s1) (gn s1) (ds s1))
        {x2 = (λ {x} → (as s2) {x})}
        (is-prop-pi' (λ {_} → is-prop-pi (λ _ →
         is-prop-pi (λ _ → is-prop-pi (λ _ ())))) _ _) ◾
     ap (λ w → isseg (as s2)
                      (λ {x1} {d1} {x2} {d2} → w {x1} {d1} {x2} {d2})
                      (ir s1) (tr s1) (tc s1) (mn s1) (mx s1) (gn s1) (ds s1))
        {x2 = (λ {x1} {d1} {x2} {d2} → (rd s2) {x1} {d1} {x2} {d2})}
        (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ → rp))))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (λ {x1} {d1} {d2} → w {x1} {d1} {d2})
                      (tr s1) (tc s1) (mn s1) (mx s1) (gn s1) (ds s1))
        {x2 = (λ {x1} {d1} {d2} → (ir s2) {x1} {d1} {d2})}
        (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ ())))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (ir s2)
                      (λ {x1} {d1} {x2} {d21} {d22} {x3} {d3} →
                         w {x1} {d1} {x2} {d21} {d22} {x3} {d3})
                      (tc s1) (mn s1) (mx s1) (gn s1) (ds s1))
        {x2 = (λ {x1} {d1} {x2} {d21} {d22} {x3} {d3} →
                 (tr s2) {x1} {d1} {x2} {d21} {d22} {x3} {d3})}
        (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ →
         is-prop-pi (λ _ → rp))))))))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (ir s2) (tr s2) (λ {x1} → w {x1}) (mn s1)
                      (mx s1) (gn s1) (ds s1))
        {x2 = (λ {x1} → (tc s2) {x1})}
        (is-prop-pi' (λ {_} → is-prop-pi (λ d1 → is-prop-pi' (λ {_} →
         is-prop-pi (λ d2 → trich-is-prop R rp (ir s2) (tr s2) d1 d2)))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (ir s2) (tr s2) (tc s2) (λ {x1} → w {x1})
                      (mx s1) (gn s1) (ds s1))
        {x2 = (λ {x1} → (mn s2) {x1})}
        (is-prop-pi' (λ {_} → is-prop-pi (λ _ → is-prop-pi (λ _ → rp))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (ir s2) (tr s2) (tc s2) (mn s2) (λ {x1} → w {x1})
                      (gn s1) (ds s1))
        {x2 = (λ {x1} → (mx s2) {x1})}
        (is-prop-pi' (λ {_} → is-prop-pi (λ _ → is-prop-pi (λ _ → rp))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (ir s2) (tr s2) (tc s2) (mn s2) (mx s2)
                      (λ {x1} → w {x1}) (ds s1))
        {x2 = (λ {x1} → (gn s2) {x1})}
        (is-prop-pi' (λ {_} → is-prop-pi (λ _ → is-prop-pi (λ _ → rp))) _ _) ◾
     ap (λ w → isseg (as s2) (rd s2) (ir s2) (tr s2) (tc s2) (mn s2) (mx s2) (gn s2)
                      (λ {x1} {d1} {x2} {d2} {d3} → w {x1} {d1} {x2} {d2} {d3}))
        {x2 = (λ {x1} {d1} {x2} {d2} {d3} → (ds s2) {x1} {d1} {x2} {d2} {d3})}
        (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi (λ _ →
         is-prop-pi (λ _ ()))))))) _ _)

   open is-seg≠
   seg≠-is-prop : is-prop is-seg≠
   seg≠-is-prop s1 s2 =
     ap (λ w → record { is-seg w ; r0 = (r0 s1) })
        (is-seg-is-prop (record { is-seg≠ s1 }) (record { is-seg≠ s2 })) ◾
     ap (λ w → record { is-seg≠ s2 hiding (r0) ; r0 = w })
        (rp _ _)

   open is-seg=
   seg=-is-prop : is-prop is-seg=
   seg=-is-prop s1 s2 =
     ap (λ w → record { is-seg w ; nr = (nr s1) })
        (is-seg-is-prop (record { is-seg= s1 }) (record { is-seg= s2 })) ◾
     ap (λ w → record { is-seg= s2 hiding (nr) ; nr = w })
        (is-prop-pi (λ _ ()) _ _)


  module _ (xmin xmax : b ≡ b) (e : (b ≡ b) ≃ (b ≡ b)) where
    open _≃_ e
    open EquivCoh
    
    record Seg : Set1 where
      field
        D : (x1 : b ≡ b) → Set
        dmin : D xmin
        dmax : D xmax
        as : asym D

        R : Rel D
        rp : rel-is-prop R
        rd : rel-has-dne R
        ir : is-irrefl R
        tr : is-trans R
        tc : is-trich R
        mn : is-min R dmin
        mx : is-max R dmax
        gn : gen-rel f R
        ds : is-disc f R
        up : is-upcl f R rp dmin dmax

      st = strict R ir
      stnn = strict-nn R ir
      dimn = di-min R ir tr tc mn
      dimx = di-max R ir tr tc mx
      smn = strict-min R ir tr mn
      smx = strict-max R ir tr mx
      ri = tpt-rel R rp rd ir tr tc
      dv = (λ {x2} {d2} {x3} {d3} →
            down-over f g η R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      ub = (λ {x2} {d2} {x3} {d3} →
            up-below f g η R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      dmon = (λ {x2} {d2} {x3} {d3} →
              down-mono f R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      umon = (λ {x2} {d2} {x3} {d3} →
              up-mono f g η R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      om1 = over-max-1 e R ir tr mx gn
      bm1 = below-min-1 e R ir tr mn gn
      su = shift-up f g (ε' e) R rp up

    record Seg≠ : Set1 where
      field
        D : (x1 : b ≡ b) → Set
        dmin : D xmin
        dmax : D xmax
        as : asym D

        R : Rel D
        rp : rel-is-prop R
        rd : rel-has-dne R
        ir : is-irrefl R
        tr : is-trans R
        tc : is-trich R
        mn : is-min R dmin
        mx : is-max R dmax
        gn : gen-rel f R
        ds : is-disc f R
        up : is-upcl f R rp dmin dmax

        r0 : R dmin dmax

      st = strict R ir
      stnn = strict-nn R ir
      dimn = di-min R ir tr tc mn
      dimx = di-max R ir tr tc mx
      smn = strict-min R ir tr mn
      smx = strict-max R ir tr mx
      ri = tpt-rel R rp rd ir tr tc
      dv = (λ {x2} {d2} {x3} {d3} →
            down-over f g η R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      ub = (λ {x2} {d2} {x3} {d3} →
            up-below f g η R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      dmon = (λ {x2} {d2} {x3} {d3} →
              down-mono f R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      umon = (λ {x2} {d2} {x3} {d3} →
              up-mono f g η R rp ir tr tc gn ds {x2 = x2} {d2} {x3} {d3} up)
      om1 = over-max-1 e R ir tr mx gn
      bm1 = below-min-1 e R ir tr mn gn
      su = shift-up f g (ε' e) R rp up

    record Seg= : Set1 where
      field
        D : (x1 : b ≡ b) → Set
        dmin : D xmin
        dmax : D xmax
        as : asym D

        R : Rel D
        rp : rel-is-prop R
        rd : rel-has-dne R
        ir : is-irrefl R
        tr : is-trans R
        tc : is-trich R
        mn : is-min R dmin
        mx : is-max R dmax
        gn : gen-rel f R
        ds : is-disc f R
        up : is-upcl f R rp dmin dmax

        nr : R dmin dmax → ⊥ {lzero}

      dimn = di-min R ir tr tc mn
      dimx = di-max R ir tr tc mx
      ri = tpt-rel R rp rd ir tr tc
      R-⊥ : {x1 : b ≡ b} → {d1 : D x1} → {x2 : b ≡ b} → {d2 : D x2} →
             R d1 d2 → ⊥
      R-⊥ {x1} {d1} {x2} {d2} r1 =
        aux (di-min R ir tr tc mn d1) (di-max R ir tr tc mx d2)
        module R-⊥ where
        aux : R dmin d1 ⊎ (xmin ≐ x1) → R d2 dmax ⊎ (x2 ≐ xmax) → ⊥
        aux (inl r2) (inl r3) = nr (tr r2 (tr r1 r3))
        aux (inl r2) (inr e1) = nr (ri (λ k → k refl) e1 (tr r2 r1))
        aux (inr e1) (inl r2) =
          nr (ri (λ k → e1 (λ e1 → k (! e1))) (λ k → k refl) (tr r1 r2))
        aux (inr e1) (inr e2) = nr (ri (λ k → e1 (λ e1 → k (! e1))) e2 r1)

      nx : xmin ≐ xmax
      nx = aux (dimn dmax)
        module nx where
        aux : R dmin dmax ⊎ (xmin ≐ xmax) → xmin ≐ xmax
        aux (inl r) = rec⊥ (nr r)
        aux (inr e) = e

  module _ (xmin xmax : b ≡ b) (e : (b ≡ b) ≃ (b ≡ b)) where
    open _≃_
    seg-eqv : Seg xmin xmax e ≃ Σ (Preseg xmin xmax (f e)) is-seg 
    f seg-eqv s = record { Seg s } , record { Seg s }
    g seg-eqv (p , s) = record { Preseg p ; is-seg s }
    η seg-eqv s = refl
    h seg-eqv = g seg-eqv
    ε seg-eqv s = refl

    seg≠-eqv : Seg≠ xmin xmax e ≃ Σ (Preseg xmin xmax (f e)) is-seg≠
    f seg≠-eqv s = record { Seg≠ s } , record { Seg≠ s }
    g seg≠-eqv (p , s) = record { Preseg p ; is-seg≠ s }
    η seg≠-eqv s = refl
    h seg≠-eqv = g seg≠-eqv
    ε seg≠-eqv s = refl

    seg=-eqv : Seg= xmin xmax e ≃ Σ (Preseg xmin xmax (f e)) is-seg=
    f seg=-eqv s = record { Seg= s } , record { Seg= s }
    g seg=-eqv (p , s) = record { Preseg p ; is-seg= s }
    η seg=-eqv s = refl
    h seg=-eqv = g seg=-eqv
    ε seg=-eqv s = refl

  module _ {xmin xmax : b ≡ b} {e : (b ≡ b) ≃ (b ≡ b)} where
    open _≃_
    seg-eq : {s1 s2 : Seg xmin xmax e} →
             PresegEqData xmin xmax (f e)
                          (record { Seg s1 }) (record { Seg s2 }) →
             s1 ≡ s2
    seg-eq {s2 = s2} d = g (eqv-embed (seg-eqv xmin xmax e))
                           (pair-prop-eq
                             (λ p → is-seg-is-prop p)
                             (preseg-eq (Seg.ir s2) (Seg.tr s2) d))

    seg≠-eq : {s1 s2 : Seg≠ xmin xmax e} →
              PresegEqData xmin xmax (f e)
                           (record { Seg≠ s1 }) (record { Seg≠ s2 }) →
              s1 ≡ s2
    seg≠-eq {s2 = s2} d = g (eqv-embed (seg≠-eqv xmin xmax e))
                            (pair-prop-eq
                              (λ p → seg≠-is-prop p)
                              (preseg-eq (Seg≠.ir s2) (Seg≠.tr s2) d))

    seg=-eq : {s1 s2 : Seg= xmin xmax e} →
              PresegEqData xmin xmax (f e)
                           (record { Seg= s1 }) (record { Seg= s2 }) →
              s1 ≡ s2
    seg=-eq {s2 = s2} d = g (eqv-embed (seg=-eqv xmin xmax e))
                            (pair-prop-eq
                              (λ p → seg=-is-prop p)
                              (preseg-eq (Seg=.ir s2) (Seg=.tr s2) d))
