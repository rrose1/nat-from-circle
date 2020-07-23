{-# OPTIONS --without-K #-}
module Segment where

open import UTT
open import SegmentProperties


module SegmentDefinitions {X : Set} (x0 : X) (e : X ≃ X) (i : X → X) where

  record Seg (xmin xmax : X) : Set1 where
    field
      D : (x1 : X) → Set
      d0 : D x0
      dmin : D xmin
      dmax : D xmax

      R : Rel D
      pr : rel-is-prop R
      ir : is-irrefl R
      tr : is-trans R
      tc : is-trich R
      mn : is-min R dmin
      mx : is-max R dmax
      ex : extensive (f e) R
      ds : is-disc (f e) R
      cl : is-closed (f e) R pr dmin dmax
      ac : is-anticlosed i D

    st = strict R ir
    dimn = di-min R ir tr tc mn
    dimx = di-max R ir tr tc mx
    smn = strict-min R ir tr mn
    smx = strict-max R ir tr mx
    ri = tpt-rel R ir tr tc
    dmon = (λ {x2} {d2} {x3} {d3} →
            cl-inv-mono (f e) R pr ir tr tc ex ds
                        {x2 = x2} {d2} {x3} {d3} cl)
    umon = (λ {x2} {d2} {x3} {d3} →
            cl-mono (f e) (g e) (η e) R pr ir tr tc ex ds
                    {x2 = x2} {d2} {x3} {d3} cl)
    ov1 = over-1 e R ir tr mx ex
    un1 = under-1 e R ir tr mn ex
    sc = shift-cl (f e) (g e) (ε' e) R pr cl


  record Seg≠ (xmin xmax : X) : Set1 where
    field
      D : (x1 : X) → Set
      dmin : D xmin
      dmax : D xmax
      d0 : D x0

      R : Rel D
      pr : rel-is-prop R
      ir : is-irrefl R
      tr : is-trans R
      tc : is-trich R
      mn : is-min R dmin
      mx : is-max R dmax
      ex : extensive (f e) R
      ds : is-disc (f e) R
      cl : is-closed (f e) R pr dmin dmax
      ac : is-anticlosed i D

      r0 : R dmin dmax

    st = strict R ir
    dimn = di-min R ir tr tc mn
    dimx = di-max R ir tr tc mx
    smn = strict-min R ir tr mn
    smx = strict-max R ir tr mx
    ri = tpt-rel R ir tr tc
    dmon = (λ {x2} {d2} {x3} {d3} →
            cl-inv-mono (f e) R pr ir tr tc ex ds
                        {x2 = x2} {d2} {x3} {d3} cl)
    umon = (λ {x2} {d2} {x3} {d3} →
            cl-mono (f e) (g e) (η e) R pr ir tr tc ex ds
                    {x2 = x2} {d2} {x3} {d3} cl)
    ov1 = over-1 e R ir tr mx ex
    un1 = under-1 e R ir tr mn ex
    sc = shift-cl (f e) (g e) (ε' e) R pr cl


  record Seg= (xmin xmax : X) : Set1 where
    field
      D : (x1 : X) → Set
      d0 : D x0
      dmin : D xmin
      dmax : D xmax

      R : Rel D
      pr : rel-is-prop R
      ir : is-irrefl R
      tr : is-trans R
      tc : is-trich R
      mn : is-min R dmin
      mx : is-max R dmax
      ex : extensive (f e) R
      ds : is-disc (f e) R
      cl : is-closed (f e) R pr dmin dmax
      ac : is-anticlosed i D

      nr : R dmin dmax → ⊥ {lzero}

    dimn = di-min R ir tr tc mn
    dimx = di-max R ir tr tc mx
    ri = tpt-rel R ir tr tc
    R-⊥ : {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
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

  Seg<0 : (xmin : X) → Set1
  Seg<0 xmin = Seg≠ xmin x0

  Seg≤0 : (xmin : X) → Set1
  Seg≤0 xmin = Seg xmin x0

  Seg-0 : (xmin : X) → Set1
  Seg-0 xmin = Seg= xmin x0

  Seg+0 : (xmax : X) → Set1
  Seg+0 xmax = Seg= x0 xmax

  Seg≥0 : (xmax : X) → Set1
  Seg≥0 xmax = Seg x0 xmax

  Seg>0 : (xmax : X) → Set1
  Seg>0 xmax = Seg≠ x0 xmax


  Seg0 = λ x → Seg<0 x ⊎ Seg≥0 x

  module _ {x1 : X} where
    D0 : Seg0 x1 → X → Set
    D0 (inl s1) = Seg≠.D s1
    D0 (inr s1) = Seg.D s1

    d00 : (s1 : Seg0 x1) → D0 s1 x0
    d00 (inl s1) = Seg≠.d0 s1
    d00 (inr s1) = Seg.d0 s1

    xmin0 : (s1 : Seg0 x1) → X
    xmin0 (inl s1) = x1
    xmin0 (inr s1) = x0

    dmin0 : (s1 : Seg0 x1) → D0 s1 (xmin0 s1)
    dmin0 (inl s1) = Seg≠.dmin s1
    dmin0 (inr s1) = Seg.dmin s1

    xmax0 : (s1 : Seg0 x1) → X
    xmax0 (inl s1) = x0
    xmax0 (inr s1) = x1

    dmax0 : (s1 : Seg0 x1) → D0 s1 (xmax0 s1)
    dmax0 (inl s1) = Seg≠.dmax s1
    dmax0 (inr s1) = Seg.dmax s1

    R0 : (s1 : Seg0 x1) → Rel (D0 s1)
    R0 (inl s1) = Seg≠.R s1
    R0 (inr s1) = Seg.R s1

    ir0 : (s1 : Seg0 x1) → is-irrefl (R0 s1)
    ir0 (inl s1) = Seg≠.ir s1
    ir0 (inr s1) = Seg.ir s1

    st0 : (s1 : Seg0 x1) → {x1 : X} → {d1 : D0 s1 x1} →
          {x2 : X} → {d2 : D0 s1 x2} →
          (r1 : R0 s1 d1 d2) → (e : x1 ≡ x2) → ⊥ {lzero}
    st0 s1 = strict {D = D0 s1} (R0 s1) (ir0 s1)

open SegmentDefinitions public


module Segmentx0 {X : Set} {x0 : X} (e : X ≃ X) (i : X → X)
                 (i0 : i x0 ≐ x0) (e0 : f e x0 ≢ x0)
                 where
  open Seg

  seg-x0 : Seg x0 e i x0 x0
  D seg-x0 x = x ≡ x0
  d0 seg-x0 = refl
  dmin seg-x0 = refl
  dmax seg-x0 = refl
  ac seg-x0 n refl _ = i0 (λ i0 → n i0)
  R seg-x0 _ _ = ⊥
  -- rp seg-x0 ()
  -- ir seg-x0 ()
  -- tr seg-x0 ()
  tc seg-x0 e1 e2 = inr (inl (λ k → k (e1 ● ! e2)))
  mn seg-x0 e1 n1 = n1 (! e1)
  mx seg-x0 e1 n1 = n1 e1
  ex seg-x0 refl = e0
  --  ds seg-x0 ()
  f (cl seg-x0) (_ , ())
  g (cl seg-x0) (_ , ())
  η (cl seg-x0) (_ , ())
  h (cl seg-x0) = g (cl seg-x0)
  ε (cl seg-x0) (_ , ())

open Segmentx0 public


module SegmentEquality {X : Set} where

  record Preseg (x0 : X) (s : X → X) (xmin xmax : X) : Set1 where
    constructor preseg
    field
      D : (x : X) → Set
      d0 : D x0
      dmin : D xmin
      dmax : D xmax
      R : Rel D
      pr : rel-is-prop R
      cl : is-closed s R pr dmin dmax

  module _ {x0 : X} {s : X → X} {xmin xmax : X} where
    open Preseg
    record PresegEqData (p1 p2 : Preseg x0 s xmin xmax) : Set1 where
      field
        Deq    : (x1 : X) → D p1 x1 ≃ D p2 x1
        Deq'   : D p1 ≡ D p2
        Deqcoh : g fam-eqv Deq ≡ Deq'

        d0eq    : g (Deq x0) (d0 p2) ≡ d0 p1
        d0eq'   : tpt (λ D → D x0) (! Deq') (d0 p2) ≡ d0 p1
        d0eqcoh : elem-fam-eq Deq Deqcoh d0eq ≡ d0eq'

        dmineq    : g (Deq xmin) (dmin p2) ≡ dmin p1
        dmineq'   : tpt (λ D → D xmin) (! Deq') (dmin p2) ≡ dmin p1
        dmineqcoh : elem-fam-eq Deq Deqcoh dmineq ≡ dmineq'

        dmaxeq    : g (Deq xmax) (dmax p2) ≡ dmax p1
        dmaxeq'   : tpt (λ D → D xmax) (! Deq') (dmax p2) ≡ dmax p1
        dmaxeqcoh : elem-fam-eq Deq Deqcoh dmaxeq ≡ dmaxeq'

        Req    : f-rel-eqv Deq (R p1) (R p2) × g-rel-eqv Deq (R p1) (R p2)
        Req'   : (λ {x1} → tpt Rel Deq' (R p1) {x1}) ≡ R p2
        Reqcoh : rel-eq Deq Deqcoh (pr p1) (pr p2) Req ≡ Req'

        preq' : (λ {x1} {d1} {x2} {d2} →
                   tpt2 (λ D → rel-is-prop {D = D}) Deq' Req' (pr p1)
                        {x1} {d1} {x2} {d2}) ≡
                pr p2

        cleq : cl-data* Deq (R p1) (pr p1) (pr p2) Req
                        (dmin p1) (dmin p2) dmaxeq (cl p1) (cl p2)


  module _ {x0 : X} {s : X → X} {xmin xmax : X}
           {p1 p2 : Preseg x0 s xmin xmax}
           (ir2 : is-irrefl (Preseg.R p2))
           (tr2 : is-trans (Preseg.R p2)) where
    open Preseg
    preseg-eq : PresegEqData p1 p2 → p1 ≡ p2
    preseg-eq record { Deq = Deq ; Deq' = refl ; Deqcoh = Deqcoh
                     ; d0eq = d0eq ; d0eq' = refl ; d0eqcoh = d0eqcoh
                     ; dmineq = dmineq ; dmineq' = refl ; dmineqcoh = dmineqcoh
                     ; dmaxeq = dmaxeq ; dmaxeq' = refl ; dmaxeqcoh = dmaxeqcoh
                     ; Req = Req ; Req' = refl ; Reqcoh = Reqcoh
                     ; preq' = refl ; cleq = cleq } =
      ap (λ w → preseg (D p2) (d0 p2) (dmin p2) (dmax p2) (R p2) (pr p2)
                        (λ {x2} → w {x2}))
         (closed-eq* Deq Deqcoh Req {pr1 = pr p1} Reqcoh refl dmineq dmineqcoh
                   dmaxeq dmaxeqcoh cleq)

  module _ {x0 : X} (e : X ≃ X) (i : X → X)
           {xmin xmax : X} (p : Preseg x0 (f e) xmin xmax) where
    open Preseg p

    record is-seg : Set where
      constructor isseg
      field
        ac : is-anticlosed i D
        ir : is-irrefl R
        tr : is-trans R
        tc : is-trich R
        mn : is-min R dmin
        mx : is-max R dmax
        ex : extensive (f e) R
        ds : is-disc (f e) R
    open is-seg
    
    is-seg-is-prop : is-prop is-seg
    is-seg-is-prop s1 s2 =
      ap (λ w → isseg (λ {x} → w {x}) (ir s1) (tr s1) (tc s1) (mn s1)
                       (mx s1) (ex s1) (ds s1))
         {x2 = (λ {x} → (ac s2) {x})}
         (is-prop-pi' (λ {_} → is-prop-pi (λ _ →
          is-prop-pi (λ _ → is-prop-pi (λ _ ())))) _ _) ●
      ap (λ w → isseg (ac s2) (λ {x1} {d1} {d2} → w {x1} {d1} {d2})
                       (tr s1) (tc s1) (mn s1) (mx s1) (ex s1) (ds s1))
         {x2 = (λ {x1} {d1} {d2} → (ir s2) {x1} {d1} {d2})}
         (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
          is-prop-pi' (λ {_} → is-prop-pi (λ _ ())))) _ _) ●
      ap (λ w → isseg (ac s2) (ir s2)
                       (λ {x1} {d1} {x2} {d21} {d22} {x3} {d3} →
                          w {x1} {d1} {x2} {d21} {d22} {x3} {d3})
                       (tc s1) (mn s1) (mx s1) (ex s1) (ds s1))
         {x2 = (λ {x1} {d1} {x2} {d21} {d22} {x3} {d3} →
                  (tr s2) {x1} {d1} {x2} {d21} {d22} {x3} {d3})}
         (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
          is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
          is-prop-pi' (λ {_} → is-prop-pi (λ _ →
          is-prop-pi (λ _ → pr))))))))) _ _) ●
      ap (λ w → isseg (ac s2) (ir s2) (tr s2) (λ {x1} → w {x1}) (mn s1)
                       (mx s1) (ex s1) (ds s1))
         {x2 = (λ {x1} → (tc s2) {x1})}
         (is-prop-pi' (λ {_} → is-prop-pi (λ d1 → is-prop-pi' (λ {_} →
          is-prop-pi (λ d2 → trich-is-prop R pr (ir s2) (tr s2) d1 d2)))) _ _) ●
      ap (λ w → isseg (ac s2) (ir s2) (tr s2) (tc s2) (λ {x1} → w {x1})
                       (mx s1) (ex s1) (ds s1))
         {x2 = (λ {x1} → (mn s2) {x1})}
         (is-prop-pi' (λ {_} → is-prop-pi (λ _ → is-prop-pi (λ _ → pr))) _ _) ●
      ap (λ w → isseg (ac s2) (ir s2) (tr s2) (tc s2) (mn s2) (λ {x1} → w {x1})
                       (ex s1) (ds s1))
         {x2 = (λ {x1} → (mx s2) {x1})}
         (is-prop-pi' (λ {_} → is-prop-pi (λ _ → is-prop-pi (λ _ → pr))) _ _) ●
      ap (λ w → isseg (ac s2) (ir s2) (tr s2) (tc s2) (mn s2) (mx s2)
                       (λ {x1} → w {x1}) (ds s1))
         {x2 = (λ {x1} → (ex s2) {x1})}
         (is-prop-pi' (λ {_} → is-prop-pi (λ _ → is-prop-pi (λ _ → pr))) _ _) ●
      ap (λ w → isseg (ac s2) (ir s2) (tr s2) (tc s2) (mn s2) (mx s2) (ex s2)
                       (λ {x1} {d1} {x2} {d2} {d3} → w {x1} {d1} {x2} {d2} {d3}))
         {x2 = (λ {x1} {d1} {x2} {d2} {d3} → (ds s2) {x1} {d1} {x2} {d2} {d3})}
         (is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
          is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi (λ _ →
          is-prop-pi (λ _ ()))))))) _ _)

  module _ {x0 : X} {e : X ≃ X} {i : X → X} {xmin xmax : X} where
    open Preseg
    
    preseg-eqv : Seg x0 e i xmin xmax ≃ Σ (Preseg x0 (f e) xmin xmax) (is-seg e i) 
    f preseg-eqv s = record { Seg s } , record { Seg s }
    g preseg-eqv = _
    η preseg-eqv s = refl
    h preseg-eqv = g preseg-eqv
    ε preseg-eqv s = refl

    seg-eq : {s1 s2 : Seg x0 e i xmin xmax} →
             PresegEqData (record { Seg s1 }) (record { Seg s2 }) →
             s1 ≡ s2
    seg-eq {s2 = s2} d = g (embed preseg-eqv)
                           (pair-eq (preseg-eq (Seg.ir s2) (Seg.tr s2) d ,
                                     is-seg-is-prop e i _ _ _))

    preseg≠-eqv : Seg≠ x0 e i xmin xmax ≃
                  Σ (Preseg x0 (f e) xmin xmax)
                    (λ p → is-seg e i p × (R p) (dmin p) (dmax p))
    f preseg≠-eqv s = record { Seg≠ s } , record { Seg≠ s } , Seg≠.r0 s
    g preseg≠-eqv = _
    η preseg≠-eqv s = refl
    h preseg≠-eqv = g preseg≠-eqv
    ε preseg≠-eqv s = refl

    seg≠-eq : {s1 s2 : Seg≠ x0 e i xmin xmax} →
              PresegEqData (record { Seg≠ s1 }) (record { Seg≠ s2 }) →
              s1 ≡ s2
    seg≠-eq {s2 = s2} d = g (embed preseg≠-eqv)
                            (pair-eq
                              (preseg-eq (Seg≠.ir s2) (Seg≠.tr s2) d ,
                               pair-eq (is-seg-is-prop e i _ _ _ ,
                                        Seg≠.pr s2 _ _)))

    preseg=-eqv : Seg= x0 e i xmin xmax ≃
                  Σ (Preseg x0 (f e) xmin xmax)
                    (λ p → is-seg e i p × ((R p) (dmin p) (dmax p) → ⊥ {lzero}))
    f preseg=-eqv s = record { Seg= s } , record { Seg= s } , Seg=.nr s
    g preseg=-eqv = _
    η preseg=-eqv s = refl
    h preseg=-eqv = g preseg=-eqv
    ε preseg=-eqv s = refl

    seg=-eq : {s1 s2 : Seg= x0 e i xmin xmax} →
              PresegEqData (record { Seg= s1 }) (record { Seg= s2 }) →
              s1 ≡ s2
    seg=-eq {s2 = s2} d = g (embed preseg=-eqv)
                            (pair-eq
                              (preseg-eq (Seg=.ir s2) (Seg=.tr s2) d ,
                               pair-eq (is-seg-is-prop e i _ _ _ ,
                                        is-prop-pi (λ _ ()) _ _)))

open SegmentEquality using (Preseg ; preseg ; PresegEqData
                           ; seg-eq ; seg≠-eq ; seg=-eq) public
