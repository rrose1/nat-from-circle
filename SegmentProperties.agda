{-# OPTIONS --without-K #-}
module SegmentProperties where

open import UTT


module _ {X : Set} where
  module _ (D : X → Set) where
    Rel : Set1
    Rel = {x1 : X} → (d1 : D x1) → {x2 : X} → (d2 : D x2) → Set

  module _ {D : X → Set} (R : Rel D) where
    rel-is-prop : Set
    rel-is-prop = {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
                  is-prop (R d1 d2)

  module _ {D1 D2 : X → Set} (e1 : (x : X) → D1 x ≃ D2 x)
           (R1 : Rel D1) (R2 : Rel D2) where
    f-rel-eqv : Set
    f-rel-eqv = {x1 x2 : X} → {d1 : D2 x1} → {d2 : D2 x2} →
                R1 (g (e1 x1) d1) (g (e1 x2) d2) →
                R2 d1 d2

    g-rel-eqv : Set
    g-rel-eqv = {x1 x2 : X} → {d1 : D2 x1} → {d2 : D2 x2} →
                R2 d1 d2 →
                R1 (g (e1 x1) d1) (g (e1 x2) d2)

  module _ {D : X → Set} (R : Rel D) where
    is-irrefl : Set
    is-irrefl = {x1 : X} → {d1 : D x1} → {d2 : D x1} → (r1 : R d1 d2) → ⊥

  module _ {D : X → Set} (R : Rel D) (ir : is-irrefl R) where
    strict : {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
             (r1 : R d1 d2) → (e : x1 ≡ x2) → ⊥ {lzero}
    strict {x1 = x1} {x2 = x2} r refl = ir r

  module _ {D : X → Set} (R : Rel D) where
    is-trans : Set
    is-trans = {x1 : X} → {d1 : D x1} →
               {x2 : X} → {d21 : D x2} → {d22 : D x2} →
               {x3 : X} → {d3 : D x3} →
               (r1 : R d1 d21) → (r2 : R d22 d3) → R d1 d3

  module _ {D : X → Set} (R : Rel D) where
    is-trich : Set
    is-trich = {x1 : X} → (d1 : D x1) → {x2 : X} → (d2 : D x2) →
               R d1 d2 ⊎ (x1 ≐ x2) ⊎ R d2 d1

  module _ {D : X → Set} (R : Rel D) (pr : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) where
    trich-is-prop : {x1 : X} → (d1 : D x1) → {x2 : X} → (d2 : D x2) →
                    is-prop (R d1 d2 ⊎ (x1 ≐ x2) ⊎ R d2 d1)
    trich-is-prop {x1} d1 {x2} d2 (inl r1) (inl r2) =
      ap inl (pr r1 r2)
    trich-is-prop {x1} d1 {x2} d2 (inl r1) (inr (inl e1)) =
      rec⊥ (e1 (λ e1 → strict R ir r1 e1))
    trich-is-prop {x1} d1 {x2} d2 (inl r1) (inr (inr r2)) =
      rec⊥ (ir (tr r1 r2))  
    trich-is-prop {x1} d1 {x2} d2 (inr (inl e1)) (inl r1) =
      rec⊥ (e1 (λ e1 → strict R ir r1 e1))
    trich-is-prop {x1} d1 {x2} d2 (inr (inl e1)) (inr (inl e2)) =
      ap inr (ap inl (is-prop-pi (λ _ ()) e1 e2))
    trich-is-prop {x1} d1 {x2} d2 (inr (inl e1)) (inr (inr r1)) =
      rec⊥ (e1 (λ e → strict R ir r1 (! e)))
    trich-is-prop {x1} d1 {x2} d2 (inr (inr r1)) (inl r2) =
      rec⊥ (ir (tr r1 r2))
    trich-is-prop {x1} d1 {x2} d2 (inr (inr r1)) (inr (inl e1)) =
      rec⊥ (e1 (λ e → strict R ir r1 (! e)))
    trich-is-prop {x1} d1 {x2} d2 (inr (inr r1)) (inr (inr r2)) =
      ap inr (ap inr (pr r1 r2))

  module _ {D : X → Set} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R) where

    tpt-rel : {x1 x2 : X} → (e1 : x1 ≐ x2) → {d1 : D x1} → {d2 : D x2} →
              {x3 x4 : X} → (e2 : x3 ≐ x4) → {d3 : D x3} → {d4 : D x4} →
              R d1 d3 → R d2 d4
    tpt-rel {_} {x2} e1 {_} {d2} {_} {x4} e2 {_} {d4} r1 = aux (tc d2 d4)
      module tpt-rel where
      aux : R d2 d4 ⊎ (x2 ≐ x4) ⊎ R d4 d2 → R d2 d4
      aux (inl r2) = r2
      aux (inr (inl e3)) =
        rec⊥ (e1 (λ e1 → e2 (λ e2 → e3 (λ e3 →
          strict R ir r1 (e1 ● e3 ● ! e2)))))
      aux (inr (inr r2)) =
        rec⊥ (e1 (λ {refl → e2 (λ {refl → ir (tr r1 r2)})}))

  module _ {D : X → Set} (R : Rel D) (pr : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R) where
    forget-rel-1 : {x1 x2 : X} → {d1 : D x1} → {d2 : D x2} → R d1 d2 →
                   Σ (D x1) (λ d1 → R d1 d2) ≃ D x1
    forget-rel-1 {x1} {x2} {d1} {d2} r1 =
      improper-subtype {P = D}
        (λ d1 → pr {d1 = d1} {d2 = d2})
        (λ r2 → tpt-rel R ir tr tc (λ k → k refl) (λ k → k refl) r2)
        r1

    forget-rel-2 : {x1 x2 : X} → {d1 : D x1} → {d2 : D x2} → R d1 d2 →
                   Σ (D x2) (R d1) ≃ D x2
    forget-rel-2 {x1} {x2} {d1} {d2} r1 =
      improper-subtype {P = D}
        (λ d2 → pr {d1 = d1} {d2 = d2})
        (λ r2 → tpt-rel R ir tr tc (λ k → k refl) (λ k → k refl) r2)
        r1

  module _ (s : X → X) {D : X → Set} (R : Rel D) where
    extensive : Set
    extensive = {x1 : X} → (d1 : D x1) → (d2 : D (s x1)) → R d1 d2

    is-disc : Set
    is-disc = {x1 : X} → {d1 : D x1} →
              {x2 : X} → {d2 : D x2} →
              {d3 : D (s x1)} → (r1 : R d1 d2) → (r2 : R d2 d3) → ⊥

    is-closed : (pr : rel-is-prop R) →
              {x1 : X} → (d1 : D x1) → {x4 : X} → (d4 : D x4) → Set
    is-closed pr d1 d4 = {x2 : X} → (Σ (D x2) (λ d2 → R d2 d4)) ≃
                                    (Σ (D (s x2)) (λ d3 → R d1 d3))

  module _ (e1 : X ≃ X) {D : X → Set} (R : Rel D) (ex : extensive (f e1) R) where
    shift-ex : {x1 : X} → (d1 : D (g e1 x1)) → (d2 : D x1) → R d1 d2
    shift-ex {x1} d1 d2 =
      tpt2 (λ x d → R d1 {x} d)
           (ε' e1 x1)
           (ε (tpt-eqv D (ε' e1 x1)) d2)
           (ex d1 (g (tpt-eqv D (ε' e1 x1)) d2))

  module _ (s t : X → X) (s-t : (x : X) → s (t x) ≡ x)
           {D : X → Set} (R : Rel D) (pr : rel-is-prop R)
           {x1 : X} {d1 : D x1} {x4 : X} {d4 : D x4}
           (cl : is-closed s R pr d1 d4) where
    shift-cl : {x2 : X} → Σ (D (t x2)) (λ d2 → R d2 d4) ≃
                          Σ (D x2) (λ d3 → R d1 d3)
    shift-cl {x2} = tpt-eqv (λ x → (Σ (D x) (R d1))) (s-t x2) ∘e cl {x2 = t x2}


  module _ (s t : X → X) (t-s : (x : X) → t (s x) ≡ x)
           {D : X → Set} (R : Rel D) (pr : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (ex : extensive s R) (ds : is-disc s R)
           {x1 : X} {d1 : D x1} {x2 : X} {d2 : D x2}
           {x3 : X} {d3 : D x3} {x4 : X} {d4 : D x4}
           (cl : is-closed s R pr d1 d4)
           (r1 : R d2 d4) (r2 : R d3 d4) (r3 : R d2 d3) where
    cl-mono : R (fst (f cl (d2 , r1))) (fst (f cl (d3 , r2)))
    cl-mono = aux (tc (fst (f cl (d2 , r1))) (fst (f cl (d3 , r2))))  
      module cl-mono where
      aux : R (fst (f cl (d2 , r1))) (fst (f cl (d3 , r2))) ⊎ (s x2 ≐ s x3) ⊎
            R (fst (f cl (d3 , r2))) (fst (f cl (d2 , r1))) →
            R (fst (f cl (d2 , r1))) (fst (f cl (d3 , r2)))
      aux (inl r5) = r5
      aux (inr (inl e1)) =
        rec⊥ (e1 (λ e1 → strict R ir r3 (! (t-s x2) ● ap t e1 ● t-s x3)))
      aux (inr (inr r5)) =
        rec⊥ (ds r3 (tr (ex d3 (fst (f cl (d3 , r2)))) r5))

  module _ (s : X → X)
           {D : X → Set} (R : Rel D) (pr : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (ex : extensive s R) (ds : is-disc s R)
           {x1 : X} {d1 : D x1} {x2 : X} {d2 : D (s x2)}
           {x3 : X} {d3 : D (s x3)} {x4 : X} {d4 : D x4}
           (cl : is-closed s R pr d1 d4)
           (r1 : R d1 d2) (r2 : R d1 d3) (r3 : R d2 d3) where
    cl-inv-mono : R (fst (g cl (d2 , r1))) (fst (g cl (d3 , r2))) 
    cl-inv-mono = aux (tc (fst (g cl (d2 , r1))) (fst (g cl (d3 , r2))))
      module cl-inv-mono where
      aux : R (fst (g cl (d2 , r1))) (fst (g cl (d3 , r2))) ⊎ (x2 ≐ x3) ⊎
            R (fst (g cl (d3 , r2))) (fst (g cl (d2 , r1))) →
            R (fst (g cl (d2 , r1))) (fst (g cl (d3 , r2)))
      aux (inl r5) = r5
      aux (inr (inl e1)) =
        rec⊥ (e1 (λ e1 → strict R ir r3 (ap s e1)))
      aux (inr (inr r5)) =
        rec⊥ (ds (tr r5 (ex (fst (g cl (d2 , r1))) d2)) r3)


  module _ {D : X → Set} (R : Rel D) where
    is-min : {xmin : X} → (dmin : D xmin) → Set
    is-min {xmin} dmin =
      {x1 : X} → (d1 : D x1) → (n1 : xmin ≢ x1) → R dmin d1

    is-max : {xmax : X} → (dmax : D xmax) → Set
    is-max {xmax} dmax =
      {x1 : X} → (d1 : D x1) → (n1 : x1 ≢ xmax) → R d1 dmax                   


  module _ {x1 : X} {D : X → Set} {d1 : D x1} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) where

    strict-min : (mn : is-min R d1) → {x2 : X} → {d2 : D x2} → R d2 d1 → ⊥
    strict-min mn {d2 = d2} r1 = ir (tr r1 (mn d2 (λ e1 → strict R ir r1 (! e1))))

    strict-max : (mx : is-max R d1) → {x2 : X} → {d2 : D x2} → R d1 d2 → ⊥
    strict-max mx {d2 = d2} r1 = ir (tr r1 (mx d2 (λ e1 → strict R ir r1 (! e1))))

  module _ {x1 : X} (e1 : X ≃ X) {D : X → Set} {d1 : D x1} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R)
           (mn : is-min R d1) (ex : extensive (f e1) R) where

    under-1 : D (g e1 x1) → ⊥
    under-1 d2 = strict-min R ir tr mn (shift-ex e1 R ex d2 d1)

  module _ {x1 : X} (e1 : X ≃ X) {D : X → Set} {d1 : D x1} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R)
           (mx : is-max R d1) (ex : extensive (f e1) R) where

    over-1 : D (f e1 x1) → ⊥
    over-1 d2 = strict-max R ir tr mx (ex d1 d2)
  
  module _ {x1 : X} {D : X → Set} {d1 : D x1} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R) (mx : is-max R d1)
           {x2 : X} (d2 : D x2) where

    di-max : R d2 d1 ⊎ (x2 ≐ x1)
    di-max = aux (tc d2 d1)
      module di-max where
      aux : R d2 d1 ⊎ (x2 ≐ x1) ⊎ R d1 d2 → R d2 d1 ⊎ (x2 ≐ x1)
      aux (inl r1) = inl r1
      aux (inr (inl e1)) = inr e1
      aux (inr (inr r1)) = rec⊥ (strict-max R ir tr mx r1)

  module _ {x1 : X} {D : X → Set} {d1 : D x1} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (mn : is-min R d1)
           {x2 : X} (d2 : D x2) where

    di-min : R d1 d2 ⊎ (x1 ≐ x2)
    di-min = aux (tc d1 d2)
      module di-min where
      aux : R d1 d2 ⊎ (x1 ≐ x2) ⊎ R d2 d1 → R d1 d2 ⊎ (x1 ≐ x2)
      aux (inl r1) = inl r1
      aux (inr (inl e1)) = inr e1
      aux (inr (inr r1)) = rec⊥ (strict-min R ir tr mn r1)

  module _ (i : X → X) (D : X → Set) where
    is-anticlosed : Set
    is-anticlosed = {x1 : X} → (n1 : i x1 ≢ x1) → (d1 : D x1) → (d2 : D (i x1)) → ⊥


  module _ {x0 : X} (e : X ≃ X) {i : X → X}
           (i0 : i x0 ≡ x0)
           (anc : (x : X) → i (f e x) ≡ g e (i x))
           (ee0 : f e (f e x0) ≢ x0)
           {xmin xmax : X}
           {D : X → Set}
           (d0 : D x0) {dmin : D xmin} {dmax : D xmax}
           {R : Rel D} (pr : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (mn : is-min R dmin) (mx : is-max R dmax) (ex : extensive (f e) R)
           (cl : is-closed (f e) R pr dmin dmax)
           (ac : is-anticlosed i D)
           where
    x0-is-extremal : (x0 ≐ xmin) ⊎ (x0 ≐ xmax)
    x0-is-extremal = aux2 (di-min R ir tr tc mn d0)
      module x0-is-extremal where
      aux1 : R dmin d0 → R d0 dmax ⊎ (x0 ≐ xmax) → (x0 ≐ xmin) ⊎ (x0 ≐ xmax)
      aux1 r1 (inl r2) = rec⊥ 
        (ac (λ e1 → ee0 (g (adj e) (! e1 ● anc x0) ● i0))
            (fst (f cl (d0 , r2)))
            (tpt D (! (anc x0))
                 (fst (g (shift-cl (f e) (g e) (ε' e) R pr cl)
                         (tpt D (! i0) d0 ,
                          tpt-rel R ir tr tc (λ k → k refl) (λ k → k (! i0)) r1)))))
      aux1 r (inr e) = inr e

      aux2 : R dmin d0 ⊎ (xmin ≐ x0) → (x0 ≐ xmin) ⊎ (x0 ≐ xmax)
      aux2 (inl r) = aux1 r (di-max R ir tr tc mx d0)
      aux2 (inr e) = inl (λ k → e (λ e → k (! e)))

  module _ {x0 : X} (e : X ≃ X) {i : X → X}
           (i0 : i x0 ≡ x0)
           (anc : (x : X) → i (f e x) ≡ g e (i x))
           (eee0 : f e (f e (f e x0)) ≢ x0)
           (eeee0 : f e (f e (f e (f e x0))) ≢ x0)
           {xmin xmax : X}
           {D : X → Set}
           (d0 : D x0) {dmin : D xmin} {dmax : D xmax}
           {R : Rel D} (pr : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (mn : is-min R dmin) (mx : is-max R dmax) (ex : extensive (f e) R)
           (cl : is-closed (f e) R pr dmin dmax)
           (ac : is-anticlosed i D)
           where
    over-2 : D (f e (f e xmax)) → ⊥ {lzero}
    over-2 d1 = aux (x0-is-extremal e i0 anc ee0 d0 pr ir tr tc mn mx ex cl ac)
                    (di-min R ir tr tc mn d1)
      module over-2 where

      ee0 : f e (f e x0) ≢ x0
      ee0 e1 = eeee0 (ap (λ x → f e (f e x)) e1 ● e1)

      gege0=iee0 : g e (g e x0) ≡ i (f e (f e x0))
      gege0=iee0 = ! (ap (λ x → g e (g e x)) i0) ●
                   ! (ap (g e) (anc x0)) ●
                   ! (anc (f e x0))
      
      iee0≠ee0 : i (f e (f e x0)) ≢ f e (f e x0)
      iee0≠ee0 e1 =
        eeee0 (g (adj (e ∘e e)) (! e1 ● ! gege0=iee0))
      
      sc = shift-cl (f e) (g e) (ε' e) R pr cl

      aux : (x0 ≐ xmin) ⊎ (x0 ≐ xmax) → R dmin d1 ⊎ (xmin ≐ f e (f e xmax)) → ⊥
      aux _ (inl r1) = over-1 e R ir tr mx ex (fst (g cl (d1 , r1)))
      aux (inl e0) (inr e1) =
        e0 (λ e0 → e1 (λ e1 →
          ac iee0≠ee0
             (fst (f cl
               (fst (f cl
                 (d0 , mx d0 (λ e2 → ee0 (ap (λ x → f e (f e x)) e2 ●
                                          ! e1 ● ! e0)))) ,
                mx _ (λ e2 → eee0 (ap (λ x → f e (f e x)) e2 ●
                                   ! e1 ● ! e0)))))
             (tpt D (f (adj (e ∘e e)) (! e1 ● ! e0)  ●
                     gege0=iee0) dmax)))
      
      aux (inr e0) (inr e1) =
        e0 (λ e0 → e1 (λ e1 →
          ac iee0≠ee0
             (tpt D (! (ap (λ x → f e (f e x)) e0)) d1)
             (tpt D gege0=iee0
                  (fst (g sc
                    (fst (g sc
                      (d0 , mn d0 (λ e2 → ee0 (ap (λ x → f e (f e x)) e0 ●
                                               ! e1 ● e2)))),
                      mn _ (λ e2 → eee0 (ap (λ x → f e (f e (f e x))) e0 ●
                                        ! (ap (f e) e1) ●
                                        g (adj e) e2))))))))

    under-2 : D (g e (g e xmin)) → ⊥ {lzero}
    under-2 d1 = aux (di-max R ir tr tc mx d1)
      module under-2 where
      aux : R d1 dmax ⊎ (g e (g e xmin) ≐ xmax) → ⊥
      aux (inl r1) =
        under-1 e R ir tr mn ex
                    (fst (f (shift-cl (f e) (g e) (ε' e) R pr cl)
                            (d1 , r1)))
      aux (inr e1) =
        e1 (λ e1 → over-2 (tpt D (! (g (adj (e ∘e e)) (! e1))) dmin))

  module _ {x0 : X} (e : X ≃ X) {i : X → X}
           (i0 : i x0 ≡ x0) (i0-inv : {x : X} → i x ≡ x → x ≡ x0)
           (anc : (x : X) → i (f e x) ≡ g e (i x))
           (e≠i : (x : X) → f e x ≢ i x)
           where
    ee0 : f e (f e x0) ≢ x0
    ee0 e1 = e≠i _ (i0-inv (anc x0 ● ! (f (adj e) (e1 ● ! i0))) ● ! i0)

    eee0 : f e (f e (f e x0)) ≢ x0
    eee0 e1 = e≠i (f e x0) (f (adj e) (e1 ● ! i0) ● ! (anc x0))

    eeee0 : f e (f e (f e (f e x0))) ≢ x0
    eeee0 e1 = ee0 (i0-inv (anc (f e x0) ●
                            ap (g e) (anc x0) ●
                            ! (f (adj (e ∘e e)) (e1 ● ! i0))))


  {- TODO : Refactor using record types to organize equality input
            data (cf. Presegments) -}

  module _ {D1 D2 : X → Set} (e1 : (x : X) → D1 x ≃ D2 x) where
    elem-fam-eqv : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
                   {x : X} → {d1 : D1 x} → {d2 : D2 x} →
                   (g (e1 x) d2 ≡ d1) ≃ (tpt (λ D → D x) (! e2) d2 ≡ d1)
    f (elem-fam-eqv {refl} β {x1} {d1} {d2}) e2 =
      ! (ap (λ e → g e d2) (ap (λ D → D x1) (g (adj' fam-eqv) β))) ● e2
    g (elem-fam-eqv {refl} β {x1} {d1} {d2}) e2 =
      ap (λ e → g e d2) (ap (λ D → D x1) (g (adj' fam-eqv) β)) ● e2
    η (elem-fam-eqv {refl} β) e2 = ε (lcomp-eqv _) e2
    h (elem-fam-eqv β) = g (elem-fam-eqv β)
    ε (elem-fam-eqv {refl} β) e2 = η (lcomp-eqv _) e2

    elem-fam-eq : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
                  {x1 : X} → {d1 : D1 x1} → {d2 : D2 x1} →
                  g (e1 x1) d2 ≡ d1 → tpt (λ D → D x1) (! e2) d2 ≡ d1
    elem-fam-eq β = f (elem-fam-eqv β)


  module RelEqv {D1 D2 : X → Set} (e1 : (x1 : X) → D1 x1 ≃ D2 x1) where
    coh : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
          {R1 : Rel D1} → {x1 x2 : X} → {d1 : D2 x1} → {d2 : D2 x2} →
          tpt Rel e2 R1 d1 d2 ≡ R1 (g (e1 x1) d1) (g (e1 x2) d2)
    coh {refl} α {R1} {x1 = x1} {x2} {d1} {d2} =
      ap (R1 d1) {x2 = (g (e1 x2) d2)}
         (! (ap (λ e → (g (e x2) d2)) (! (ε' fam-eqv e1) ● ap (f fam-eqv) α))) ●
      ap (λ d → R1 d _) {x2 = (g (e1 x1) d1)}
         (! (ap (λ e → (g (e x1) d1)) (! (ε' fam-eqv e1) ● ap (f fam-eqv) α)))

    rel-eqv : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
              {R1 : Rel D1} → {R2 : Rel D2} →
              (pr1 : rel-is-prop R1) → (pr2 : rel-is-prop R2) →
              f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2 ≃
              ((λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2)
    f (rel-eqv α pr1 pr2) (f1 , g1) =
      funext' (λ {x1} → funext (λ d1 →
      funext' (λ {x2} → funext (λ d2 →
      coh α ● ua (biinv f1 g1 (λ _ → pr1 _ _) g1 (λ _ → pr2 _ _)) ))))

    g (rel-eqv α {R1 = R1} pr1 pr2) e3 =
      ((λ {x1} {x2} {d1} {d2} →
          g (f tpt-id-eqv (ap (λ R → R d1 d2) (! e3) ● coh α))) ,
       (λ {x1} {x2} {d1} {d2} →
          f (f tpt-id-eqv (ap (λ R → R d1 d2) (! e3) ● coh α))))

    η (rel-eqv α pr1 pr2) (f1 , g1) =
      pair-eq
       ((is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ → pr2))))) _ _) ,
         is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ → pr1))))) _ _)

    h (rel-eqv α pr1 pr2) = g (rel-eqv α pr1 pr2)

    ε (rel-eqv α pr1 pr2) e3 =
      f (adj' happly'-eqv) (funext' (λ {x1} →
      f (adj' happly-eqv) (funext (λ d1 →
      f (adj' happly'-eqv) (funext' (λ {x2} →
      f (adj' happly-eqv) (funext (λ d2 →
        hprop-is-set pr2 _ _ ))))))))

    rel-eq : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
             {R1 : Rel D1} → {R2 : Rel D2} →
             (pr1 : rel-is-prop R1) → (pr2 : rel-is-prop R2) →
             f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2 →
             (λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2
    rel-eq α pr1 pr2 = f (rel-eqv α pr1 pr2)

  open RelEqv using (rel-eqv ; rel-eq) public

  module _ {D1 D2 : X → Set} (e1 : (x1 : X) → D1 x1 ≃ D2 x1) where
    rel-is-prop-eq : {e2 : D1 ≡ D2} → (α : g fam-eqv e1 ≡ e2) →
                     {R1 : Rel D1} → {R2 : Rel D2} →
                     (e3 : f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2) →
                     {pr1 : rel-is-prop R1} → {pr2 : rel-is-prop R2} →
                     {e4 : (λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2} →
                     (rel-eq e1 α pr1 pr2 e3 ≡ e4) →
                     (λ {x1} {d1} {x2} {d2} →
                        tpt2 (λ D → rel-is-prop {D = D}) e2 e4 pr1
                                                {x1} {d1} {x2} {d2}) ≡ pr2
    rel-is-prop-eq _ _ _ =
      is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
      is-prop-pi' (λ {_} → is-prop-is-prop _)))) _ _

  module _ {s : X → X} {x1 : X} {x4 : X} where
     closed-tpt : {D1 D2 : (x1 : X) → Set} → (e1 : D1 ≡ D2) →
                  {R1 : Rel D1} → {R2 : Rel D2} →
                  (e2 : (λ {x1} → tpt Rel e1 R1 {x1})≡ R2) →
                  {pr1 : rel-is-prop R1} → {pr2 : rel-is-prop R2} →
                  (e3 : (λ {x1} {d1} {x2} {d2} →
                        tpt2 (λ D → rel-is-prop {D = D}) e1 e2 pr1
                                                {x1} {d1} {x2} {d2}) ≡ pr2) →
                  {d11 : D1 x1} → {d21 : D2 x1} →
                  (e4 : tpt (λ D → D x1) (! e1) d21 ≡ d11) →
                  {d14 : D1 x4} → {d24 : D2 x4} →
                  (e5 : tpt (λ D → D x4) (! e1) d24 ≡ d14) →
                  is-closed s R1 pr1 d11 d14 → is-closed s R2 pr2 d21 d24
     closed-tpt refl refl refl refl refl cl = cl

     module _ {D1 D2 : (x1 : X) → Set} (e1 : (x1 : X) → D1 x1 ≃ D2 x1)
              (R1 : Rel D1) {R2 : Rel D2}
              (pr1 : rel-is-prop R1) (pr2 : rel-is-prop R2)
              (e3 : f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2)
              (d11 : D1 x1) (d21 : D2 x1)
              {d14 : D1 x4} {d24 : D2 x4} (e8 : g (e1 x4) d24 ≡ d14)
              (cl1 : is-closed s R1 pr1 d11 d14) (cl2 : is-closed s R2 pr2 d21 d24)
              where
       cl-data* :  Set
       cl-data* = {x2 : X} → (d22 : D2 x2) →
                  (r1 : R1 (g (e1 x2) d22) d14) → (r2 : R2 d22 d24) →
                   f (e1 (s x2)) (fst (f cl1 (g (e1 x2) d22 , r1))) ≡
                   fst (f cl2 (d22 , r2))

     closed-eq* : {D1 D2 : (x1 : X) → Set} → (e1 : (x1 : X) → D1 x1 ≃ D2 x1) →
                {e2 : D1 ≡ D2} → (α : g fam-eqv e1 ≡ e2) →
                {R1 : Rel D1} → {R2 : Rel D2} →
                (e3 : f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2) →
                {pr1 : rel-is-prop R1} → {pr2 : rel-is-prop R2} →
                {e4 : (λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2} →
                (rel-eq e1 α pr1 pr2 e3 ≡ e4) →
                (e5 : (λ {x1} {d1} {x2} {d2} →
                         tpt2 (λ D → rel-is-prop {D = D}) e2 e4 pr1
                              {x1} {d1} {x2} {d2}) ≡ pr2) →
                {d11 : D1 x1} → {d21 : D2 x1} →
                (e6 : g (e1 x1) d21 ≡ d11) →
                {e7 : tpt (λ D → D x1) (! e2) d21 ≡ d11} →
                  elem-fam-eq e1 α e6 ≡ e7 →
                {d14 : D1 x4} → {d24 : D2 x4} →
                (e8 : g (e1 x4) d24 ≡ d14) →
                {e9 : tpt (λ D → D x4) (! e2) d24 ≡ d14} →
                  elem-fam-eq e1 α e8 ≡ e9 →
                {cl1 : is-closed s R1 pr1 d11 d14} →
                {cl2 : is-closed s R2 pr2 d21 d24} →
                cl-data* e1 R1 pr1 pr2 e3 d11 d21 e8 cl1 cl2 →
                (λ {x2} → closed-tpt e2 e4 e5 e7 e9 cl1 {x2}) ≡ cl2
     closed-eq* e1 {refl} α1 {R1} e3 {pr1} {pr2} {refl} α2 refl e6 {refl}
                α3 e8 {refl} α4 {cl1} {cl2} α5 =
       funext' (λ {x2} →
       biinv-eq (funext (λ w →
       pair-eq (ap
         (λ w → fst (f cl1 w))
         (pair-eq (ap (λ e → g e (fst w))
                      (ap (λ D → D x2)
                          (g (adj fam-eqv) (! α1))) , pr1 _ _)) ●
       ! (ap (λ e → f e (fst (f cl1 (g (e1 x2) (fst w) ,
                    tpt (R1 (g (e1 x2) (fst w))) e8 (snd e3 (snd w))))))
             (ap (λ a → a (s x2))
                 (g (adj' fam-eqv) α1))) ●
       α5 {x2} (fst w) _ (snd w) , pr1 _ _))))
