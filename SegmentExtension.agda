{-# OPTIONS --without-K #-}
module SegmentExtension where

open import UTT
open import SegmentProperties
open import Segment


module IncrementMaxEqv
       {X : Set} {xmin : X}
       (e : X ≃ X) {i : X → X}
       (i0 : i xmin ≡ xmin)
       (i0-inv : {x : X} → i x ≡ x → x ≡ xmin)
       (anc1 : (x : X) → i (f e x) ≡ g e (i x))
       (anc2 : (x : X) → f e (i x) ≡ i (g e x))
       (e≠i : (x : X) → f e x ≢ i x)
       (xmax : X)
       where

  incr-max-eqv : Seg xmin e i xmin xmax ≃ Seg≠ xmin e i xmin (f e xmax)
  incr-max-eqv = eqv
    module incr-max-eqv where
    D-f-eqv : (X → Set) → X → Set
    D-f-eqv D x = D x ⊎ D (g e x) × (g e x ≐ xmax)

    D-g-eqv : (X → Set) → X → Set
    D-g-eqv D x = D x × (x ≢ f e xmax)

    module _ (s : Seg xmin e i xmin xmax) where
      open Seg s
      f-eqv : Seg≠ xmin e i xmin (f e xmax)
      Seg≠.D f-eqv = D-f-eqv D

      Seg≠.d0 f-eqv = inl d0

      Seg≠.dmin f-eqv = inl dmin

      Seg≠.dmax f-eqv = inr (tpt D (! (η e xmax)) dmax , λ k → k (η e xmax))

      Seg≠.ac f-eqv n (inl d1) (inl d2) = ac n d1 d2
      Seg≠.ac f-eqv {x1 = x1} n (inl d1) (inr (d2 , e2)) = aux (dimx d1)
        module ac-f-eqv-l-r where
        aux : R d1 dmax ⊎ (x1 ≐ xmax) → ⊥
        aux (inl r1) =
          ac (λ e3 → e2 (λ e2 →
            smn {d2 = d1}
                (ri (λ k → k refl)
                    (λ k → k (! e2 ● ! (anc1 x1) ● e3 ● i0-inv e3))
                    r1)))
             (fst (f cl (d1 , r1)))
             (tpt D (! (anc1 x1)) d2)
        aux (inr e3) = 
          e2 (λ e2 → e3 (λ e3 →
            e≠i _ (g (adj e) (e3 ● ! e2))))

      Seg≠.ac f-eqv {x1 = x1} n (inr (d1 , e1)) (inl d2) = aux (dimx d2)
        module ac-f-eqv-r-l where
        aux : R d2 dmax ⊎ (i x1 ≐ xmax) → ⊥
        aux (inl r1) =
          ac (λ e3 → e1 (λ e1 →
                smn {d2 = d2} (ri (λ k → k refl) (λ k → k (! e1 ● i0-inv e3)) r1)))
             d1
             (tpt D (anc2 x1) (fst (f cl (d2 , r1))))
        aux (inr e2) =
          e1 (λ e1 → e2 (λ e2 → e≠i (g e x1) (ap (f e ) (e1 ● ! e2) ● anc2 x1)))

      Seg≠.ac f-eqv {x} n (inr (d1 , e1)) (inr (d2 , e2)) =
        e1 (λ e1 → e2 (λ e2 → n (g (embed (!e e)) (e2 ● ! e1))))

      Seg≠.R f-eqv (inl d1) (inl d2) = R d1 d2
      Seg≠.R f-eqv (inl _) (inr _) = ⊤
      Seg≠.R f-eqv (inr _) _ = ⊥

      Seg≠.pr f-eqv {d1 = inl _} {d2 = inl _} = pr
      Seg≠.pr f-eqv {d1 = inl _} {d2 = inr _} = ⊤-is-prop
      Seg≠.pr f-eqv {d1 = inr _} {d2 = inl _} ()
      Seg≠.pr f-eqv {d1 = inr _} {d2 = inr _} ()

      Seg≠.ir f-eqv {d1 = inl _} {inl _} = ir
      Seg≠.ir f-eqv {d1 = inl d1} {inr (d2 , e2)} _ =
       e2 (λ e2 → ov1 (tpt D (g (adj' e) e2) d1))

      Seg≠.tr f-eqv {d1 = inl _} {d21 = inl _} {inl _} {d3 = inl _} r1 r2 = tr r1 r2
      Seg≠.tr f-eqv {d1 = inl _} {d21 = inl _} {inl _} {d3 = inr _} _ _ = tt
      Seg≠.tr f-eqv {d1 = inl _} {d21 = inr (d21 , e1)} {inl d22} {d3 = inl _} =
        rec⊥ (e1 (λ e1 → ov1 (tpt D (g (adj' e) e1) d22)))
      Seg≠.tr f-eqv {d1 = inl _} {d21 = inr (d21 , e1)} {inl d22} {d3 = inr _} =
        rec⊥ (e1 (λ e1 → ov1 (tpt D (g (adj' e) e1) d22)))
        
      Seg≠.tc f-eqv (inl d1) (inl d2) = tc d1 d2
      Seg≠.tc f-eqv (inl _) (inr _) = inl tt
      Seg≠.tc f-eqv (inr _) (inl _) = inr (inr tt)
      Seg≠.tc f-eqv {x1} (inr (d1 , e1)) {x2} (inr (d2 , e2)) =
        inr (inl (λ k → e1 (λ e1 → e2 (λ e2 →
          k (g (embed (!e e)) (e1 ● ! e2))))))

      Seg≠.mn f-eqv (inl d1) n = mn d1 n
      Seg≠.mn f-eqv (inr _) _ = tt

      Seg≠.mx f-eqv (inl _) _ = tt
      Seg≠.mx f-eqv (inr (_ , e1)) n = e1 (λ e1 → n (g (adj' e) e1))

      Seg≠.ex f-eqv (inl d1) (inl d2) = ex d1 d2
      Seg≠.ex f-eqv (inl _) (inr _) = tt
      Seg≠.ex f-eqv (inr (d1 , e1)) (inl d2) =
        e1 (λ e1 → over-2 e i0 anc1
                          (eee0 e i0 i0-inv anc1 e≠i)
                          (eeee0 e i0 i0-inv anc1 e≠i)
                          dmin pr ir tr tc mn mx ex cl ac
                          (tpt D (ap (f e) (g (adj' e) e1)) d2))
      Seg≠.ex f-eqv {x1} (inr (d1 , e1)) (inr (d2 , e2)) =
        e1 (λ e1 → ov1 (tpt D (η e x1 ● ! (ε' e x1) ● ap (f e) e1) d2))

      Seg≠.ds f-eqv {d1 = inl d1} {d2 = inl d2} {inl d3} r1 r2 = ds r1 r2
      Seg≠.ds f-eqv {x1} {d1 = inl d1} {d2 = inl d2} {inr (d3 , e3)} r1 _ = 
        e3 (λ e3 → smx {d2 = d2} (ri (λ k → k (! (η e x1) ● e3)) (λ k → k refl) r1))

      f (Seg≠.cl f-eqv {x2 = x}) (inl d , _) = aux (dimx d)
        module f-cl-f-eqv where
        aux : R d dmax ⊎ (x ≐ xmax) →
              Σ (Seg≠.D f-eqv (f e x))
                (Seg≠.R f-eqv (Seg≠.dmin f-eqv))
        aux (inl r) = inl (fst (f cl (d , r))) , snd (f cl (d , r))
        aux (inr e1) =
          inr (tpt D (! (η e x)) d , λ k → e1 (λ e1 → k (η e x ● e1))) , tt

      g (Seg≠.cl f-eqv {x2 = x}) (inl d , r) =
        inl (fst (g cl (d , r))) , tt
      g (Seg≠.cl f-eqv {x2 = x}) (inr (d1 , e1) , _) =
        inl (tpt D (η e x) d1) , tt

      η (Seg≠.cl f-eqv {x2 = x}) (inl d , tt) =
        pair-eq (aux (dimx d) , ⊤-is-prop _ _)
        module η-cl-f-eqv where
        aux : (a1 : R d dmax ⊎ (x ≐ xmax)) →
              fst (g (Seg≠.cl f-eqv) (f-cl-f-eqv.aux d tt a1)) ≡ inl d
        aux (inl r) = ap inl (ηs pr cl d r _)
        aux (inr e1) = ap inl (ε (tpt-eqv D (η e x)) d)

      h (Seg≠.cl f-eqv) = g (Seg≠.cl f-eqv)

      ε (Seg≠.cl f-eqv {x2 = x}) (inl d1 , r1) =
        pair-eq (aux (dimx (fst (g cl (d1 , r1)))) , pr _ _)
        module ε-cl-f-eqv-l where
        aux : (a1 : R (fst (g cl (d1 , r1))) dmax ⊎ (x ≐ xmax)) →
              fst (f-cl-f-eqv.aux (fst (g cl (d1 , r1))) tt a1) ≡ inl d1
        aux (inl r2) = ap inl (εs pr cl d1 r1 r2)
        aux (inr e1) = rec⊥ (e1 (λ e1 → ov1 (tpt D (ap (f e) e1) d1)))

      ε (Seg≠.cl f-eqv {x2 = x1}) (inr (d1 , e1) , r1) =
        pair-eq (aux (dimx (tpt D (η e x1) d1)) , ⊤-is-prop _ _)
        module ε-cl-f-eqv-r where
        aux : (a1 : R (tpt D (η e x1) d1) dmax ⊎ (x1 ≐ xmax)) →
              fst (f-cl-f-eqv.aux (tpt D (η e x1) d1) tt a1) ≡
              inr (d1 , e1)
        aux (inl r2) = rec⊥ (e1 (λ e1 → st r2 (! (η e x1) ● e1)))
        aux (inr e2) =
          ap inr (pair-eq (η (tpt-eqv D (η e x1)) d1 , is-prop-pi (λ _ ()) _ _))

      Seg≠.r0 f-eqv = tt

    module _ (s : Seg≠ xmin e i xmin (f e xmax)) where
      open Seg≠ s
      g-eqv : Seg xmin e i xmin xmax
      Seg.D g-eqv = D-g-eqv D
      Seg.d0 g-eqv = d0 , st r0
      Seg.dmin g-eqv = dmin , st r0
      Seg.dmax g-eqv = fst (g cl (dmax , r0)) , st (snd (g cl (dmax , r0)))
      Seg.ac g-eqv n (d1 , _) (d2 , _) = ac n d1 d2
      Seg.R g-eqv (d1 , _) (d2 , _) = R d1 d2
      Seg.pr g-eqv = pr
      Seg.ir g-eqv = ir
      Seg.tr g-eqv = tr
      Seg.tc g-eqv (d1 , _) (d2 , _) = tc d1 d2
      Seg.mn g-eqv (d1 , _) n = mn d1 n
      Seg.mx g-eqv {x} (d , n1) n2 = aux (tc d (fst (g cl (dmax , r0))))
        module mx-g-eqv where
        aux : R d (fst (g cl (dmax , r0))) ⊎ (x ≐ xmax) ⊎
              R (fst (g cl (dmax , r0))) d →
              R d (fst (g cl (dmax , r0)))
        aux (inl r) = r
        aux (inr (inl e2)) = rec⊥ (e2 (λ e2 → (n2 e2)))
        aux (inr (inr r)) = rec⊥ (ds r (mx d n1))

      Seg.ex g-eqv (d1 , _) (d2 , _) = ex d1 d2
      Seg.ds g-eqv = ds

      f (Seg.cl g-eqv {x}) ((d1 , n1) , r1) =
        (fst (f cl (d1 , mx d1 n1)) ,
         st (umon (mx d1 n1)
                  (mx (fst (g cl (dmax , r0)))
                      (λ e3 → st (ex (fst (g cl (dmax , r0))) dmax) e3))
                  r1)) ,
        snd (f cl (d1 , mx d1 n1))
      g (Seg.cl g-eqv {x}) ((d1 , n1) , r1) =
        (fst (g cl (d1 , r1)) , st (snd (g cl (d1 , r1)))) ,
        dmon r1 r0 (mx d1 n1)
      η (Seg.cl g-eqv {x}) ((d1 , n1) , r1) =
        pair-eq (pair-eq
          (ηs pr cl d1 (mx d1 n1) _ ,
           is-prop-pi (λ _ ()) _ _) ,
          pr _ _)
      h (Seg.cl g-eqv) = g (Seg.cl g-eqv)
      ε (Seg.cl g-eqv {x}) ((d1 , _) , r2) =
        pair-eq (pair-eq
          (εs pr cl d1 r2 _ ,
           is-prop-pi (λ _ ()) _ _) ,
          pr _ _)

    module _ (s : Seg xmin e i xmin xmax) where
      open Seg s

      open Seg (g-eqv (f-eqv s))
        renaming
        (D to D' ; d0 to d0' ; dmin to dmin' ; dmax to dmax' ; R to R' ; pr to pr' ;
         tc to tc' ; cl to cl' ; ri to ri')
        using ()

      open PresegEqData      
      η-eqv : g-eqv (f-eqv s) ≡ s
      η-eqv = seg-eq eq-data
        module η-eqv where
        Deq-eq-data : (x : X) → D' x ≃ D x
        f (Deq-eq-data x) (inl d , e) = d
        f (Deq-eq-data x) (inr (d , e1) , n) =
          rec⊥ (e1 (λ e1 → (n (g (adj' e) e1))))
        g (Deq-eq-data x) d = inl d , (λ e → ov1 (tpt D e d))
        η (Deq-eq-data x) (inl d , e) =
          pair-eq (refl , is-prop-pi (λ _ ()) _ _)
        η (Deq-eq-data x) (inr (d , e1) , n) =
          rec⊥ (e1 (λ e1 → (n (! (g (adj e) (! e1))))))
        h (Deq-eq-data x) = g (Deq-eq-data x)
        ε (Deq-eq-data x) d = refl

        eq-data : PresegEqData (preseg D' d0' dmin' dmax' R'
                                       (λ {x1} {d1} {x2} {d2} →
                                          pr' {x1} {d1} {x2} {d2}) cl')
                               record { Seg s }
        Deq eq-data = Deq-eq-data
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl

        d0eq eq-data = ap (λ n → (inl d0 , n)) (is-prop-pi (λ _ ()) _ _)
        d0eq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (d0eq eq-data)
        d0eqcoh eq-data = refl

        dmineq eq-data = ap (λ n → (inl dmin , n)) (is-prop-pi (λ _ ()) _ _)
        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl
        
        dmaxeq eq-data = pair-eq (ap inl (! (ε (tpt-eqv D (η e xmax)) dmax)) ,
                                 is-prop-pi (λ _ ()) _ _)
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl

        Req eq-data = id , id
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → pr' {x1} {d1} {x2} {d2})
                 pr (id , id)
        Reqcoh eq-data = refl

        preq' eq-data = rel-is-prop-eq (Deq eq-data) refl (id , id) refl

        -----
        cleq eq-data {x2 = x2} d2 r2 r3 = aux1 _ refl
          module cleq-eq-data where
          aux1 : (a1 : Σ (D' (f e x2)) (R' dmin')) →
                 f cl' ((inl d2 , (λ e → ov1 (tpt D e d2))) , r2) ≡ a1 →
                 f (Deq-eq-data (f e x2)) (fst a1) ≡ fst (f cl (d2 , r3))
          aux1 ((inr (d4 , n) , e1) , r4) β1 =
            rec⊥ (n (λ e2 → e1 (! (η' (!e e) (f e x2)) ● ap (f e) e2)))
          aux1 ((inl d4 , _) , r4) β1 = aux2 (dimx d2) (ap fst (ap fst β1))
            module aux1 where
            aux2 : (a1 : R d2 dmax ⊎ (x2 ≐ xmax)) →
                   fst (f-cl-f-eqv.aux s d2 tt a1) ≡ inl d4 →
                   f (Deq-eq-data (f e x2))
                     (inl d4 , (λ e → ov1 (tpt D e d4))) ≡
                   fst (f cl (d2 , r3))
            aux2 (inl _) β2 =
              ! (inl-eq β2) ● ap (λ r → fst (f cl (d2 , r))) (pr _ _)
            aux2 (inr _) β2 = rec⊥ (inl-neq-inr (! β2))


    module _ (s : Seg≠ xmin e i xmin (f e xmax)) where
      open Seg≠ s

      open Seg≠ (f-eqv (g-eqv s))
        renaming
        (D to D' ; d0 to d0' ; dmin to dmin' ; dmax to dmax' ; R to R' ; pr to pr' ;
         cl to cl' ; dimx to dimx')
        using ()

      open PresegEqData
      
      ε-eqv : f-eqv (g-eqv s) ≡ s
      ε-eqv = seg≠-eq eq-data
        module ε-eqv where
        f-Deq-eq-data : (x : X) → D' x → D x
        f-Deq-eq-data x (inl (d , _)) = d
        f-Deq-eq-data x (inr ((d , n) , e)) =
          fst (f sc (d , (mx d n)))

        eq-data : PresegEqData (preseg D' d0' dmin' dmax' R'
                                       (λ {x1} {d1} {x2} {d2} →
                                          pr' {x1} {d1} {x2} {d2}) cl')
                                 record { Seg≠ s }
        f (Deq eq-data x) = f-Deq-eq-data x
        g (Deq eq-data x) d = aux (dimx d)
          module g-Deq-eq-data where
          aux : R d dmax ⊎ (x ≐ f e xmax) →
                D x × (x ≡ f e xmax → ⊥) ⊎
                (D (g e x) × (g e x ≢ f e xmax)) × (g e x ≐ xmax)
          aux (inl r) = inl (d , st r)
          aux (inr e1) =
            inr ((fst (g sc (d , ri (λ k → k refl) (nn-map ! e1) r0)) ,
                 (λ e2 → ov1 (tpt D (g (adj' e) e2) d))) ,
                 nn-map (f (adj' e)) e1)
        η (Deq eq-data x) (inl (d , n)) = aux _
          module η-Deq-eq-data-l where
          aux : (a1 : R d dmax ⊎ (x ≐ f e xmax)) →
                g-Deq-eq-data.aux x d a1 ≡ inl (d , n)
          aux (inl _) = ap (λ n → inl (d , n)) (is-prop-pi (λ _ ()) _ _)
          aux (inr e) = rec⊥ (e n)
          
        η (Deq eq-data x) (inr ((d , n) , e1)) = aux _
          module η-Deq-eq-data-r where
          aux : (a1 : R (f-Deq-eq-data x (inr ((d , n) , e1))) dmax ⊎
                      (x ≐ f e xmax)) →
                g-Deq-eq-data.aux x _ a1 ≡ inr ((d , n) , e1)
          aux (inl r) = rec⊥ (e1 (f (neg-eqv (!e (adj' e))) (st r)))
          aux (inr _) = 
            ap inr (pair-eq (pair-eq (ηs pr sc d _ _ ,
                                      is-prop-pi (λ _ ()) _ _) ,
                             is-prop-pi (λ _ ()) _ _))
        h (Deq eq-data x) = g (Deq eq-data x)
        ε (Deq eq-data x) d = aux (dimx d)
          module ε-Deq-eq-data where
          aux : (a1 : R d dmax ⊎ (x ≐ f e xmax)) →
                f-Deq-eq-data x (g-Deq-eq-data.aux x d a1) ≡ d
          aux (inl _) = refl
          aux (inr _) = εs pr sc d _ _
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl

        dmineq eq-data = aux (dimx dmin)
          module dmineq-eq-data where
          aux : (a1 : R dmin dmax ⊎ (xmin ≐ f e xmax)) →
                g-Deq-eq-data.aux xmin dmin a1 ≡ dmin'
          aux (inl _) = ap inl (pair-eq (refl , is-prop-pi (λ _ ()) _ _))
          aux (inr e) = rec⊥ (e (λ e → st r0 e))

        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl

        d0eq eq-data    = aux (dimx d0)
          module d0eq-eq-data where
          aux : (a1 : R d0 dmax ⊎ (xmin ≐ f e xmax)) →
                g-Deq-eq-data.aux xmin d0 a1 ≡ d0'
          aux (inl _) = ap inl (pair-eq (refl , is-prop-pi (λ _ ()) _ _))
          aux (inr e) = rec⊥ (e (λ e → st r0 e))

        d0eq' eq-data   = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (d0eq eq-data)
        d0eqcoh eq-data = refl

        dmaxeq eq-data = aux (dimx dmax)
          module dmaxeq-eq-data where
          dn-tpt-comm : {x1 x2 : X} → {d1 : D (f e x1)} →
                        {r1 r2 : R dmin d1} → r1 ≡ r2 → (r3 : R dmin d1) →
                        (e1 : x2 ≡ x1) →
                        fst (g cl (tpt (λ x → Σ (D x) (R dmin))
                                       (! (ap (f e) e1))
                                       (d1 , r1))) ≡
                        fst (tpt (λ x → (D x) × (x ≢ f e xmax))
                                 (! e1)
                                 (fst (g cl (d1 , r2)) ,
                                  st (snd (g cl (d1 , r3)))))
          dn-tpt-comm refl _ refl = refl

          aux : (a1 : R dmax dmax ⊎ (f e xmax ≐ f e xmax)) →
                g-Deq-eq-data.aux (f e xmax) dmax a1 ≡ dmax'
          aux (inl r) = rec⊥ (ir r)
          aux (inr e1) =
            ap inr (pair-eq
                    (pair-eq
                     (! (ap (λ e2 →
                       fst (g cl (tpt (λ x → Σ (D x) (R dmin)) (! e2)
                           (dmax , ri (λ k → k refl)
                                      (λ n → e1 (λ x → n (! x)))
                                      r0))))
                            (τ' e xmax)) ●
                      dn-tpt-comm (pr _ r0) r0 (η e xmax) ,
                      is-prop-pi (λ _ ()) _ _) ,
                     is-prop-pi (λ _ ()) _ _))
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl
        
        fst (Req eq-data) {x1} {x2} {d1} {d2} = aux (dimx d1) (dimx d2)
          module fst-Req-eq-data where
          aux : (a1 : R d1 dmax ⊎ (x1 ≐ f e xmax)) →
                (a2 : R d2 dmax ⊎ (x2 ≐ f e xmax)) →
                R' (g-Deq-eq-data.aux x1 d1 a1) (g-Deq-eq-data.aux x2 d2 a2) →
                R d1 d2
          aux (inl _) (inl _) r = r
          aux (inl r) (inr e) _ = ri (λ k → k refl) (nn-map ! e) r
          aux (inr _) _ ()
          
        snd (Req eq-data) {x1} {x2} {d1} {d2} = aux (dimx d1) (dimx d2)
          module snd-Req-eq-data where
          aux : (a1 : R d1 dmax ⊎ (x1 ≐ f e xmax)) →
                (a2 : R d2 dmax ⊎ (x2 ≐ f e xmax)) →
                R d1 d2 →
                R' (g-Deq-eq-data.aux x1 d1 a1) (g-Deq-eq-data.aux x2 d2 a2)
          aux (inl _) (inl _) r = r
          aux (inl _) (inr _) _ = tt
          aux (inr e) (inl r1) r2 = smx {d2 = d2} (ri e (λ k → k refl) r2)
          aux (inr e1) (inr e2) r = ir {d1 = dmax} {d2 = dmax} (ri e1 e2 r)
          
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → pr' {x1} {d1} {x2} {d2}) pr (Req eq-data)
        Reqcoh eq-data = refl

        preq' eq-data = rel-is-prop-eq (Deq eq-data) refl (Req eq-data) refl
        
        cleq eq-data {x2 = x1} d1 r1 r2 = aux2 (dimx d1) r1
          module cleq-eq-data where
          tpt-d1 : {x1 x2 : X} → (e1 : x2 ≡ x1) → {d1 : D x1} →
                   (r3 : R d1 dmax) → D x2 × (x2 ≢ f e xmax)
          tpt-d1 e1 {d1 = d1} r3 = tpt (λ x → D x × (x ≢ f e xmax)) (! e1)
                                       (d1 , strict R ir r3)

          cl-tpt-comm : {x1 x2 : X} → (e1 : x2 ≡ x1) → {d1 : D x1} →
                        (r2 r3 : R d1 dmax) →
                        fst (tpt (λ x → Σ (D x) (R dmin))
                                 (ap (f e) e1)
                                 (f cl (fst (tpt-d1 e1 r3) ,
                                  mx (fst (tpt-d1 e1 r3))
                                     (λ e3 → snd (tpt-d1 e1 r3) e3))))
                        ≡ fst (f cl (d1 , r2))
          cl-tpt-comm refl {d1 = d1} r2 r3 =
            ap (λ r → fst (f cl (d1 , r)))
               (pr (mx d1 (strict R ir r3)) r2)

          aux1 : (r3 : R d1 dmax) → 
                 (a2 : R d1 (fst (g cl (dmax , r0))) ⊎ (x1 ≐ xmax)) →
                 f-Deq-eq-data (f e x1)
                   (fst (f-cl-f-eqv.aux
                          (g-eqv s) (d1 , strict R ir r3) tt a2)) ≡
                 fst (f cl (d1 , r2))
          aux1 r3 (inl r4) = ap (λ r → fst (f cl (d1 , r))) (pr _ _)
          aux1 r3 (inr e1) = 
            ap (λ e2 →
              fst (tpt (λ x → Σ (D x) (R dmin)) e2
                       (f cl (fst (tpt-d1 (η e x1) r3) ,
                        mx (fst (tpt-d1 (η e x1) r3))
                           (snd (tpt-d1 (η e x1) r3))))))
               (! (τ' e x1)) ●
            cl-tpt-comm (η e x1) r2 r3
          
          aux2 : (a1 : R d1 dmax ⊎ (x1 ≐ f e xmax)) →
                 (r1 : R' (g-Deq-eq-data.aux x1 d1 a1) dmax') →
                 f-Deq-eq-data (f e x1)
                   (fst (f cl' (g-Deq-eq-data.aux x1 d1 a1 , r1))) ≡
                 fst (f cl (d1 , r2))
          aux2 (inl r3) tt = aux1 r3 (Seg.dimx (g-eqv s) (d1 , st r3))

    eqv : Seg xmin e i xmin xmax ≃ Seg≠ xmin e i xmin (f e xmax)
    f eqv = f-eqv
    g eqv = g-eqv
    η eqv = η-eqv
    h eqv = g eqv
    ε eqv = ε-eqv


module IncrementMinEqv
       {X : Set} {xmax : X}
       (e : X ≃ X) {i : X → X}
       (i0 : i xmax ≡ xmax)
       (i0-inv : {x : X} → i x ≡ x → x ≡ xmax)
       (anc1 : (x : X) → i (f e x) ≡ g e (i x))
       (anc2 : (x : X) → f e (i x) ≡ i (g e x))
       (e≠i : (x : X) → f e x ≢ i x)
       (xmin : X)
       where

  incr-min-eqv : Seg≠ xmax e i xmin xmax ≃ Seg xmax e i (f e xmin) xmax
  incr-min-eqv = eqv
    module incr-min-eqv where
    D-f-eqv : (X → Set) → X → Set
    D-f-eqv D x = D x × (xmin ≢ x)

    D-g-eqv : (X → Set) → X → Set
    D-g-eqv D x = D x ⊎ D (f e x) × (f e x ≐ f e xmin)

    module _ (s : Seg≠ xmax e i xmin xmax) where
      open Seg≠ s
      f-eqv : Seg xmax e i (f e xmin) xmax
      Seg.D f-eqv = D-f-eqv D
      Seg.d0 f-eqv = d0 , st r0
      Seg.dmin f-eqv = fst (f cl (dmin , r0)) , st (snd (f cl (dmin , r0)))
      Seg.dmax f-eqv = dmax , st r0
      Seg.R f-eqv (d1 , _) (d2 , _) = R d1 d2
      Seg.pr f-eqv = pr
      Seg.ir f-eqv = ir
      Seg.tr f-eqv = tr
      Seg.tc f-eqv (d1 , _) (d2 , _) = tc d1 d2
      Seg.mn f-eqv {x1} (d1 , n1) n2 = aux (tc d1 (fst (f cl (dmin , r0))))
        module mn-f-eqv where
        aux : R d1 (fst (f cl (dmin , r0))) ⊎
              (x1 ≐ f e xmin) ⊎ R (fst (f cl (dmin , r0))) d1 →
              R (fst (f cl (dmin , r0))) d1
        aux (inl r1) = rec⊥ (ds (mn d1 n1) r1)
        aux (inr (inl e2)) = rec⊥ (e2 (λ e2 → n2 (! e2)))
        aux (inr (inr r1)) = r1
      Seg.mx f-eqv (d1 , _) n2 = mx d1 n2

      Seg.ex f-eqv (d1 , _) (d2 , _) = ex d1 d2
      Seg.ds f-eqv = ds

      f (Seg.cl f-eqv {x}) ((d1 , n1) , r1) =
        (fst (f cl (d1 , r1)) , st (snd (f cl (d1 , r1)))) , umon r0 r1 (mn d1 n1)
      g (Seg.cl f-eqv {x}) ((d1 , n1) , r1) =
        (fst (g cl (d1 , mn d1 n1)) ,
         st (dmon (ex dmin (fst (f cl (dmin , r0)))) (mn d1 n1) r1)) ,
        snd (g cl (d1 , mn d1 n1))
      η (Seg.cl f-eqv {x}) ((d1 , n1) , r1) =
        pair-eq (pair-eq
          (ηs pr cl d1 r1 _ ,
           is-prop-pi (λ _ ()) _ _) ,
          pr _ _)
      h (Seg.cl f-eqv) = g (Seg.cl f-eqv)
      ε (Seg.cl f-eqv {x}) ((d1 , n1) , r1) =
        pair-eq (pair-eq
          (εs pr cl d1 _ _ ,
           is-prop-pi (λ _ ()) _ _) ,
          pr _ _)
      Seg.ac f-eqv n (d1 , _) (d2 , _) = ac n d1 d2

    module _ (s : Seg xmax e i (f e xmin) xmax) where
      open Seg s
      g-eqv : Seg≠ xmax e i xmin xmax
      Seg≠.D g-eqv = D-g-eqv D

      Seg≠.d0 g-eqv = inl d0
      Seg≠.dmin g-eqv = inr (dmin , λ k → k refl)
      Seg≠.dmax g-eqv = inl dmax

      Seg≠.R g-eqv (inl d1) (inl d2) = R d1 d2
      Seg≠.R g-eqv (inl _) (inr _) = ⊥
      Seg≠.R g-eqv (inr _) (inl _) = ⊤
      Seg≠.R g-eqv (inr _) (inr _) = ⊥

      Seg≠.pr g-eqv {d1 = inl _} {d2 = inl _} = pr
      Seg≠.pr g-eqv {d1 = inl _} {d2 = inr _} ()
      Seg≠.pr g-eqv {d1 = inr _} {d2 = inl _} = ⊤-is-prop
      Seg≠.pr g-eqv {d1 = inr _} {d2 = inr _} ()

      Seg≠.ir g-eqv {d1 = inl _} {inl _} = ir
      Seg≠.ir g-eqv {x1 = x1} {d1 = inr (d1 , e1)} {inl d2} _ =
        e1 (λ e1 → un1 (tpt D (! (η e x1) ● ap (g e) e1) d2))

      Seg≠.tr g-eqv {d1 = inl _} {d21 = inl _} {d22 = inl _} {d3 = inl _} r1 r2 =
        tr r1 r2
      Seg≠.tr g-eqv {d1 = inl _} {x2} {d21 = inl d21} {d22 = inr (d22 , e22)}
                    {d3 = inl _} _ _ =
        rec⊥ (e22 (λ e22 → un1 (tpt D (! (η e x2) ● ap (g e) e22) d21)))
      Seg≠.tr g-eqv {d1 = inr _} {d21 = inl _} {d22 = inl _} {d3 = inl _} r1 r2 = tt
      Seg≠.tr g-eqv {d1 = inr _} {x2} {d21 = inl d21} {d22 = inr (d22 , e22)}
                    {d3 = inl _} r1 r2 =
        rec⊥ (e22 (λ e22 → un1 (tpt D (! (η e x2) ● ap (g e) e22) d21)))

      Seg≠.tc g-eqv (inl d1) (inl d2) = tc d1 d2
      Seg≠.tc g-eqv (inl _) (inr _) = inr (inr tt)
      Seg≠.tc g-eqv (inr _) (inl _) = inl tt
      Seg≠.tc g-eqv {x1} (inr (d1 , e1)) {x2} (inr (d2 , e2)) =
        inr (inl (λ k → e1 (λ e1 → e2 (λ e2 →
          k (g (embed e) (e1 ● ! e2))))))

      Seg≠.mn g-eqv (inl _) _ = tt
      Seg≠.mn g-eqv (inr (_ , e1)) n1 = e1 (λ e1 → n1 (! (g (embed e) e1)))

      Seg≠.mx g-eqv (inl d1) n = mx d1 n
      Seg≠.mx g-eqv (inr _) _ = tt

      Seg≠.ex g-eqv (inl d1) (inl d2) = ex d1 d2
      Seg≠.ex g-eqv (inr _) (inl _) = tt
      Seg≠.ex g-eqv (inl d1) (inr (d2 , e2)) =
        e2 (λ e2 → under-2 e i0 anc1
                           (eee0 e i0 i0-inv anc1 e≠i)
                           (eeee0 e i0 i0-inv anc1 e≠i)
                           d0 pr ir tr tc mn mx ex cl ac
                           (tpt D (f (adj (e ∘e e)) e2) d1))
      
      Seg≠.ex g-eqv {x1} (inr (d1 , e1)) (inr (d2 , e2)) =
        e2 (λ e2 → un1 (tpt D (! (η e (f e x1)) ● ap (g e) e2) d1))

      Seg≠.ds g-eqv {d1 = inl d1} {d2 = inl d2} {inl d3} r1 r2 = ds r1 r2
      Seg≠.ds g-eqv {x1} {d1 = inr (d1 , e1)} {d2 = inl d2} {inl d3} _ r2 = 
        smn {d2 = d2} (ri (λ k → k refl) e1 r2)

      f (Seg≠.cl g-eqv {x2 = x1}) (inl d1 , r1) = inl (fst (f cl (d1 , r1))) , tt
      f (Seg≠.cl g-eqv {x2 = x1}) (inr (d1 , e1) , _) = inl d1 , tt

      g (Seg≠.cl g-eqv {x2 = x1}) (inl d1 , _) = aux (dimn d1)
        module g-cl-g-eqv where
        aux : R dmin d1 ⊎ (f e xmin ≐ f e x1) →
              Σ (D-g-eqv D x1) (λ d → Seg≠.R g-eqv d (Seg≠.dmax g-eqv))
        aux (inl r1) = inl (fst (g cl (d1 , r1))) , snd (g cl (d1 , r1))
        aux (inr e1) = inr (d1 , (λ k → e1 (λ e1 → k (! e1)))) , tt

      η (Seg≠.cl g-eqv {x2 = x}) (inl d1 , r1) =
        pair-eq (aux (dimn (fst (f cl (d1 , r1)))) , pr _ _)
        module η-cl-g-eqv-l where
        aux : (a : R dmin (fst (f cl (d1 , r1))) ⊎ (f e xmin ≐ f e x)) →
              fst (g-cl-g-eqv.aux (fst (f cl (d1 , r1))) tt a) ≡ inl d1
        aux (inl r2) = ap inl (ηs pr cl d1 r1 r2)
        aux (inr e1) =
          rec⊥ (e1 (λ e1 → un1 (tpt D (! (η e x) ● ! (ap (g e) e1)) d1)))
        
      η (Seg≠.cl g-eqv {x2 = x}) (inr (d1 , e1) , _) =
        pair-eq (aux (dimn d1) , ⊤-is-prop _ _)
        module η-cl-g-eqv-r where
        aux : (a : R dmin d1 ⊎ (f e xmin ≐ f e x)) →
              fst (g-cl-g-eqv.aux d1 tt a) ≡ inr (d1 , e1)
        aux (inl r1) = rec⊥ (e1 (λ e1 → st r1 (! e1)))
        aux (inr e2) = ap inr (pair-eq (refl , is-prop-pi (λ _ ()) _ _))

      h (Seg≠.cl g-eqv) = g (Seg≠.cl g-eqv)

      ε (Seg≠.cl g-eqv {x2 = x}) (inl d1 , _) =
        pair-eq (aux (dimn d1) , ⊤-is-prop _ _)
        module ε-cl-g-eqv where
        aux : (a : R dmin d1 ⊎ (f e xmin ≐ f e x)) →
              fst (f (Seg≠.cl g-eqv) (g-cl-g-eqv.aux d1 _ a)) ≡ inl d1
        aux (inl r1) = ap inl (εs pr cl d1 r1 (snd (g cl (d1 , r1))))
        aux (inr e1) = refl

      Seg≠.ac g-eqv n1 (inl d1) (inl d2) = ac n1 d1 d2
      Seg≠.ac g-eqv {x1} n1 (inl d1) (inr (d2 , e2)) = aux (dimn d1)
        module ac-g-eqv-l-r where
        aux : R dmin d1 ⊎ (f e xmin ≐ x1) → ⊥
        aux (inl r1) =
          ac (λ e3 → e2 (λ e2 →
                smx {d2 = d1}
                    (ri (λ k → k (! e2 ● anc2 x1 ● e3 ● i0-inv e3))
                        (λ k → k refl)
                        r1)))
             (fst (g sc (d1 , r1)))
             (tpt D (anc2 x1) d2)
        aux (inr e3) = 
          e2 (λ e2 → e3 (λ e3 →
            e≠i (g e x1) (ε' e x1 ● ! e3 ● ! e2 ● anc2 x1)))
      
      Seg≠.ac g-eqv {x1} n1 (inr (d1 , e1)) (inl d2) = aux (dimn d2)
        module ac-g-eqv-r-l where
        aux : R dmin d2 ⊎ (f e xmin ≐ i x1) → ⊥
        aux (inl r1) =
          ac (λ e3 → e1 (λ e1 →
                smx {d2 = d2} (ri (λ k → k (! e1 ● i0-inv e3)) (λ k → k refl) r1)))
             d1
             (tpt D (! (anc1 x1)) (fst (g sc (d2 , r1))))
        aux (inr e3) = 
          e1 (λ e1 → e3 (λ e3 → e≠i x1 (e1 ● e3)))
      
      Seg≠.ac g-eqv n1 (inr (d1 , e1)) (inr (d2 , e2)) =
        e1 (λ e1 → e2 (λ e2 → n1 (g (embed e) (e2 ● ! e1))))

      Seg≠.r0 g-eqv = tt

    module _ (s : Seg≠ xmax e i xmin xmax) where
      open Seg≠ s
      open Seg≠ (g-eqv (f-eqv s))
        renaming (D to D' ; d0 to d0' ; dmin to dmin' ; dmax to dmax' ;
                  R to R' ; pr to pr' ; tc to tc' ; cl to cl' ; ri to ri')
        using    ()

      open PresegEqData
      
      η-eqv : g-eqv (f-eqv s) ≡ s
      η-eqv = seg≠-eq eq-data
        module η-eqv where
        Deq-eq-data : (x1 : X) → D' x1 ≃ D x1
        f (Deq-eq-data x1) (inl (d1 , n1)) = d1
        f (Deq-eq-data x1) (inr ((d1 , n1) , e1)) = fst (g cl (d1 , mn d1 n1))
        g (Deq-eq-data x1) d1 = aux (dimn d1)
          module g-Deq-eq-data where
          aux : R dmin d1 ⊎ (xmin ≐ x1) → D' x1
          aux (inl r1) = inl (d1 , st r1)
          aux (inr e1) =
            inr ((fst (f cl (d1 , ri e1 (λ k → k refl) r0)) ,
                  st (snd (f cl (d1 , ri e1 (λ k → k refl) r0)))) ,
                 (λ k → e1 (λ e1 → k (! (ap (f e) e1)))))
          
        η (Deq-eq-data x1) (inl (d1 , n1)) = aux (dimn d1)
          module η-Deq-eq-data-l where
          aux : (a : R dmin d1 ⊎ (xmin ≐ x1)) →
                g-Deq-eq-data.aux x1 d1 a ≡ inl (d1 , n1)
          aux (inl r1) =
            ap inl (pair-eq (refl , is-prop-pi (λ _ ()) _ _))
          aux (inr e1) = rec⊥ (e1 n1)
          
        η (Deq-eq-data x1) (inr ((d1 , n1) , e1)) =
          aux (dimn (fst (g cl (d1 , mn d1 n1))))
          module η-Deq-eq-data-r where
          aux : (a : R dmin (fst (g cl (d1 , mn d1 n1))) ⊎ (xmin ≐ x1)) →
                g-Deq-eq-data.aux x1 (fst (g cl (d1 , mn d1 n1))) a ≡
                inr ((d1 , n1) , e1)
          aux (inl r1) = rec⊥ (e1 (λ e1 → st r1 (! (g (embed e) e1))))
          aux (inr e2) =
            ap inr
              (pair-eq
                (pair-eq
                  (εs pr cl d1 (mn d1 n1) (ri e2 (λ k → k refl) r0) ,
                   is-prop-pi (λ _ ()) _ _) ,
                 is-prop-pi (λ _ ()) _ _))
        
        h (Deq-eq-data x1) = g (Deq-eq-data x1)
        ε (Deq-eq-data x1) d1 = aux (dimn d1)
          module ε-Deq-eq-data where
          aux : (a : R dmin d1 ⊎ (xmin ≐ x1)) →
                f (Deq-eq-data x1) (g-Deq-eq-data.aux x1 d1 a) ≡ d1
          aux (inl r1) = refl
          aux (inr e1) =
            ηs pr cl d1 (ri e1 (λ k → k refl) r0)
               (mn (fst (f cl (d1 , ri e1 (λ k → k refl) r0)))
                   (st (snd (f cl (d1 , ri e1 (λ k → k refl) r0))))) 
        eq-data : PresegEqData (preseg D' d0' dmin' dmax' R'
                                       (λ {x1} {d1} {x2} {d2} →
                                          pr' {x1} {d1} {x2} {d2}) cl')
                               record { Seg≠ s }
        Deq eq-data = Deq-eq-data
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl

        d0eq eq-data = aux (dimn d0)
          module d0eq-eq-data where
          aux : (a : R dmin d0 ⊎ (xmin ≐ xmax)) →
                g-Deq-eq-data.aux xmax d0 a ≡ d0'
          aux (inl r) =
            ap (λ n → inl (d0 , n)) (is-prop-pi (λ _ ()) (st r) (st r0))
          aux (inr e1) = rec⊥ (e1 (λ e1 → st r0 e1))
        d0eq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (d0eq eq-data)
        d0eqcoh eq-data = refl
        
        dmineq eq-data = aux (dimn dmin)
          module dmineq-eq-data where
          aux : (a : R dmin dmin ⊎ (xmin ≐ xmin)) →
                g-Deq-eq-data.aux xmin dmin a ≡ dmin'
          aux (inl r) = rec⊥ (ir r)
          aux (inr e) =
            ap inr (pair-eq
                     (pair-eq
                       (ap (λ r → fst (f cl (dmin , r)))
                           (pr (ri e (λ k → k refl) r0) r0) ,
                        is-prop-pi (λ _ ()) _ _) ,
                      is-prop-pi (λ _ ()) _ _))
        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl
        
        dmaxeq eq-data = aux (dimn dmax)
          module dmaxeq-eq-data where
          aux : (a : R dmin dmax ⊎ (xmin ≐ xmax)) →
                g-Deq-eq-data.aux xmax dmax a ≡ dmax'
          aux (inl r) =
            ap (λ n → inl (dmax , n)) (is-prop-pi (λ _ ()) (st r) (st r0))
          aux (inr e1) = rec⊥ (e1 (λ e1 → st r0 e1))
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl

        fst (Req eq-data) {x1} {x2} {d1} {d2} = aux (dimn d1) (dimn d2)
          module fst-Req-eq-data where
          aux : (a1 : R dmin d1 ⊎ (xmin ≐ x1)) → (a2 : R dmin d2 ⊎ (xmin ≐ x2)) →
                R' (g-Deq-eq-data.aux x1 d1 a1)
                   (g-Deq-eq-data.aux x2 d2 a2) →
                R d1 d2
          aux (inl _) (inl _) r = r
          aux (inr e) (inl r) _ = ri e (λ k → k refl) r
        
        snd (Req eq-data) {x1} {x2} {d1} {d2} r1 = aux (dimn d1) (dimn d2)
          module snd-Req-eq-data where
          aux : (a1 : R dmin d1 ⊎ (xmin ≐ x1)) → (a2 : R dmin d2 ⊎ (xmin ≐ x2)) →
                R' (g-Deq-eq-data.aux x1 d1 a1)
                   (g-Deq-eq-data.aux x2 d2 a2)
          aux (inl _) (inl _) = r1
          aux (inl r2) (inr e1) = rec⊥ (e1 (λ e1 → st (tr r2 r1) e1))
          aux (inr _) (inl _) = tt
          aux (inr e1) (inr e2) =
            rec⊥ (e1 (λ e1 → e2 (λ e2 → st r1 (! e1 ● e2))))
            
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → pr' {x1} {d1} {x2} {d2}) pr (Req eq-data)
        Reqcoh eq-data = refl
        
        preq' eq-data = rel-is-prop-eq (Deq eq-data) refl (Req eq-data) refl

        cleq eq-data {x2} d2 r2 r3 = aux2 _ refl
          module cleq-eq-data where
          aux1-l : (d3 : D x2) → (n3 : xmin ≢ x2) → (r4 : R d3 dmax) →
                   (a2 : R dmin d2 ⊎ (xmin ≐ x2)) →
                   g-Deq-eq-data.aux x2 d2 a2 ≡ inl (d3 , n3) → 
                   fst (f cl (d3 , r4)) ≡ fst (f cl (d2 , r3))
          aux1-l d3 n3 r4 (inl _) e3 =
            ap (λ d → fst (f cl d))
               (pair-eq  (! (ap fst (inl-eq e3)) , pr _ _))
          aux1-l d3 n3 r4 (inr _) e3 = rec⊥ (inl-neq-inr (! e3))

          aux1-r : (d3 : D (f e x2)) → (n3 : xmin ≢ f e x2) →
                   (e3 : f e x2 ≐ f e xmin) →
                   (a2 : R dmin d2 ⊎ (xmin ≐ x2)) →
                   g-Deq-eq-data.aux x2 d2 a2 ≡ inr ((d3 , n3) , e3) →
                   d3 ≡ fst (f cl (d2 , r3))
          aux1-r d3 n3 e3 (inl _) β2 = rec⊥ (inl-neq-inr β2)
          aux1-r d3 n3 e3 (inr _) β2 =
            ! (ap fst (ap fst (inr-eq β2))) ●
            ap (λ r → fst (f cl (d2 , r))) (pr _ _)

          aux2 : (a : Σ (D-f-eqv D x2 ⊎ D-f-eqv D (f e x2) × (f e x2 ≐ f e xmin))
                        (λ d → R' d dmax')) →
                 (g-Deq-eq-data.aux x2 d2 (dimn d2) , r2) ≡ a →
                 f (Deq-eq-data (f e x2)) (fst (f cl' a)) ≡ fst (f cl (d2 , r3))
          aux2 (inl (d3 , n3) , r4) e2 = aux1-l d3 n3 r4 (dimn d2) (ap fst e2)
          aux2 (inr ((d3 , n3) , e3) , r4) e2 =
            aux1-r d3 n3 e3 (dimn d2) (ap fst e2)

    module _ (s : Seg xmax e i (f e xmin) xmax) where
      open Seg s
      open Seg (f-eqv (g-eqv s))
        renaming (D to D' ; d0 to d0' ; dmin to dmin' ; dmax to dmax' ;
                  R to R' ; pr to pr' ; tc to tc' ; cl to cl' ; ri to ri')
        using    ()

      open PresegEqData

      ε-eqv : f-eqv (g-eqv s) ≡ s
      ε-eqv = seg-eq eq-data
        module ε-eqv where
        Deq-eq-data : (x1 : X) → D' x1 ≃ D x1
        f (Deq-eq-data x1) (inl d1 , n1) = d1
        f (Deq-eq-data x1) (inr (d1 , e1) , n1) =
          rec⊥ (e1 (λ e1 → n1 (! (g (embed e) e1))))
        g (Deq-eq-data x1) d1 =
          inl d1 , (λ e1 → un1 (tpt D (! e1 ● ! (η e xmin)) d1))
        η (Deq-eq-data x1) (inl d1 , n1) =
          pair-eq (refl , is-prop-pi (λ _ ()) _ _)
        η (Deq-eq-data x1) (inr (d1 , e1) , n1) =
          rec⊥ (e1 (λ e1 → n1 (! (g (embed e) e1))))
        h (Deq-eq-data x1) = g (Deq-eq-data x1)
        ε (Deq-eq-data x1) d1 = refl

        eq-data : PresegEqData (preseg D' d0' dmin' dmax' R'
                                       (λ {x1} {d1} {x2} {d2} →
                                          pr' {x1} {d1} {x2} {d2}) cl')
                               record { Seg s }
        Deq eq-data = Deq-eq-data
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl

        d0eq eq-data = ap (λ n → (inl d0 , n)) (is-prop-pi (λ _ ()) _ _)
        d0eq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (d0eq eq-data)
        d0eqcoh eq-data = refl

        dmineq eq-data = ap (λ n → (inl dmin , n)) (is-prop-pi (λ _ ()) _ _)
        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl

        dmaxeq eq-data = ap (λ n → (inl dmax , n)) (is-prop-pi (λ _ ()) _ _)
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl

        Req eq-data = id , id
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → pr' {x1} {d1} {x2} {d2})
                 pr (id , id)
        Reqcoh eq-data = refl

        preq' eq-data = rel-is-prop-eq (Deq eq-data) refl (id , id) refl

        cleq eq-data {x2 = x2} d2 r2 r3 =
          ap (λ r → fst (f cl (d2 , r)))
             (pr r2 r3)
          
    eqv : Seg≠ xmax e i xmin xmax ≃ Seg xmax e i (f e xmin) xmax
    f eqv = f-eqv
    g eqv = g-eqv
    η eqv = η-eqv
    h eqv = g eqv
    ε eqv = ε-eqv
