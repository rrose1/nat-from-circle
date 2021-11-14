{-# OPTIONS --without-K --rewriting #-}
module LessThan where

open import UTT
open import ZModel
open import ZModelsHaveDecEq


infix 4 _<_
_<_ : (x1 x2 : Z) -> Type
x1 < x2 = aux (seg x1) (seg x2)
  module _<_ where
  aux : Seg<0 x1 ⊎ Seg≥0 x1 -> Seg<0 x2 ⊎ Seg≥0 x2 -> Type
  aux (inl s1) (inl _) = Σ (D x2) (R dmin) where open Seg≠ s1
  aux (inl _) (inr _) = ⊤
  aux (inr _) (inl _) = ⊥
  aux (inr _) (inr s2) = Σ (D x1) (λ d2 -> R d2 dmax) where open Seg s2

<-irrefl : (x1 : Z) -> ¬ (x1 < x1)
<-irrefl x1 = aux (seg x1)
  module <-irrefl where
  aux : (a1 : Seg0 x1) -> _<_.aux _ _ a1 a1 -> ⊥
  aux (inl s1) (d1 , r1) = Seg≠.ir s1 r1
  aux (inr s1) (d1 , r1) = Seg.ir s1 r1

<-ext : (x1 : Z) -> x1 < f e x1
<-ext x1 = tpt (_<_.aux _ _ (seg x1)) (! (seg-cmpt x1)) (aux (seg x1))
  module <-ext where
  aux1 : (s1 : Seg<0 x1) ->
         (a1 : Seg.R (incr-min s1) (Seg.dmin (incr-min s1))
                     (Seg.dmax (incr-min s1)) ⊎ (f e x1 ≐ zero)) ->
         _<_.aux _ _ (inl s1)
           (f (ide _ ⊎e nneg-part-eqv.eqv _)
              (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                 (f ⊎-assoc (inl (npos-part-eqv.g-eqv _ (incr-min s1) a1)))))
  aux1 s1 (inl _) = f cl (dmin , r0) where open Seg≠ s1
  aux1 s1 (inr _) = tt

  aux : (a1 : Seg<0 x1 ⊎ Seg≥0 x1) -> _<_.aux _ _ a1 (f (seg0-eqv _) a1)
  aux (inl s1) = aux1 s1 (Seg.dimx (incr-min s1) (Seg.dmin (incr-min s1)))
  aux (inr s1) = inl dmax , tt where open Seg s1
  

arith-1 : {x1 : Z} -> (zero < x1) -> f e x1 ≢ zero
arith-1 {x1} = aux (seg zero) (seg x1)
  module arith-1 where
  aux : (a0 : Seg0 zero) -> (a1 : Seg0 x1) -> _<_.aux _ _ a0 a1 -> f e x1 ≢ zero
  aux (inl s1) (inl s2) _ _ = ir r0 where open Seg≠ s1
  aux (inl s1) (inr s2) _ _ = ir r0 where open Seg≠ s1
  aux (inr s1) (inl s2) ()
  aux (inr s1) (inr s2) (d1 , r1) e1 = ov1 (tpt D (! e1) dmin) where open Seg s2

<-disc : {x1 x2 : Z} -> (x1 < f e x2) -> (x1 ≡ x2) ⊎ (x1 < x2)
<-disc {x1} {x2} =
  tpt (λ s -> _<_.aux _ _ (seg x1) s -> (x1 ≡ x2) ⊎ (x1 < x2))
      (! (seg-cmpt x2))
      (aux1 (seg x1) (seg x2))
  module <-disc where
  aux1 : (a1 : Seg0 x1) -> (a2 : Seg0 x2) -> _<_.aux _ _ a1 (f (seg0-eqv _) a2) ->
         (x1 ≡ x2) ⊎ (_<_.aux _ _ a1 a2)
  aux1 (inl s1) (inl s2) = aux2 (Seg.dimx (incr-min s2) (Seg.dmin (incr-min s2)))
    module <-disc-aux1-l-l where
    open Seg≠ s1
    aux3 : (d1 : D x2) ->  R dmin d1 ⊎ (x1 ≐ x2) ->
           (x1 ≡ x2) ⊎ Σ (D x2) (R dmin)
    aux3 d1 (inl r1) = inr (d1 , r1)
    aux3 d1 (inr e1) = inl (stab e1)

    aux2 : (a1 : Seg.R (incr-min s2) (Seg.dmin (incr-min s2))
                                     (Seg.dmax (incr-min s2))
                 ⊎ (f e x2 ≐ zero)) ->
           _<_.aux _ _ (inl s1)
             (f (ide _ ⊎e nneg-part-eqv.eqv _)
                (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                   (f ⊎-assoc (inl (npos-part-eqv.g-eqv _ (incr-min s2) a1))))) ->
           (x1 ≡ x2) ⊎ Σ (D x2) (R dmin)
    aux2 (inl r1) (d1 , r2) =
      aux3 (fst (g cl (d1 , r2)))
           (dimn _)
    aux2 (inr e1) _ =
      aux3 (fst (g cl (tpt D (! (stab e1)) dmax ,
                              ri (λ k -> k refl)
                                 (λ k -> e1 (λ e1 -> k (! e1))) r0)))
           (dimn _)

  aux1 (inl s1) (inr s2) _ = inr tt
  aux1 (inr s1) (inl s2) = aux2 (Seg.dimx (incr-min s2) (Seg.dmin (incr-min s2)))
    module <-disc-aux1-r-l where
    open Seg≠ s2
    aux2 : (a1 : Seg.R (incr-min s2) (Seg.dmin (incr-min s2))
                                     (Seg.dmax (incr-min s2))
                 ⊎ (f e x2 ≐ zero)) ->
           _<_.aux _ _ (inr s1)
             (f (ide _ ⊎e nneg-part-eqv.eqv _)
                (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                   (f ⊎-assoc (inl (npos-part-eqv.g-eqv _ (incr-min s2) a1))))) ->
           (x1 ≡ x2) ⊎ ⊥
    aux2 (inl r1) ()
    aux2 (inr e1) ((d1 , n1) , r1) = inr (e1 (λ e1 -> ds (mn d1 n1) r1))

  aux1 (inr s1) (inr s2) (inl d1 , tt) = aux2 (dimx d1)
    module <-disc-aux1-r-r where
    open Seg s2
    aux2 : R d1 dmax ⊎ (x1 ≐ x2) ->
           (x1 ≡ x2) ⊎ _<_.aux _ _ (inr s1) (inr s2)
    aux2 (inl r1) = inr (d1 , r1)
    aux2 (inr e1) = inl (stab e1)

<-is-prop : {x1 x2 : Z} -> is-prop (x1 < x2)
<-is-prop {x1} {x2} = aux _ refl _ refl
  module <-is-prop where
  aux : (a1 : Seg<0 x1 ⊎ Seg≥0 x1) -> seg x1 ≡ a1 ->
        (a2 : Seg<0 x2 ⊎ Seg≥0 x2) -> seg x2 ≡ a2 ->
        is-prop (_<_.aux _ _ a1 a2)
  aux (inl s1) b1 (inl s2) b2 _ _ =
    pair-eq (tpt (λ s -> is-prop (D0 s x2)) b1 (dom-seg-is-prop x1 x2) _ _ ,
             pr _ _)
    where open Seg≠ s1
  aux (inl s1) b1 (inr s2) b2 = ⊤-is-prop
  aux (inr s1) b1 (inl s2) b2 ()
  aux (inr s1) b1 (inr s2) b2 _ _ =
    pair-eq (tpt (λ s -> is-prop (D0 s x1)) b2 (dom-seg-is-prop x2 x1) _ _ , pr _ _)
    where open Seg s2

<-mono : {x1 x2 : Z} -> (x1 < x2) ≃ (f e x1 < f e x2)
<-mono {x1} {x2} =
  tpt2-cart-eqv (λ s1 s2 -> _<_.aux (f e x1) (f e x2) s1 s2)
                (! (seg-cmpt x1)) (! (seg-cmpt x2)) ∘e
  aux1 _ refl _ refl
  module mono1 where
  aux1 : (a1 : Seg<0 x1 ⊎ Seg≥0 x1) -> seg x1 ≡ a1 ->
         (a2 : Seg<0 x2 ⊎ Seg≥0 x2) -> seg x2 ≡ a2 ->
         _<_.aux x1 x2 a1 a2 ≃
         _<_.aux _ _ (f (seg0-eqv x1) a1) (f (seg0-eqv x2) a2)
  aux1 (inl s1) b1 (inl s2) _ =
    aux2 (Seg.dimx (incr-min s1) (Seg.dmin (incr-min s1)))
         (Seg.dimx (incr-min s2) (Seg.dmin (incr-min s2))) 
    module <-mono-l-l where
    open Seg≠ s1
    aux2 : (a1 : Seg.R (incr-min s1) (Seg.dmin (incr-min s1))
                   (Seg.dmax (incr-min s1))
                   ⊎ (f e x1 ≐ zero)) ->
           (a2 : Seg.R (incr-min s2) (Seg.dmin (incr-min s2))
                   (Seg.dmax (incr-min s2))
                   ⊎ (f e x2 ≐ zero)) ->
           Σ (D x2) (R dmin) ≃
           _<_.aux _ _ (f (ide _ ⊎e nneg-part-eqv.eqv _)
                          (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                             (f ⊎-assoc
                                (inl (npos-part-eqv.g-eqv _
                                       (incr-min s1) a1)))))
                       (f (ide _ ⊎e nneg-part-eqv.eqv _)
                          (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                             (f ⊎-assoc (inl (npos-part-eqv.g-eqv _
                                               (incr-min s2) a2)))))
    aux2 (inl _) (inl _) = eqv
      module <-mono-l-l-aux2-l-l where
      eqv : Σ (D x2) (R dmin) ≃
            Σ (D (f e x2) × (x1 ≢ f e x2))
              (λ d -> R (fst (f cl (dmin , r0))) (fst d))
      f eqv (d2 , r3) =
        (fst (f cl (d2 , mx d2 (Seg≠.st s2 (Seg≠.r0 s2)))) ,
         (λ e1 -> un1 (tpt D (f (adj e) (! e1)) d2))) ,
        Seg.mn (incr-min s1)
               (_ , (λ e1 -> un1 (tpt D (f (adj e) (! e1)) d2)))
               (λ e1 -> st r3 (g (embed e) e1))

      g eqv ((d2 , n1) , r3) =
        fst (g cl (d2 , mn d2 n1)) ,
        mn (fst (g cl (d2 , mn d2 n1))) (λ e1 -> st r3 (ap (f e) e1))

      η eqv (d2 , r3) = pair-eq (ηs pr cl d2 _ _ , pr _ _)

      h eqv = g eqv
      ε eqv ((d2 , n1) , r3) =
        pair-eq (pair-eq
          (εs pr cl d2 _ _ , is-prop-pi (λ _ ()) _ _) ,
           Seg.pr (incr-min s1) {d1 = Seg.dmin (incr-min s1)}
                  {d2 = d2 , n1} _ _)

    f (aux2 (inl r1) (inr e2)) _ = tt
    g (aux2 (inl r1) (inr e2)) _ =
      fst (g cl (tpt D (! (stab e2)) dmax ,
                 ri (λ k -> k refl) (λ k -> e2 (λ e2 -> k (! e2))) r0)) ,
      mn _ (λ e3 -> e2 (λ e2 -> st r1 (ap (f e) e3 • e2)))
    η (aux2 (inl r1) (inr e2)) _ =
      pair-eq (tpt (λ s -> is-prop (D0 s x2)) b1 (dom-seg-is-prop x1 x2) _ _ ,
               pr _ _)
    h (aux2 (inl r1) (inr e2)) = g (aux2 (inl r1) (inr e2))
    ε (aux2 (inl r1) (inr e2)) = ⊤-is-prop tt

    f (aux2 (inr e1) (inl r2)) (d2 , r3) =
      e1 (λ e1 -> ds {d3 = tpt D (! e1) dmax} r3 (ri (λ k -> k refl)
                    (λ k -> k (! e1))
                    (mx d2 (Seg≠.st s2 (Seg≠.r0 s2)))))
    g (aux2 (inr e1) (inl r2)) ()
    η (aux2 (inr e1) (inl r2)) (d2 , r3) =
      rec⊥ (e1 (λ e1 -> ds {d3 = tpt D (! e1) dmax} r3 (ri (λ k -> k refl)
                          (λ k -> k (! e1))
                          (mx d2 (Seg≠.st s2 (Seg≠.r0 s2))))))
    h (aux2 (inr e1) (inl r2)) = g (aux2 (inr e1) (inl r2))
    ε (aux2 (inr e1) (inl r2)) ()


    f (aux2 (inr e1) (inr e2)) (d2 , r2) =
      rec⊥ (e1 (λ e1 -> e2 (λ e2 -> st r2 (g (embed e) (e1 • ! e2)))))
    g (aux2 (inr e1) (inr e2)) (d2 , r2) =
      rec⊥ (e1 (λ e1 -> e2 (λ e2 -> Seg≠.st s2 r2 (e1 • ! e2))))
    η (aux2 (inr e1) (inr e2)) (d2 , r2) =
      rec⊥ (e1 (λ e1 -> e2 (λ e2 -> st r2 (g (embed e) (e1 • ! e2)))))
    h (aux2 (inr e1) (inr e2)) = g (aux2 (inr e1) (inr e2))
    ε (aux2 (inr e1) (inr e2)) (d2 , r2) =
      rec⊥ (e1 (λ e1 -> e2 (λ e2 -> Seg≠.st s2 r2 (e1 • ! e2))))

  ----
  aux1 (inl s1) _ (inr s2) b2 =
    aux2 (Seg.dimx (incr-min s1) (Seg.dmin (incr-min s1)))
    module <-mono-l-r where
    open Seg s2
    aux2 : (a1 : Seg.R (incr-min s1) (Seg.dmin (incr-min s1))
                                     (Seg.dmax (incr-min s1))
                 ⊎ (f e x1 ≐ zero)) ->
           ⊤ ≃
           _<_.aux _ _ (f (ide _ ⊎e nneg-part-eqv.eqv _)
                          (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                             (f ⊎-assoc
                                (inl (npos-part-eqv.g-eqv _
                                       (incr-min s1) a1)))))
                       (f (seg0-eqv x2) (inr s2))
    aux2 (inl r1) = ide _
    f (aux2 (inr e1)) _ = inl (tpt D (! (stab e1)) d0) , tt
    g (aux2 (inr e1)) _ = tt
    η (aux2 (inr e1)) = ⊤-is-prop tt
    h (aux2 (inr e1)) = g (aux2 (inr e1))
    ε (aux2 (inr e1)) (inl d1 , tt) =
      ap (λ d -> inl d , tt)
         (tpt (λ s -> is-prop (D0 s (f e x1))) b2 (dom-seg-is-prop x2 (f e x1)) _ _)

  ----
  aux1 (inr s1) _ (inl s2) _ = 
    aux2 (Seg.dimx (incr-min s2) (Seg.dmin (incr-min s2)))
    module <-mono-r-l where
    open Seg≠ s2
    aux2 : (a2 : Seg.R (incr-min s2) (Seg.dmin (incr-min s2))
                                     (Seg.dmax (incr-min s2))
                 ⊎ (f e x2 ≐ zero)) ->
           ⊥ ≃
           _<_.aux _ _ (f (seg0-eqv x1) (inr s1))
                       (f (ide _ ⊎e nneg-part-eqv.eqv _)
                          (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                             (f ⊎-assoc
                                (inl (npos-part-eqv.g-eqv _
                                       (incr-min s2) a2)))))
    aux2 (inl r1) = ide _
    f (aux2 (inr e1)) ()
    g (aux2 (inr e1)) ((d1 , n1) , r2) = ds (mn d1 n1) r2
    η (aux2 (inr e1)) ()
    h (aux2 (inr e1)) = g (aux2 (inr e1))
    ε (aux2 (inr e1)) ((d1 , n1) , r2) = rec⊥ (ds (mn d1 n1) r2)


  ----
  aux1 (inr s1) _ (inr s2) b2 = eqv
    module <-mono-aux1-r-r where
    open Seg s2
    eqv : Σ (D x1) (λ d1 -> R d1 dmax) ≃
          Σ (D (f e x1) ⊎ D (g e (f e x1)) × (g e (f e x1) ≐ x2))
            (λ d2 -> Seg≠.R (incr-max s2) d2 (Seg≠.dmax (incr-max s2)))
    f eqv (d1 , r1) = inl (fst (f cl (d1 , r1))) , tt

    g eqv (inl d1 , tt) = aux2 (dimn d1)
      module g-mono-aux1-r-r-eqv where
      aux2 : R dmin d1 ⊎ (zero ≐ f e x1) -> Σ (D x1) (λ d2 -> R d2 dmax)
      aux2 (inl r1) = g cl (d1 , r1)
      aux2 (inr e1) =
        rec⊥ (e1 (λ e1 -> Seg.ov1 s1 (tpt (Seg.D s1) e1 (Seg.dmin s1))))

    η eqv (d1 , r1) =
      pair-eq (tpt (λ s -> is-prop (D0 s x1)) b2 (dom-seg-is-prop x2 x1) _ _ ,
               pr _ _)

    h eqv = g eqv

    ε eqv (inl d1 , r1) =
      pair-eq (ap inl (tpt (λ s -> is-prop (D0 s (f e x1)))
                           b2 (dom-seg-is-prop x2 (f e x1)) _ _) ,
                           Seg≠.pr (incr-max s2)
                                   {d1 = inl d1}
                                   {d2 = Seg≠.dmax (incr-max s2)}
                                   _ _)

<-mono' : {x1 x2 : Z} -> (g e x1 < g e x2) ≃ (x1 < x2)
<-mono' {x1} {x2} =
  tpt2-cart-eqv _<_ (ε' e x1) (ε' e x2) ∘e <-mono

<-adj : {x1 x2 : Z} -> (f e x1 < x2) ≃ (x1 < g e x2)
<-adj {x1} {x2} = !e <-mono ∘e !e (tpt2-cart-eqv _<_ refl (ε' e x2))

<-adj' : {x1 x2 : Z} -> (x1 < f e x2) ≃ (g e x1 < x2)
<-adj' {x1} {x2} = !e <-mono ∘e !e (tpt2-cart-eqv _<_ (ε' e x1) refl)

<-disc' : {x1 x2 : Z} -> (x1 < x2) -> (x1 ≡ g e x2) ⊎ (x1 < g e x2)
<-disc' r = f (adj e ⊎e <-adj) (<-disc (f <-mono r))


<-trans-eqv : (x1 : Z) ->
              ((x2 x3 : Z) -> x1 < x2 -> x2 < x3 -> x1 < x3) ≃
              ((x2 x3 : Z) -> (f e x1) < x2 -> x2 < x3 -> (f e x1) < x3)
<-trans-eqv x1 =
  pi-eqv-2 (λ x2 ->
    pi-eqv-2 (λ x3 ->
      pi-eqv-2 (λ w1 ->
        pi-eqv-2 (λ w2 -> !e <-adj)
        ∘e !e (pi-eqv-1 <-mono'))
      ∘e pi-eqv-1 <-adj)
    ∘e !e (pi-eqv-1' (!e e) {P = λ x3 -> x1 < g e x2 -> g e x2 < x3 -> x1 < x3}))
  ∘e !e (pi-eqv-1' (!e e) {P = λ x2 -> (x3 : Z) -> x1 < x2 -> x2 < x3 -> x1 < x3})

<-trans-0 : (x2 x3 : Z) -> zero < x2 -> x2 < x3 -> zero < x3
<-trans-0 x2 x3 = aux1 (seg zero) (seg x2) (seg x3)
  module <-trans-0 where
  aux1 : (a1 : Seg0 zero) -> (a2 : Seg0 x2) -> (a3 : Seg0 x3) ->
        _<_.aux _ _ a1 a2 -> _<_.aux _ _ a2 a3 -> _<_.aux _ _ a1 a3
  aux1 (inl s1) _ _ = rec⊥ (ir r0) where open Seg≠ s1
  aux1 (inr s1) (inl s2) _ ()
  aux1 (inr s1) (inr s2) (inl s3) _ ()
  aux1 (inr s1) (inr s2) (inr s3) _ (d2 , r2) = dmin , aux2 (dimn d2)
    module <-trans-0-aux-r-r-r where
    open Seg s3
    aux2 : R dmin d2 ⊎ (zero ≐ x2) -> R dmin dmax
    aux2 (inl r3) = tr r3 r2
    aux2 (inr e2) = ri (λ k -> e2 (λ e2 -> k (! e2))) (λ k -> k refl) r2

<-trich-eqv : (x1 : Z) ->
              ((x2 : Z) -> (x1 < x2) ⊎ (x2 ≡ x1) ⊎ (x2 < x1)) ≃
              ((x2 : Z) -> (f e x1 < x2) ⊎ (x2 ≡ f e x1) ⊎ (x2 < f e x1))
<-trich-eqv x1 =
  pi-eqv-2 (λ x2 -> !e <-adj ⊎e
                   (!-eqv ∘e !e (adj e {x1} {x2}) ∘e !-eqv) ⊎e
                   !e <-adj')
  ∘e !e (pi-eqv-1' (!e e) {P = λ x2 -> (x1 < x2) ⊎ (x2 ≡ x1) ⊎ (x2 < x1)})

<-trich-0 : (x2 : Z) -> (zero < x2) ⊎ (x2 ≡ zero) ⊎ (x2 < zero)
<-trich-0 x2 = aux (seg zero) (seg x2)
  module <-trich-0 where
  aux : (a1 : Seg0 zero) -> (a2 : Seg0 x2) ->
        (_<_.aux _ _ a1 a2) ⊎ (x2 ≡ zero) ⊎ (_<_.aux _ _ a2 a1)
  aux (inl s1) _ = rec⊥ (ir r0) where open Seg≠ s1
  aux (inr s1) (inl s2) = inr (inr tt)
  aux (inr s1) (inr s2) = aux2 (dimn dmax)
    module <-trich-0-aux-r-r where
    open Seg s2
    aux2 : R dmin dmax ⊎ (zero ≐ x2) ->
           (_<_.aux _ _ (inr s1) (inr s2)) ⊎ (x2 ≡ zero) ⊎
           (_<_.aux x2 zero (inr s2) (inr s1))
    aux2 (inl r1) = inl (dmin , r1)
    aux2 (inr e1) = inr (inl (stab (λ k -> e1 (λ e1 -> k (! e1)))))


<-trans : {x1 x2 x3 : Z} -> x1 < x2 -> x2 < x3 -> x1 < x3
<-trans {x1} {x2} {x3} = indZ <-trans-0 <-trans-eqv x1 x2 x3

<-trich : (x1 x2 : Z) -> (x1 < x2) ⊎ (x2 ≡ x1) ⊎ (x2 < x1)
<-trich = indZ <-trich-0 <-trich-eqv

