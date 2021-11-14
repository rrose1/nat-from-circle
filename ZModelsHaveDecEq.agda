{-# OPTIONS --without-K --rewriting #-}
module ZModelsHaveDecEq where

open import UTT
open import SegmentProperties
open import Segment using (module SegmentDefinitions ; seg-x0)
open import SegmentExtension
open import SegmentEquivalences
  using ( module Seg0Eqv ; module MinSegEqv
        ; module NonnegativePartEqv ; module NonpositivePartEqv)
open import ZModel

open SegmentDefinitions zero e -_ public
open MinSegEqv zero e -_ public
open NonpositivePartEqv zero e -_ public
open NonnegativePartEqv zero e -_ public
open Seg0Eqv zero e -_ i0 i0-inv anc1 anc2 e≠i public


module SectionOfSeg0 where
  seg : (x : Z) -> Seg0 x
  seg = indZ (inr (seg-x0 e -_ (λ k -> k i0) (λ p -> e≠i zero (p • i0)))) seg0-eqv

  seg-cmpt : (x : Z) -> seg (f e x) ≡ f (seg0-eqv x) (seg x)
  seg-cmpt = indZ-e (inr (seg-x0 e -_ (λ k -> k i0) λ p -> e≠i zero (p • i0))) seg0-eqv

open SectionOfSeg0 public


module ZStability where
  stab-lem1-0 : stab-lem1-type zero (seg zero)
  f (stab-lem1-0 x2) = fst
  g (stab-lem1-0 x2) e1 = e1 , (λ k -> k e1)
  η (stab-lem1-0 x2) (e1 , e2) =
    pair-eq (refl , is-prop-pi (λ _ ()) _ _)
  h (stab-lem1-0 x2) = g (stab-lem1-0 x2)
  ε (stab-lem1-0 x2) _ = refl

  stab-lem1 : (x : Z) -> stab-lem1-type x (seg x)
  stab-lem1 =
    indZ stab-lem1-0
         (λ x1 -> !e (tpt-eqv (stab-lem1-type (f e x1)) (seg-cmpt x1)) ∘e
                 stab-lem1-eqv x1 (seg x1))

  stab-lem2 : {x1 x2 : Z} -> (zero ≡ x1 + - x2) ≃ (x1 ≡ x2)
  stab-lem2 {x1} {x2} =
    !e (embed (+eqv (- x2))) ∘e
    !-eqv ∘e
    lcomp-eqv (+invr x2)

  stab : {x1 x2 : Z} -> x1 ≐ x2 -> x1 ≡ x2
  stab {x1} {x2} e1 =
    f stab-lem2 (f (stab-lem1 (x1 + - x2) zero)
                    (d00 (seg (x1 + (- x2))) , nn-map (g stab-lem2) e1))

  Z-is-set : is-set Z
  Z-is-set = stab-eq->is-set stab

  Z-has-dec-eq : has-dec-eq Z
  Z-has-dec-eq x1 x2 = aux1 (seg (x1 + - x2))
    module Z-has-dec-eq where
    aux1 : (s1 : Seg0 (x1 + - x2)) -> (x1 ≡ x2) ⊎ (x1 ≢ x2)
    aux1 (inl s1) = inr (λ e1 -> st r0 (! (g stab-lem2 e1))) where open Seg≠ s1
    aux1 (inr s1) = aux2 (dimn dmax)
      module _ where
      open Seg s1
      aux2 : R dmin dmax ⊎ (zero ≐ x1 + - x2) -> (x1 ≡ x2) ⊎ (x1 ≢ x2)
      aux2 (inl r1) = inr (λ e1 -> st r1 (g stab-lem2 e1))
      aux2 (inr e1) = inl (f stab-lem2 (stab e1))

open ZStability using (stab ; Z-has-dec-eq ; Z-is-set) public


module SectionDomainFibersAreProps where
  dom-seg-is-prop-eqv : (x1 : Z) -> (s1 : Seg0 x1) ->
                        ((x2 : Z) -> is-prop (D0 s1 x2)) ≃
                        ((x2 : Z) -> is-prop (D0 (f (seg0-eqv x1) s1) x2))

  dom-seg-is-prop-eqv x1 (inl s1) =
    aux (Seg.dimx (incr-min s1) (Seg.dmin (incr-min s1)))
    module dom-seg-is-prop-eqv-l where
    open Seg≠ s1
    eqv : ((x2 : Z) (d2 d3 : D x2) -> d2 ≡ d3) ≃
          ((x2 : Z) (d2 d3 : D x2 × (x1 ≢ x2)) -> d2 ≡ d3)
    f eqv ϕ x2 (d2 , n2) (d3 , n3) =
      pair-eq (ϕ x2 d2 d3 , is-prop-pi (λ _ ()) _ _)
    g eqv ϕ x2 d2 d3 = aux2 (dimn d2)
      module _ where
      aux2 : R dmin d2 ⊎ (x1 ≐ x2) -> d2 ≡ d3
      aux2 (inl r2) = ap fst (ϕ x2 (d2 , st r2) (d3 , st r2))
      aux2 (inr e2) =
        ap fst (g (embed (cl {x2}))
           (pair-eq
             (ap fst (ϕ (f e x2)
               (fst (f cl (d2 , ri e2 (λ k -> k refl) r0)) ,
                st (snd (f cl (d2 , ri e2 (λ k -> k refl) r0))))
               (fst (f cl (d3 , ri e2 (λ k -> k refl) r0)) ,
                st (snd (f cl (d3 , ri e2 (λ k -> k refl) r0))))) ,
              pr _ _)))

    η eqv _ = funext (λ x2 -> is-prop-is-prop (D x2) _ _)
    h eqv = g eqv
    ε eqv _ = funext (λ x2 -> is-prop-is-prop (D x2 × (x1 ≢ x2)) _ _)

    aux : (a : Seg.R (incr-min s1) (Seg.dmin (incr-min s1))
                                   (Seg.dmax (incr-min s1)) ⊎
               (f e x1 ≐ zero)) ->
          ((x2 : Z) -> is-prop (D x2)) ≃
          ((x2 : Z) ->
           is-prop (D0 (f (ide _ ⊎e nneg-part-eqv.eqv _)
                          (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                             (f ⊎-assoc (inl (npos-part-eqv.g-eqv _
                                               (incr-min s1) a))))) x2))
    aux (inl r1) = eqv
    aux (inr e1) = eqv

  {-
  ((x2 : Z) -> (d2 d3 : D x2) -> d2 ≡ d3) ≃
  ((x2 : Z) -> (d2 d3 : D x2 ⊎ D (g e x2) × (g e x2 ≐ x1)) -> d2 ≡ d3)
  -}
  f (dom-seg-is-prop-eqv x1 (inr s1)) ϕ x2 (inl d2) (inl d3) = ap inl (ϕ x2 d2 d3)
  f (dom-seg-is-prop-eqv x1 (inr s1)) ϕ x2 (inl d2) (inr (d3 , e3)) =
    rec⊥ (e3 (λ e3 -> ov1 (tpt D (g (adj' e) e3) d2))) where open Seg s1
  f (dom-seg-is-prop-eqv x1 (inr s1)) ϕ x2 (inr (d2 , e2)) (inl d3) =
    rec⊥ (e2 (λ e2 -> ov1 (tpt D (g (adj' e) e2) d3))) where open Seg s1
  f (dom-seg-is-prop-eqv x1 (inr s1)) ϕ x2 (inr (d2 , e2)) (inr (d3 , e3)) =
    ap inr (pair-eq (ϕ (g e x2) d2 d3 , is-prop-pi (λ _ ()) _ _))

  g (dom-seg-is-prop-eqv x1 (inr s1)) ϕ x2 d2 d3 = inl-eq (ϕ x2 (inl d2) (inl d3))

  η (dom-seg-is-prop-eqv x1 (inr s1)) ϕ = funext (λ x2 -> is-prop-is-prop _ _ _)
  h (dom-seg-is-prop-eqv x1 (inr s1)) = g (dom-seg-is-prop-eqv x1 (inr s1))
  ε (dom-seg-is-prop-eqv x1 (inr s1)) ϕ = funext (λ x2 -> is-prop-is-prop _ _ _)

  dom-seg-is-prop : (x1 x2 : Z) -> is-prop (D0 (seg x1) x2)
  dom-seg-is-prop x1 x2 =
    indZ (λ _ -> Z-is-set)
         (λ x1 -> pi-eqv-2 (λ x2 ->
           !e (tpt-eqv (λ s1 -> is-prop (D0 s1 x2))
                       (seg-cmpt x1))) ∘e
           dom-seg-is-prop-eqv x1 (seg x1) )
         x1 x2
         
open SectionDomainFibersAreProps using (dom-seg-is-prop) public




{-
  Conjecture:
    dom-seg-eqv-eqv : (x1 : Z) ->
                      ((s1 : Seg0 x1) -> (x2 : Z) -> D0 s1 x2 -> D0 s1 x2 ≃ D0 s1 x1) ≃
                      ((s1 : Seg0 (f e x1)) ->
                       (x2 : Z) -> D0 s1 x2 -> D0 s1 x2 ≃ D0 s1 (f e x1))
    dom-seg-eqv-eqv x1 = pi-eqv-1' (seg0-eqv x1) ∘e pi-eqv-2 eqv
      module dom-seg-eqv-eqv where
      eqv : (s1 : Seg0 x1) ->
            ((x2 : Z) -> D0 s1 x2 -> D0 s1 x2 ≃ D0 s1 x1) ≃
            ((x2 : Z) -> D0 (f (seg0-eqv x1) s1) x2 ->
              D0 (f (seg0-eqv x1) s1) x2 ≃ D0 (f (seg0-eqv x1) s1) (f e x1))
      eqv (inl s1) = aux1 (Seg.dimx (incr-min s1) (Seg.dmin (incr-min s1)))
        module _ where
        open Seg≠ s1
        lem1 : D x1 ≃ D (f e x1)
        lem1 = {!!}

        lem2 : x1 ≢ f e x1
        lem2 = {!!}

        aux3 : ((x2 : Z) -> D x2 -> D x2 ≃ D x1) ≃
               ((x2 : Z) -> D x2 × (x1 ≢ x2) -> D x2 × (x1 ≢ x2) ≃ D x1)
        f aux3 ϕ x2 (d2 , n2) = ϕ x2 d2 ∘e ×unitr (n2 , {!!})
        g aux3 ϕ x2 d2 = aux4 (dimn d2)
          module _ where
          aux4 : R dmin d2 ⊎ (x1 ≐ x2) -> D x2 ≃ D x1
          aux4 (inl r2) = ϕ x2 (d2 , st r2) ∘e !e (×unitr (st r2 , {!!}))
          aux4 (inr e2) = aux5 (stab e2) d2
            module _ where
            aux5 : {x2 : Z} -> (e2 : x1 ≡ x2) -> (d2 : D x2) -> D x2 ≃ D x1
            aux5 refl d2 = ϕ (f e x1) (f lem1 d2 , lem2) ∘e !e (×unitr (lem2 , {!!})) ∘e lem1

        η aux3 ϕ = funext (λ x2 -> funext (λ d2 -> aux6 x2 d2 (dimn d2)))
          module _ where
          aux6 : (x2 : Z) -> (d2 : D x2) ->
                 (a : R dmin d2 ⊎ (x1 ≐ x2)) -> aux4 (f aux3 ϕ) x2 d2 a ≡ ϕ x2 d2
          aux6 x2 d2 (inl r2) = biinv-eq (funext (λ d3 -> {!!}))
          aux6 x2 d2 (inr e2) = biinv-eq (funext (λ d3 -> aux7 e2 _ refl d2 d3))
            module _ where
            aux7 : {x2 : Z} -> (e2 : x1 ≐ x2) -> (e3 : x1 ≡ x2) -> stab e2 ≡ e3 -> (d2 : D x2) -> (d3 : D x2) -> f (aux5 (f aux3 ϕ) x2 d2 e2 e3 d2) d3 ≡ f (ϕ x2 d2) d3
            aux7 e2 refl _ d2 d3 = {!!}

        h aux3 = g aux3

        ε aux3 = {!!}

        aux2 : ((x2 : Z) -> D x2 -> D x2 ≃ D x1) ≃
               ((x2 : Z) ->
                 D x2 × (x1 ≢ x2) ->
                 D x2 × (x1 ≢ x2) ≃ D (f e x1) × (x1 ≢ f e x1))
        aux2 = {!!}

        aux1 : (a : Seg.R (incr-min s1) (Seg.dmin (incr-min s1))
                                        (Seg.dmax (incr-min s1)) ⊎
                    (f e x1 ≐ zero)) ->
               ((x2 : Z) -> D x2 -> D x2 ≃ D x1) ≃
               ((x2 : Z) -> (D0 (f (ide _ ⊎e nneg-part-eqv.eqv _)
                            (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                               (f ⊎-assoc (inl (npos-part-eqv.g-eqv _
                                                 (incr-min s1) a))))) x2) ->
                 (D0 (f (ide _ ⊎e nneg-part-eqv.eqv _)
                            (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                               (f ⊎-assoc (inl (npos-part-eqv.g-eqv _
                                                 (incr-min s1) a))))) x2) ≃
                 (D0 (f (ide _ ⊎e nneg-part-eqv.eqv _)
                            (f (ide _ ⊎e min-seg-eqv _ ⊎e ide _)
                               (f ⊎-assoc (inl (npos-part-eqv.g-eqv _
                                                 (incr-min s1) a))))) (f e x1)))
        aux1 (inl r2) = aux2
        aux1 (inr e2) = aux2


      eqv (inr s1) = {!!}
-}
