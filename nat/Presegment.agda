{-# OPTIONS --without-K #-}
module Presegment where

open import TT
open import Structure

open _≃_


module _ {B : Set} {b : B} where
  record Preseg (xmin xmax : b ≡ b) (s : b ≡ b → b ≡ b) : Set1 where
    constructor preseg
    field
      D : (x : b ≡ b) → Set
      dmin : D xmin
      dmax : D xmax
      R : Rel D
      rp : rel-is-prop R
      up : is-upcl s R rp dmin dmax


  open Preseg
  record PresegEqData (xmin xmax : b ≡ b) (s : b ≡ b → b ≡ b)
                      (p1 p2 : Preseg xmin xmax s) : Set1 where
    field
      Deq    : (x1 : b ≡ b) → D p1 x1 ≃ D p2 x1
      Deq'   : D p1 ≡ D p2
      Deqcoh : g fam-eqv Deq ≡ Deq'

      dmineq    : g (Deq xmin) (dmin p2) ≡ dmin p1
      dmineq'   : tpt (λ D → D xmin) (! Deq') (dmin p2) ≡ dmin p1
      dmineqcoh : elem-fam-eq Deq Deqcoh dmineq ≡ dmineq'

      dmaxeq    : g (Deq xmax) (dmax p2) ≡ dmax p1
      dmaxeq'   : tpt (λ D → D xmax) (! Deq') (dmax p2) ≡ dmax p1
      dmaxeqcoh : elem-fam-eq Deq Deqcoh dmaxeq ≡ dmaxeq'

      Req    : f-rel-eqv Deq (R p1) (R p2) × g-rel-eqv Deq (R p1) (R p2)
      Req'   : (λ {x1} → tpt Rel Deq' (R p1) {x1}) ≡ R p2
      Reqcoh : rel-eq Deq Deqcoh (rp p1) (rp p2) Req ≡ Req'

      rpeq' : (λ {x1} {d1} {x2} {d2} →
                 tpt2 (λ D → rel-is-prop {D = D}) Deq' Req' (rp p1)
                      {x1} {d1} {x2} {d2}) ≡
              rp p2

      upeq : up-data* Deq (R p1) (rp p1) (rp p2) Req
                      (dmin p1) (dmin p2) dmaxeq (up p1) (up p2)

  module _ {xmin xmax : b ≡ b} {s : b ≡ b → b ≡ b}
           {p1 p2 : Preseg xmin xmax s}
           (ir2 : is-irrefl (Preseg.R p2))
           (tr2 : is-trans (Preseg.R p2)) where
    open PresegEqData

    preseg-eq : PresegEqData xmin xmax s p1 p2 → p1 ≡ p2
    preseg-eq record { Deq = Deq ; Deq' = refl ; Deqcoh = Deqcoh
                     ; dmineq = dmineq ; dmineq' = refl ; dmineqcoh = dmineqcoh
                     ; dmaxeq = dmaxeq ; dmaxeq' = refl ; dmaxeqcoh = dmaxeqcoh
                     ; Req = Req ; Req' = refl ; Reqcoh = Reqcoh
                     ; rpeq' = refl ; upeq = upeq } =
      ap (λ w → preseg (D p2) (dmin p2) (dmax p2) (R p2) (rp p2)
                        (λ {x2} → w {x2}))
         (upcl-eq* Deq Deqcoh Req {rp1 = rp p1} Reqcoh refl dmineq dmineqcoh
                   dmaxeq dmaxeqcoh upeq)
