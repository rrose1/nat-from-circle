{-# OPTIONS --without-K #-}
module Structure where

open import TT


open _≃_
open EquivCoh

module _ {X : Set} where
  module _ (D : X → Set) where
    Rel : Set1
    Rel = {x1 : X} → (d1 : D x1) → {x2 : X} → (d2 : D x2) → Set

  module _ {D : X → Set} (R : Rel D) where
    rel-is-prop : Set
    rel-is-prop = {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
                  is-prop (R d1 d2)

    rel-has-dne : Set
    rel-has-dne = {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
                  has-dne (R d1 d2)

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
    strict-nn : {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
                (r1 : R d1 d2) → (e : x1 ≐ x2) → ⊥
    strict-nn {x1 = x1} {x2 = x2} r e = e (λ {refl → ir r})

    strict : {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
             (r1 : R d1 d2) → (e : x1 ≡ x2) → ⊥ {lzero}
    strict {x1 = x1} {x2 = x2} r refl = ir r

  module _ {D : X → Set} (R : Rel D) where
    is-trans : Set
    is-trans = {x1 : X} → {d1 : D x1} →
               {x2 : X} → {d21 : D x2} → {d22 : D x2} →
               {x3 : X} → {d3 : D x3} →
               (r1 : R d1 d21) → (r2 : R d22 d3) → R d1 d3

  module _ {D : X → Set} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) where
    antisym :  {x1 : X} → {d1 : D x1} → {x2 : X} → {d2 : D x2} →
               R d1 d2 → R d2 d1 → ⊥
    antisym r1 r2 = ir (tr r1 r2)

  module _ {D : X → Set} (R : Rel D) where
    is-trich : Set
    is-trich = {x1 : X} → (d1 : D x1) → {x2 : X} → (d2 : D x2) →
               R d1 d2 ⊎ (x1 ≐ x2) ⊎ R d2 d1

  module _ {D : X → Set} (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) where
    trich-is-prop : {x1 : X} → (d1 : D x1) → {x2 : X} → (d2 : D x2) →
                    is-prop (R d1 d2 ⊎ (x1 ≐ x2) ⊎ R d2 d1)
    trich-is-prop {x1} d1 {x2} d2 (inl r1) (inl r2) =
      ap inl (rp r1 r2)
    trich-is-prop {x1} d1 {x2} d2 (inl r1) (inr (inl e1)) =
      rec⊥ (strict-nn R ir r1 e1)
    trich-is-prop {x1} d1 {x2} d2 (inl r1) (inr (inr r2)) =
      rec⊥ (antisym R ir tr r1 r2)  
    trich-is-prop {x1} d1 {x2} d2 (inr (inl e1)) (inl r1) =
      rec⊥ (strict-nn R ir r1 e1)
    trich-is-prop {x1} d1 {x2} d2 (inr (inl e1)) (inr (inl e2)) =
      ap inr (ap inl (is-prop-pi (λ _ ()) e1 e2))
    trich-is-prop {x1} d1 {x2} d2 (inr (inl e1)) (inr (inr r1)) =
      rec⊥ (e1 (λ e → strict R ir r1 (! e)))
    trich-is-prop {x1} d1 {x2} d2 (inr (inr r1)) (inl r2) =
      rec⊥ (antisym R ir tr r1 r2)
    trich-is-prop {x1} d1 {x2} d2 (inr (inr r1)) (inr (inl e1)) =
      rec⊥ (e1 (λ e → strict R ir r1 (! e)))
    trich-is-prop {x1} d1 {x2} d2 (inr (inr r1)) (inr (inr r2)) =
      ap inr (ap inr (rp r1 r2))

  module _ {D : X → Set} (R : Rel D) (rp : rel-is-prop R) (rd : rel-has-dne R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R) where

    tpt-rel : {x1 x2 : X} → (e1 : x1 ≐ x2) → {d1 : D x1} → {d2 : D x2} →
              {x3 x4 : X} → (e2 : x3 ≐ x4) → {d3 : D x3} → {d4 : D x4} →
              R d1 d3 → R d2 d4
    tpt-rel {_} {_} e1 {_} {d2} {_} {x4} e2 {_} {d4} r1 =
      rd (λ k → e1 (λ e1 → e2 (λ e2 → k (aux e1 e2 r1 (tc d2 d4)))))
      module tpt-rel where
      aux : {x1 x2 : X} → (e1 : x1 ≡ x2) → {d1 : D x1} → {d2 : D x2} →
            {x3 x4 : X} → (e2 : x3 ≡ x4) → {d3 : D x3} → {d4 : D x4} →
            R d1 d3 → R d2 d4 ⊎ (x2 ≐ x4) ⊎ R d4 d2 → R d2 d4
      aux e1 e2 r1 (inl r2) = r2
      aux refl refl r1 (inr (inl e3)) = rec⊥ (strict-nn R ir r1 e3)
      aux refl refl r1 (inr (inr r2)) = rec⊥ (ir (tr r1 r2))

  module _ (s : X → X) {D : X → Set} (R : Rel D) where
    gen-rel : Set
    gen-rel = {x1 : X} → (d1 : D x1) → (d2 : D (s x1)) → R d1 d2

    is-disc : Set
    is-disc = {x1 : X} → {d1 : D x1} →
              {x2 : X} → {d2 : D x2} →
              {d3 : D (s x1)} → (r1 : R d1 d2) → (r2 : R d2 d3) → ⊥

    is-upcl : (rp : rel-is-prop R) →
              {x1 : X} → (d1 : D x1) → {x4 : X} → (d4 : D x4) → Set
    is-upcl rp d1 d4 = {x2 : X} → SubEqv (λ d2 → rp {x1 = x2} {d1 = d2} {d2 = d4})
                                          (λ d3 → rp {d1 = d1} {x2 = s x2} {d2 = d3})
                         -- (Σ (D x2) (λ d2 → R d2 d4)) ≃
                         -- (Σ (D (s x2)) (λ d3 → R d1 d3))

  module _ (e1 : X ≃ X) {D : X → Set} (R : Rel D) (gn : gen-rel (f e1) R) where
    shift-gen : {x1 : X} → (d1 : D (g e1 x1)) → (d2 : D x1) → R d1 d2
    shift-gen {x1} d1 d2 =
      tpt2 (λ x d → R d1 {x} d)
           (ε' e1 x1)
           (ε (tpt-eqv D (ε' e1 x1)) d2)
           (gn d1 (g (tpt-eqv D (ε' e1 x1)) d2))

  module _ (s t : X → X) (s-t : (x : X) → s (t x) ≡ x)
           {D : X → Set} (R : Rel D) (rp : rel-is-prop R)
           {x1 : X} {d1 : D x1} {x4 : X} {d4 : D x4}
           (up : is-upcl s R rp d1 d4) where
    open SubEqv
    shift-up : {x2 : X} → SubEqv (λ d2 → rp {x1 = t x2} {d1 = d2} {d2 = d4})
                                  (λ d3 → rp {d1 = d1} {x2 = x2} {d2 = d3})
    shift-up {x2} =
      f subeqv-eqv (tpt-eqv (λ x → (Σ (D x) (R d1))) (s-t x2)) ∘s
      up {x2 = t x2}


  module _ (s t : X → X) (t-s : (x : X) → t (s x) ≡ x)
           {D : X → Set} (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (gn : gen-rel s R) (ds : is-disc s R)
           {x1 : X} {d1 : D x1} {x2 : X} {d2 : D x2}
           {x3 : X} {d3 : D x3} {x4 : X} {d4 : D x4}
           (up : is-upcl s R rp d1 d4)
           (r1 : R d2 d4) (r2 : R d3 d4) (r3 : R d2 d3) where
    open SubEqv

    up-mono : R (fst (f up (d2 , r1))) (fst (f up (d3 , r2)))
    up-mono = aux (tc (fst (f up (d2 , r1))) (fst (f up (d3 , r2))))  
      module up-mono where
      aux : R (fst (f up (d2 , r1))) (fst (f up (d3 , r2))) ⊎ (s x2 ≐ s x3) ⊎
            R (fst (f up (d3 , r2))) (fst (f up (d2 , r1))) →
            R (fst (f up (d2 , r1))) (fst (f up (d3 , r2)))
      aux (inl r5) = r5
      aux (inr (inl e1)) =
        rec⊥ (strict-nn R ir r3 (nn-map (λ e → ! (t-s x2) ◾ ap t e ◾ t-s x3) e1))
      aux (inr (inr r5)) =
        rec⊥ (ds r3 (tr (gn d3 (fst (f up (d3 , r2)))) r5))

  module _ (s : X → X)
           {D : X → Set} (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (gn : gen-rel s R) (ds : is-disc s R)
           {x1 : X} {d1 : D x1} {x2 : X} {d2 : D (s x2)}
           {x3 : X} {d3 : D (s x3)} {x4 : X} {d4 : D x4}
           (up : is-upcl s R rp d1 d4)
           (r1 : R d1 d2) (r2 : R d1 d3) (r3 : R d2 d3) where
    open SubEqv

    down-mono : R (fst (g up (d2 , r1))) (fst (g up (d3 , r2))) 
    down-mono = aux (tc (fst (g up (d2 , r1))) (fst (g up (d3 , r2))))
      module down-mono where
      aux : R (fst (g up (d2 , r1))) (fst (g up (d3 , r2))) ⊎ (x2 ≐ x3) ⊎
            R (fst (g up (d3 , r2))) (fst (g up (d2 , r1))) →
            R (fst (g up (d2 , r1))) (fst (g up (d3 , r2)))
      aux (inl r5) = r5
      aux (inr (inl e1)) =
        rec⊥ (strict-nn R ir r3 (nn-map (ap s) e1))
      aux (inr (inr r5)) =
        rec⊥ (ds (tr r5 (gn (fst (g up (d2 , r1))) d2)) r3)

  module _ (s t : X → X) (t-s : (x : X) → t (s x) ≡ x)
           {D : X → Set} (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (gn : gen-rel s R) (ds : is-disc s R)
           {x1 : X} {d1 : D x1} {x2 : X} {d2 : D x2}
           {x3 : X} {d3 : D (s x3)} {x4 : X} {d4 : D x4}
           (up : is-upcl s R rp d1 d4)
           (r1 : R d2 d4) (r2 : R d2 d3) (n1 : x2 ≢ x3) where
    open SubEqv

    up-below : R (fst (f up (d2 , r1))) d3
    up-below = aux (tc (fst (f up (d2 , r1))) d3)
      module up-below where
      aux : R (fst (f up (d2 , r1))) d3 ⊎ (s x2 ≐ s x3) ⊎
            R d3 (fst (f up (d2 , r1))) →
            R (fst (f up (d2 , r1))) d3
      aux (inl r3) = r3
      aux (inr (inl e1)) = rec⊥ (e1 (λ e → n1 (! (t-s x2) ◾ ap t e ◾ t-s x3)))
      aux (inr (inr r3)) = rec⊥ (ds r2 r3)


  module _ (s t : X → X) (t-s : (x : X) → t (s x) ≡ x)
           {D : X → Set} (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (gn : gen-rel s R) (ds : is-disc s R)
           {x1 : X} {d1 : D x1} {x2 : X} {d2 : D x2}
           {x3 : X} {d3 : D (s x3)} {x4 : X} {d4 : D x4}
           (up : is-upcl s R rp d1 d4)
           (r1 : R d1 d3) (r2 : R d2 d3) (n1 : x2 ≢ x3) where
    open SubEqv

    down-over : R d2 (fst (g up (d3 , r1)))
    down-over = aux (tc d2 (fst (g up (d3 , r1))))
      module down-over where
      aux : R d2 (fst (g up (d3 , r1))) ⊎ (x2 ≐ x3) ⊎
            R (fst (g up (d3 , r1))) d2 →
            R d2 (fst (g up (d3 , r1)))
      aux (inl r3) = r3
      aux (inr (inl e1)) = rec⊥ (e1 (λ e1 → n1 e1))
      aux (inr (inr r3)) = rec⊥ (ds r3 r2)

  module _ {D : X → Set} (R : Rel D) where
    is-min : {xmin : X} → (dmin : D xmin) → Set
    is-min {xmin} dmin =
      {x1 : X} → (d1 : D x1) → (n1 : xmin ≢ x1) → R dmin d1

    is-max : {xmax : X} → (dmax : D xmax) → Set
    is-max {xmax} dmax =
      {x1 : X} → (d1 : D x1) → (n1 : xmax ≢ x1) → R d1 dmax                   


  module _ {D : X → Set} {x0 : X} {d0 : D x0} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) where

    strict-min : (mn : is-min R d0) → {x1 : X} → {d1 : D x1} → R d1 d0 → ⊥
    strict-min mn {d1 = d1} r1 =
      antisym R ir tr (mn d1 (λ e1 → strict R ir r1 (! e1))) r1

    strict-max : (mx : is-max R d0) → {x1 : X} → {d1 : D x1} → R d0 d1 → ⊥
    strict-max mx {d1 = d1} r1 =
      antisym R ir tr (mx d1 (λ e1 → strict R ir r1 e1)) r1


  module _ (e1 : X ≃ X) {D : X → Set} {x0 : X} {d0 : D x0} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R)
           (mn : is-min R d0) (gn : gen-rel (f e1) R) where

    below-min-1 : D (g e1 x0) → ⊥
    below-min-1 d1 = strict-min R ir tr mn (shift-gen e1 R gn d1 d0)

  module _ (e1 : X ≃ X) {D : X → Set} {x0 : X} {d0 : D x0} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R)
           (mx : is-max R d0) (gn : gen-rel (f e1) R) where

    over-max-1 : D (f e1 x0) → ⊥
    over-max-1 d1 = strict-max R ir tr mx (gn d0 d1)

  module _ {D : X → Set} {x0 : X} {d0 : D x0} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R) (mx : is-max R d0)
           {x1 : X} (d1 : D x1) where

    di-max : R d1 d0 ⊎ (x1 ≐ x0)
    di-max = aux (tc d1 d0)
      module di-max where
      aux : R d1 d0 ⊎ (x1 ≐ x0) ⊎ R d0 d1 → R d1 d0 ⊎ (x1 ≐ x0)
      aux (inl r1) = inl r1
      aux (inr (inl e1)) = inr e1
      aux (inr (inr r1)) = rec⊥ (strict-max R ir tr mx r1)

  module _ {D : X → Set} {x0 : X} {d0 : D x0} (R : Rel D)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (mn : is-min R d0)
           {x1 : X} (d1 : D x1) where

    di-min : R d0 d1 ⊎ (x0 ≐ x1)
    di-min = aux (tc d0 d1)
      module di-min where
      aux : R d0 d1 ⊎ (x0 ≐ x1) ⊎ R d1 d0 → R d0 d1 ⊎ (x0 ≐ x1)
      aux (inl r1) = inl r1
      aux (inr (inl e1)) = inr e1
      aux (inr (inr r1)) = rec⊥ (strict-min R ir tr mn r1)



  {- Equality principles -}
  {- Refactor using record types to organize equality input data (cf. Presegments) -}

  module _ {D1 D2 : X → Set} (e1 : (x : X) → D1 x ≃ D2 x) where
    elem-fam-eqv : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
                   {x : X} → {d1 : D1 x} → {d2 : D2 x} →
                   (g (e1 x) d2 ≡ d1) ≃ (tpt (λ D → D x) (! e2) d2 ≡ d1)
    f (elem-fam-eqv {refl} β {x1} {d1} {d2}) e2 =
      ! (ap (λ e → g e d2) (ap (λ D → D x1) (f (eqv-adj (!e fam-eqv)) β))) ◾ e2
    g (elem-fam-eqv {refl} β {x1} {d1} {d2}) e2 =
      ap (λ e → g e d2) (ap (λ D → D x1) (f (eqv-adj (!e fam-eqv)) β)) ◾ e2
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
         (! (ap (λ e → (g (e x2) d2)) (! (ε' fam-eqv e1) ◾ ap (f fam-eqv) α))) ◾
      ap (λ d → R1 d _) {x2 = (g (e1 x1) d1)}
         (! (ap (λ e → (g (e x1) d1)) (! (ε' fam-eqv e1) ◾ ap (f fam-eqv) α)))

    rel-eqv : {e2 : D1 ≡ D2} → g fam-eqv e1 ≡ e2 →
              {R1 : Rel D1} → {R2 : Rel D2} →
              (pr1 : rel-is-prop R1) → (pr2 : rel-is-prop R2) →
              f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2 ≃
              ((λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2)
    f (rel-eqv α pr1 pr2) (f1 , g1) =
      funext' (λ {x1} → funext (λ d1 →
      funext' (λ {x2} → funext (λ d2 →
      coh α ◾ ua (biinv f1 g1 (λ _ → pr1 _ _) g1 (λ _ → pr2 _ _)) ))))

    g (rel-eqv α {R1 = R1} pr1 pr2) e3 =
      ((λ {x1} {x2} {d1} {d2} →
          g (f tpt-id-eqv (ap (λ R → R d1 d2) (! e3) ◾ coh α))) ,
       (λ {x1} {x2} {d1} {d2} →
          f (f tpt-id-eqv (ap (λ R → R d1 d2) (! e3) ◾ coh α))))

    η (rel-eqv α pr1 pr2) (f1 , g1) =
      cart-pair-eq
       ((is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ → pr2))))) _ _) ,
         is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
         is-prop-pi' (λ {_} → is-prop-pi (λ _ → pr1))))) _ _)

    h (rel-eqv α pr1 pr2) = g (rel-eqv α pr1 pr2)

    ε (rel-eqv α pr1 pr2) e3 =
      g (eqv-adj (!e happly'-eqv)) (funext' (λ {x1} →
      g (eqv-adj (!e happly-eqv)) (funext (λ d1 →
      g (eqv-adj (!e happly'-eqv)) (funext' (λ {x2} →
      g (eqv-adj (!e happly-eqv)) (funext (λ d2 →
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
                        tpt2 (λ D → rel-is-prop {D = D}) e2 e4 pr1 {x1} {d1} {x2} {d2}) ≡ pr2
    rel-is-prop-eq _ _ _ =
      is-prop-pi' (λ {_} → is-prop-pi' (λ {_} → is-prop-pi' (λ {_} →
      is-prop-pi' (λ {_} → is-prop-is-prop _)))) _ _

  module _ {s : X → X} {x1 : X} {x4 : X} where
     upcl-tpt : {D1 D2 : (x1 : X) → Set} → (e1 : D1 ≡ D2) →
                  {R1 : Rel D1} → {R2 : Rel D2} →
                  (e2 : (λ {x1} → tpt Rel e1 R1 {x1})≡ R2) →
                  {rp1 : rel-is-prop R1} → {rp2 : rel-is-prop R2} →
                  (e3 : (λ {x1} {d1} {x2} {d2} →
                           tpt2 (λ D → rel-is-prop {D = D}) e1 e2 rp1 {x1} {d1} {x2} {d2}) ≡ rp2) →
                  {d11 : D1 x1} → {d21 : D2 x1} →
                  (e4 : tpt (λ D → D x1) (! e1) d21 ≡ d11) →
                  {d14 : D1 x4} → {d24 : D2 x4} →
                  (e5 : tpt (λ D → D x4) (! e1) d24 ≡ d14) →
                  is-upcl s R1 rp1 d11 d14 → is-upcl s R2 rp2 d21 d24
     upcl-tpt refl refl refl refl refl up = up

     open SubEqv

     module _ {D1 D2 : (x1 : X) → Set} (e1 : (x1 : X) → D1 x1 ≃ D2 x1)
              (R1 : Rel D1) {R2 : Rel D2}
              (rp1 : rel-is-prop R1) (rp2 : rel-is-prop R2)
              (e3 : f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2)
              (d11 : D1 x1) (d21 : D2 x1)
              {d14 : D1 x4} {d24 : D2 x4} (e8 : g (e1 x4) d24 ≡ d14)
              (up1 : is-upcl s R1 rp1 d11 d14) (up2 : is-upcl s R2 rp2 d21 d24)
              where
       up-data :  Set
       up-data = {x2 : X} → (p : Σ (D2 x2) (λ d22 → R2 d22 d24)) →
                   f (e1 (s x2))
                     (fst (f up1 (g (e1 x2) (fst p) ,
                      tpt (R1 (g (e1 x2) (fst p))) e8 (snd e3 (snd p))))) ≡
                   fst (f up2 p)

       up-data* :  Set
       up-data* = {x2 : X} → (d22 : D2 x2) →
                  (r1 : R1 (g (e1 x2) d22) d14) → (r2 : R2 d22 d24) →
                   f (e1 (s x2)) (fst (f up1 (g (e1 x2) d22 , r1))) ≡
                   fst (f up2 (d22 , r2))


     upcl-eq : {D1 D2 : (x1 : X) → Set} → (e1 : (x1 : X) → D1 x1 ≃ D2 x1) →
               {e2 : D1 ≡ D2} → (α : g fam-eqv e1 ≡ e2) →
               {R1 : Rel D1} → {R2 : Rel D2} →
               (e3 : f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2) →
               {rp1 : rel-is-prop R1} → {rp2 : rel-is-prop R2} →
               {e4 : (λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2} →
               (rel-eq e1 α rp1 rp2 e3 ≡ e4) →
               (e5 : (λ {x1} {d1} {x2} {d2} →
                        tpt2 (λ D → rel-is-prop {D = D}) e2 e4 rp1
                             {x1} {d1} {x2} {d2}) ≡ rp2) →
               {d11 : D1 x1} → {d21 : D2 x1} →
               (e6 : g (e1 x1) d21 ≡ d11) →
               {e7 : tpt (λ D → D x1) (! e2) d21 ≡ d11} →
                 elem-fam-eq e1 α e6 ≡ e7 →
               {d14 : D1 x4} → {d24 : D2 x4} →
               (e8 : g (e1 x4) d24 ≡ d14) →
               {e9 : tpt (λ D → D x4) (! e2) d24 ≡ d14} →
                 elem-fam-eq e1 α e8 ≡ e9 →
               {up1 : is-upcl s R1 rp1 d11 d14} → {up2 : is-upcl s R2 rp2 d21 d24} →
               up-data e1 R1 rp1 rp2 e3 d11 d21 e8 up1 up2 →
               (λ {x2} → upcl-tpt e2 e4 e5 e7 e9 up1 {x2}) ≡ up2
     upcl-eq e1 {refl} α1 {R1} e3 {rp1} {rp2} {refl} α2 refl e6 {refl}
             α3 e8 {refl} α4 {up1} {up2} α5 =
       funext' (λ {x2} → subeqv-eq (λ p →
         ! (ap (λ p → fst (f up1 p))
               (pair-prop-eq
                 (λ _ → rp1)
                 (ap (λ e → g e (fst p))
                     (ap (λ D → D x2)
                         (f (eqv-adj (!e fam-eqv)) α1))))) ◾
         ! (ap (λ e → f e (fst (f up1 (g (e1 x2) (fst p) ,
                            tpt (R1 (g (e1 x2) (fst p))) e8 (snd e3 (snd p))))))
               (ap (λ a → a (s x2)) (f (eqv-adj (!e fam-eqv)) α1))) ◾
         α5 p))


     upcl-eq* : {D1 D2 : (x1 : X) → Set} → (e1 : (x1 : X) → D1 x1 ≃ D2 x1) →
               {e2 : D1 ≡ D2} → (α : g fam-eqv e1 ≡ e2) →
               {R1 : Rel D1} → {R2 : Rel D2} →
               (e3 : f-rel-eqv e1 R1 R2 × g-rel-eqv e1 R1 R2) →
               {rp1 : rel-is-prop R1} → {rp2 : rel-is-prop R2} →
               {e4 : (λ {x1} → tpt Rel e2 R1 {x1}) ≡ R2} →
               (rel-eq e1 α rp1 rp2 e3 ≡ e4) →
               (e5 : (λ {x1} {d1} {x2} {d2} →
                        tpt2 (λ D → rel-is-prop {D = D}) e2 e4 rp1
                             {x1} {d1} {x2} {d2}) ≡ rp2) →
               {d11 : D1 x1} → {d21 : D2 x1} →
               (e6 : g (e1 x1) d21 ≡ d11) →
               {e7 : tpt (λ D → D x1) (! e2) d21 ≡ d11} →
                 elem-fam-eq e1 α e6 ≡ e7 →
               {d14 : D1 x4} → {d24 : D2 x4} →
               (e8 : g (e1 x4) d24 ≡ d14) →
               {e9 : tpt (λ D → D x4) (! e2) d24 ≡ d14} →
                 elem-fam-eq e1 α e8 ≡ e9 →
               {up1 : is-upcl s R1 rp1 d11 d14} → {up2 : is-upcl s R2 rp2 d21 d24} →
               up-data* e1 R1 rp1 rp2 e3 d11 d21 e8 up1 up2 →
               (λ {x2} → upcl-tpt e2 e4 e5 e7 e9 up1 {x2}) ≡ up2
     upcl-eq* e1 {refl} α1 {R1} e3 {rp1} {rp2} {refl} α2 refl e6 {refl}
              α3 e8 {refl} α4 {up1} {up2} α5 =
       funext' (λ {x2} →
        subeqv-eq (λ w → ! (ap (λ w → fst (f up1 w))
               (pair-prop-eq
                 (λ _ → rp1)
                 (ap (λ e → g e (fst w))
                     (ap (λ D → D x2)
                         (f (eqv-adj (!e fam-eqv)) α1))))) ◾
         ! (ap (λ e → f e (fst (f up1 (g (e1 x2) (fst w) ,
                            tpt (R1 (g (e1 x2) (fst w))) e8 (snd e3 (snd w))))))
               (ap (λ a → a (s x2)) (f (eqv-adj (!e fam-eqv)) α1))) ◾ α5 {x2} (fst w) (tpt (R1 (g (e1 x2) (fst w))) e8 (snd e3 (snd w))) (snd w)))
