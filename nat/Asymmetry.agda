{-# OPTIONS --without-K #-}
module Asymmetry where

open import TT


module _ {B : Set} {b : B} where
  module _ (D : b ≡ b → Set) where
    asym : Set
    asym = {x1 : b ≡ b} → (n1 : x1 ≢ refl) → (d1 : D x1) → (d2 : D (! x1)) → ⊥


module _ {B : Set} {b : B} {l : b ≡ b}
         (ll-neq-refl : l ◾ l ≢ refl) (lll-neq-refl : l ◾ l ◾ l ≢ refl) where
  open import Structure
  open _≃_
  open SubEqv
  module _ {D : b ≡ b → Set}
           {dmin : D refl} {xmax : b ≡ b} {dmax : D xmax} (as : asym D)
           (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (mn : is-min R dmin) (mx : is-max R dmax) (gn : gen-rel (λ e → l ◾ e) R)
           (up : is-upcl (λ e → l ◾ e) R rp dmin dmax) where

    over-max-2 : D (l ◾ l ◾ xmax) → ⊥
    over-max-2 d1 = aux (di-min R ir tr tc mn d1)
      module over-max-2 where
      aux : R dmin d1 ⊎ (refl ≐ l ◾ l ◾ xmax) → ⊥
      aux (inl r1) = over-max-1 (lcomp-eqv l) R ir tr mx gn (fst (g up (d1 , r1)))
      aux (inr e2) =
        e2 (λ e2 →
          as ll-neq-refl
             (fst
               (f up (tpt D ◾unitr
                 (fst (f up
                   (dmin , mx dmin
                     (λ e3 →
                        ll-neq-refl
                          (! ◾unitr ◾ ! (f lwhisk-eqv e3) ◾ ◾assoc ◾ ! e2))))) ,
              mx (tpt D ◾unitr (fst (f up (dmin , mx dmin _))))
                 (λ e4 → lll-neq-refl
                    (! (f lwhisk-eqv (f lwhisk-eqv e4)) ◾ ! e2)))))
             (tpt D (! (g (eqv-adj (!e (lcomp-eqv (l ◾ l)))) (e2 ◾ ! ◾assoc)) ◾
                     ◾unitr)
                  dmax))

  module _ {D : b ≡ b → Set}
           {xmin : b ≡ b} {dmin : D xmin} {dmax : D refl} (as : asym D)
           (R : Rel D) (rp : rel-is-prop R)
           (ir : is-irrefl R) (tr : is-trans R) (tc : is-trich R)
           (mn : is-min R dmin) (mx : is-max R dmax) (gn : gen-rel (λ e → l ◾ e) R)
           (up : is-upcl (λ e → l ◾ e) R rp dmin dmax) where

    below-min-2 : D (! l ◾ ! l ◾ xmin) → ⊥
    below-min-2 d = aux (di-max R ir tr tc mx d)
      module below-min-2 where
      aux : R d dmax ⊎ (! l ◾ ! l ◾ xmin ≐ refl) → ⊥
      aux (inl r) =
        below-min-1 (lcomp-eqv l) R ir tr mn gn
                    (tpt D (ε (lcomp-eqv l) (! l ◾ xmin)) (fst (f up (d , r))))
      aux (inr e) =
        e (λ e →
          as ll-neq-refl
             (tpt D (f (eqv-adj (lcomp-eqv (! l ◾ ! l))) (◾assoc ◾ e) ◾
                     ◾unitr ◾
                     !-comp ◾
                     (!! [2,0,2] !!))
                  dmin)
             (fst (g up
               (tpt D (f (eqv-adj (!e (lcomp-eqv l))) (! !-comp))
                    (fst (g up (tpt D (! ◾invr) dmax ,
                          mn _ (λ e2 → ll-neq-refl
                            (! (f (eqv-adj (lcomp-eqv (! l ◾ ! l))) (◾assoc ◾ e) ◾
                                ◾unitr ◾
                                !-comp ◾
                                (!! [2,0,2] !!)) ◾
                             e2 ◾
                             ◾invr))))) ,
                    mn _ (λ e2 → lll-neq-refl
                      (! (f lwhisk-eqv (f (eqv-adj (!e (lcomp-eqv l))) (! !-comp) ◾
                          ! e2 ◾
                          f (eqv-adj (lcomp-eqv (! l ◾ ! l))) (◾assoc ◾ e) ◾
                          ◾unitr ◾
                          !-comp ◾
                          (!! [2,0,2] !!))) ◾
                       ◾invr))))))
