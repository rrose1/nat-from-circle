{-# OPTIONS --without-K --rewriting #-}
module IncrementMin where

open import S1TT
open import LoopS1LoopIsCentral
open import LoopS1HasDiv2Alg
open import Structure
open import Presegment
open import Asymmetry
open import Segment
open import LoopS1Segment


open _≃_
open SubEqv

module _ (xmin : b ≡ b) where

  incr-min-eqv : Seg<0 xmin ≃ Seg≤0 (l ◾ xmin)
  incr-min-eqv = eqv
    module incr-min-eqv where
    D-f-eqv : ((b ≡ b) → Set) → (b ≡ b) → Set
    D-f-eqv D x = D x × (xmin ≢ x)

    D-g-eqv : ((b ≡ b) → Set) → (b ≡ b) → Set
    D-g-eqv D x = D x ⊎ D (l ◾ x) × (l ◾ x ≐ l ◾ xmin)

    module _ (s : Seg<0 xmin) where
      open Seg≠ s
      f-eqv : Seg≤0 (l ◾ xmin)
      Seg.D f-eqv = D-f-eqv D
      Seg.dmin f-eqv = fst (f up (dmin , r0)) , st (snd (f up (dmin , r0)))
      Seg.dmax f-eqv = dmax , st r0 
      Seg.as f-eqv n (d1 , _) (d2 , _) = as n d1 d2
      Seg.R f-eqv (d1 , _) (d2 , _) = R d1 d2
      Seg.rp f-eqv = rp
      Seg.rd f-eqv = rd
      Seg.ir f-eqv = ir
      Seg.tr f-eqv = tr
      Seg.tc f-eqv (d1 , _) (d2 , _) = tc d1 d2
      Seg.mn f-eqv {x1 = x} (d , n1) n2 =
        ri (λ k → k refl) (λ k → k (εl x))
           (ub {d3 = tpt D (! (εl x)) d}
               r0 (ri (λ k → k refl) (λ k → k (! (εl x))) (mn d n1))
                      (g (neg-eqv (eqv-adj (lcomp-eqv l))) n2))   
      Seg.mx f-eqv (d , _) = mx d
      Seg.gn f-eqv (d1 , _) (d2 , _) = gn d1 d2
      Seg.ds f-eqv = ds
      
      f (Seg.up f-eqv) ((d1 , n1), r2) =
        (fst (f up (d1 , r2)) , st (snd (f up (d1 , r2)))) , umon r0 r2 (mn d1 n1 )
      g (Seg.up f-eqv {x2 = x2}) ((d1 , n1), r2) =
        (fst (g up (d1 , (mn d1 n1))) ,
         st (dv (mn d1 n1) (mn d1 n1)
                (λ e1 → stnn r2 (λ k → k (f lwhisk-eqv e1))))) ,
        mx (fst (g up (d1 , (mn d1 n1))))
           (λ e1 → stnn (snd (g up (d1 , (mn d1 n1)))) (λ k → k (! e1)))
      η (Seg.up f-eqv) ((d2 , n2), r3) =
        pair-prop-eq (λ _ → is-prop-pi (λ _ ())) (η^ up d2 r3 _)
      h (Seg.up f-eqv) = g (Seg.up f-eqv)
      ε (Seg.up f-eqv) ((d2 , n2), r3) =
        pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
          (ε'^ up d2 (mn d2 n2) (mx (fst (g up (d2 , (mn d2 n2)))) (λ e1 →
            stnn (snd (g up (d2 , (mn d2 n2)))) (λ k → k (! e1)))))


    module _ (s : Seg≤0 (l ◾ xmin)) where
      open Seg s
      g-eqv : Seg<0 xmin
      Seg≠.D g-eqv = D-g-eqv D
      Seg≠.dmin g-eqv = inr (dmin , (λ k → k refl))
      Seg≠.dmax g-eqv = inl dmax
      
      Seg≠.as g-eqv n (inl d1) (inl d2) = as n d1 d2

      Seg≠.as g-eqv {x1 = x} n (inl d1) (inr (d2 , e2)) = aux (dimn d1)
        module as-incr-min-l-r where
        aux : R dmin d1 ⊎ (l ◾ xmin ≐ x) → ⊥
        aux (inl r) =
          as (λ e3 → om1 (tpt D (f (eqv-adj (!e leqv)) e3) d1))
             (fst (g up (tpt D (! (εl x)) d1 ,
                          ri (λ k → k refl) (λ k → k (! (εl x))) r)))
             (tpt D (! (com-l (! x)) ◾ ! (! x [1,0,2] !!) ◾ ! !-comp) d2)
        aux (inr e3) =
          e2 (λ e2 → e3 (λ e3 →
            even-neq-odd (div2-dbl x) div2-l
                         (! (f (eqv-adj (!e (rcomp-eqv x))) (e2 ◾ e3)))))

      Seg≠.as g-eqv {x1 = x} n (inr (d1 , e1)) (inl d2) = aux (dimn d2)
        module as-incr-min-r-l where
        aux : R dmin d2 ⊎ (l ◾ xmin ≐ ! x) → ⊥
        aux (inl r) =
          as (λ e2 → om1 (tpt D (! ◾unitl ◾
                                  g (eqv-adj (!e (rcomp-eqv x))) (! e2) ◾
                                  ! ◾unitr) d2))
             d1
             (fst (g up
              (tpt D (! (εl (! x)) ◾
                      ! (l [1,0,2] !-comp) ◾
                      (l [1,0,2] ap ! (com-l x))) d2 ,
               ri (λ k → k refl)
                  (λ k → k (! (εl (! x)) ◾
                             ! (l [1,0,2] !-comp) ◾
                             (l [1,0,2] ap ! (com-l x)))) r)))
        
        aux (inr e2) =
          e1 (λ e1 → e2 (λ e2 →
            even-neq-odd (div2-dbl (! x)) div2-l
                         (! (f (eqv-adj (rcomp-eqv x)) (e1 ◾ e2)))))
          
        
      Seg≠.as g-eqv {x} n (inr (d1 , e1)) (inr (d2 , e2)) =
        e1 (λ e1 → e2 (λ e2 →
          n (no-2tor (g (eqv-adj (lcomp-eqv x))
                        (g lwhisk-eqv (e1 ◾ ! e2) ◾ ! ◾unitr)))))

      Seg≠.R g-eqv (inl d1) (inl d2) = R d1 d2
      Seg≠.R g-eqv (inl _) (inr _) = ⊥
      Seg≠.R g-eqv (inr _) (inl _) = ⊤
      Seg≠.R g-eqv (inr _) (inr _) = ⊥
      
      Seg≠.rp g-eqv {d1 = inl _} {d2 = inl _} = rp
      Seg≠.rp g-eqv {d1 = inl _} {d2 = inr _} ()
      Seg≠.rp g-eqv {d1 = inr _} {d2 = inl _} = ⊤-is-prop
      Seg≠.rp g-eqv {d1 = inr _} {d2 = inr _} ()
      
      Seg≠.rd g-eqv {d1 = inl _} {d2 = inl _} = rd
      Seg≠.rd g-eqv {d1 = inl _} {d2 = inr _} r = r (λ ())
      Seg≠.rd g-eqv {d1 = inr _} {d2 = inl _} _ = tt
      Seg≠.rd g-eqv {d1 = inr _} {d2 = inr _} r = r (λ ())
      
      Seg≠.ir g-eqv {d1 = inl _} {inl _} = ir
      Seg≠.ir g-eqv {d1 = inl _} {inr _} ()
      Seg≠.ir g-eqv {d1 = inr (d1 , e1)} {inl d2} _ =
        e1 (λ e1 → bm1 (tpt D (! (ηl xmin ◾ ! (g lwhisk-eqv e1))) d2))
      Seg≠.ir g-eqv {d1 = inr _} {inr _} ()
      
      Seg≠.tr g-eqv {d1 = inl _} {d21 = inl _} {inl _} {d3 = inl _} r1 r2 = tr r1 r2
      Seg≠.tr g-eqv {d1 = inl _} {d21 = inl d21} {inr (d22 , e22)} {d3 = inl _} _ _ =
        rec⊥ (e22 (λ e22 → (bm1 (tpt D (g lwhisk-eqv e22 ◾ ! (ηl xmin)) d21))))
      Seg≠.tr g-eqv {d1 = inr _} {d21 = inl _} {inl _} {d3 = inl _} r1 r2 = tt
      Seg≠.tr g-eqv {d1 = inr _} {d21 = inl _} {inr _} {d3 = inl _} r1 r2 = tt

      Seg≠.tc g-eqv (inl d1) (inl d2) = tc d1 d2
      Seg≠.tc g-eqv (inl _) (inr _) = inr (inr tt)
      Seg≠.tc g-eqv (inr _) (inl _) = inl tt
      Seg≠.tc g-eqv (inr (d1 , e1)) (inr (d2 , e2)) =
        inr (inl (λ k → e1 (λ e1 → e2 (λ e2 → k (g lwhisk-eqv (e1 ◾ ! e2))))))
      
      Seg≠.mn g-eqv (inl _) _ = tt
      Seg≠.mn g-eqv (inr (d , e)) n = e (λ e → n (! (g lwhisk-eqv e)))
      
      Seg≠.mx g-eqv (inl d) n = mx d n
      Seg≠.mx g-eqv (inr _) _ = tt
      
      Seg≠.gn g-eqv (inl d1) (inl d2) = gn d1 d2
      Seg≠.gn g-eqv (inl d1) (inr (d2 , e2)) =
        e2 (λ e2 → below-min-2 ll-neq-refl lll-neq-refl as R rp ir tr tc mn mx gn up
                    (tpt D (f (eqv-adj leqv) (g lwhisk-eqv e2) ◾
                            f lwhisk-eqv (! (ηl xmin))) d1))
      Seg≠.gn g-eqv (inr _) (inl _) = tt
      Seg≠.gn g-eqv (inr (d1 , e1)) (inr (d2 , e2)) =
        e2 (λ e2 → bm1 (tpt D (g lwhisk-eqv e2 ◾ ! (ηl xmin)) d1))

      Seg≠.ds g-eqv {d1 = inl _} {d2 = inl _} {inl _} r1 r2 = ds r1 r2
      Seg≠.ds g-eqv {d1 = inr (d1 , e1)} {d2 = inl d2} {inl d3} _ r2 =
        smn {d1 = d2} (ri (λ k → k refl) e1 r2)
      
      f (Seg≠.up g-eqv {x2}) (inl d2 , r2) = inl (fst (f up (d2 , r2))) , tt
      f (Seg≠.up g-eqv {x2}) (inr (d2 , e2) , _) = inl d2 , tt
      
      g (Seg≠.up g-eqv {x2}) (inl d2 , tt) = aux (dimn d2)
        module g-up-g-eqv where
        aux : R dmin d2 ⊎ (l ◾ xmin ≐ fl x2) →
              Σ (D x2 ⊎ D (l ◾ x2) × (l ◾ x2 ≐ l ◾ xmin))
                (λ d → Seg≠.R g-eqv d (inl dmax))
        aux (inl r3) = inl (fst (g up (d2 , r3))) , snd (g up (d2 , r3))
        aux (inr e1) = inr (d2 , (λ k → e1 (λ e1 → k (! e1)))) , tt
      
      η (Seg≠.up g-eqv {x2}) (inl d2 , r2) = aux (dimn (fst (f up (d2 , r2))))
        module η-up-g-eqv-l where
        aux : (a : R dmin (fst (f up (d2 , r2))) ⊎ (l ◾ xmin ≐ fl x2)) →
              fst (g-up-g-eqv.aux (fst (f up (d2 , r2))) a) ≡ inl d2
        aux (inl r3) = ap inl (η^ up d2 r2 r3)
        aux (inr e1) =
          rec⊥ (e1 (λ e1 → (bm1 (tpt D (! (ηl x2) ◾ ! (f lwhisk-eqv e1)) d2))))
        
      η (Seg≠.up g-eqv {x2}) (inr (d2 , e2) , _) = aux (dimn d2)
        module η-up-g-eqv-r where
        aux : (a : R dmin d2 ⊎ (l ◾ xmin ≐ fl x2)) →
              fst (g-up-g-eqv.aux d2 a) ≡ inr (d2 , e2)
        aux (inl r3) = rec⊥ (smn {d1 = dmin} (ri (λ k → k refl) e2 r3))
        aux (inr e3) = ap inr (pair-prop-eq (λ _ → is-prop-pi λ _ ()) refl)
        
      h (Seg≠.up g-eqv) = g (Seg≠.up g-eqv)

      ε (Seg≠.up g-eqv {x2}) (inl d2 , tt) = aux (dimn d2)
        module ε-up-g-eqv where
        aux : (a : R dmin d2 ⊎ (l ◾ xmin ≐ fl x2)) →
              fst (f (Seg≠.up g-eqv) (g-up-g-eqv.aux d2 a)) ≡ inl d2
        aux (inl r3) = ap inl (ε'^ up d2 r3 (snd (g up (d2 , r3))))
        aux (inr e1) = refl
        
      Seg≠.r0 g-eqv = tt


    module _ (s : Seg<0 xmin) where
      open Seg≠ s

      open Seg≠ (g-eqv (f-eqv s))
        renaming
        (D to D' ; dmin to dmin' ; dmax to dmax' ; R to R' ; rp to rp' ; up to up')
        using ()

      open PresegEqData
      
      η-eqv : g-eqv (f-eqv s) ≡ s
      η-eqv = seg≠-eq eq-data
        module η-eqv where
        eq-data : PresegEqData xmin refl fl
                   (preseg D' dmin' dmax' R'
                           (λ {x1} {d1} {x2} {d2} → rp' {x1} {d1} {x2} {d2}) up')
                   record { Seg≠ s }
                   
        f (Deq eq-data x) (inl (d , _)) = d
        f (Deq eq-data x) (inr ((d , n) , _)) = fst (g up (d , mn d n))
        
        g (Deq eq-data x) d = aux (dimn d)
          module g-Deq-eq-data where
          aux : R dmin d ⊎ (xmin ≐ x) → D' x
          aux (inl r) = inl (d , st r)
          aux (inr e) = inr ((fst (f up (d , ri e (λ k → k refl) r0)) ,
                              st (snd (f up (d , ri e (λ k → k refl) r0)))) ,
                             (λ k → e (λ e → k (f lwhisk-eqv (! e)))))
        
        η (Deq eq-data x) (inl (d1 , n1)) = aux (dimn d1)
          module η-Deq-eq-data-l where
          aux : (a : R dmin d1 ⊎ (xmin ≐ x)) →
                g-Deq-eq-data.aux x d1 a ≡ inl (d1 , n1)
          aux (inl r2) = ap (λ n → inl (d1 , n)) (is-prop-pi (λ _ ()) (st r2) n1)
          aux (inr e1) = rec⊥ (e1 n1)
          
        η (Deq eq-data x) (inr ((d1 , n1) , e1)) =
          aux (dimn (fst (g up (d1 , (mn d1 n1)))))
          module η-Deq-eq-data-r where
          aux : (a : R dmin (fst (g up (d1 , (mn d1 n1)))) ⊎ (xmin ≐ x)) →
                g-Deq-eq-data.aux x (fst (g up (d1 , (mn d1 n1)))) a ≡
                inr ((d1 , n1) , e1)
          aux (inl r2) = rec⊥ (stnn r2 (λ k → e1 (λ e1 → k (! (g lwhisk-eqv e1)))))
          aux (inr e2) =
            ap inr
              (pair-prop-eq
                (λ _ → is-prop-pi (λ _ ()))
                (pair-prop-eq
                  (λ _ → is-prop-pi (λ _ ()))
                  (ε'^ up d1 (mn d1 n1) (ri e2 (λ k → k refl) r0))))
          
        h (Deq eq-data x) = g (Deq eq-data x)
        
        ε (Deq eq-data x) d = aux (dimn d)
          module ε-Deq-eq-data where
          aux : (a : R dmin d ⊎ (xmin ≐ x)) →
                f (Deq eq-data x) (g-Deq-eq-data.aux x d a) ≡ d
          aux (inl r) = refl
          aux (inr e) = η^ up d _ _
          
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl
        
        dmineq eq-data = aux (dimn dmin)
          module dmineq-eq-data where
          aux : (a : R dmin dmin ⊎ (xmin ≐ xmin)) →
                g-Deq-eq-data.aux xmin dmin a ≡ dmin'
          aux (inl r) = rec⊥ (ir r)
          aux (inr e) =
            ap inr (pair-prop-eq
                     (λ _ → is-prop-pi λ _ ())
                     (pair-prop-eq
                       (λ _ → is-prop-pi λ _ ())
                       (ap (λ r → fst (f up (dmin , r)))
                           (rp (ri e (λ k → k refl) r0) r0))))
        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl
        
        dmaxeq eq-data = aux (dimn dmax)
          module dmaxeq-eq-data where
          aux : (a : R dmin dmax ⊎ (xmin ≐ refl)) →
                g-Deq-eq-data.aux refl dmax a ≡ dmax'
          aux (inl r) =
            ap (λ n → inl (dmax , n)) (is-prop-pi (λ _ ()) (st r) (st r0))
          aux (inr e) = rec⊥ (stnn r0 e)
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
          aux (inl r2) (inr e1) = rec⊥ (stnn (tr r2 r1) e1)
          aux (inr _) (inl _) = tt
          aux (inr e1) (inr e2) =
            rec⊥ (stnn r1 (λ k → e1 (λ e1 → e2 (λ e2 → k (! e1 ◾ e2)))))
            
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → rp' {x1} {d1} {x2} {d2}) rp (Req eq-data)
        Reqcoh eq-data = refl
        
        rpeq' eq-data = rel-is-prop-eq (Deq eq-data) refl (Req eq-data) refl
        
        upeq eq-data {x2 = x2} d22 r1 r2 = aux1 _ refl
          module upeq-eq-data where
          aux1 : (a1 : Σ (Seg.D (f-eqv s) x2 ⊎
                          Seg.D (f-eqv s) (l ◾ x2) × (l ◾ x2 ≐ l ◾ xmin))
                         (λ d → R' d dmax')) →
                 (g-Deq-eq-data.aux x2 d22 (dimn d22) , r1) ≡ a1 →
                 f (Deq eq-data (l ◾ x2)) (fst (f up' a1)) ≡ fst (f up (d22 , r2))
          aux1 (inl (d3 , r3) , r4) β1 = aux2 (dimn d22) (ap fst β1)
            module aux1-l where
            aux2 : (a2 : R dmin d22 ⊎ (xmin ≐ x2)) →
                   g-Deq-eq-data.aux x2 d22 a2 ≡ inl (d3 , r3) → 
                   fst (f up (d3 , r4)) ≡ fst (f up (d22 , r2))
            aux2 (inl _) β2 =
              ap (λ d → fst (f up d))
                 (pair-prop-eq (λ _ → rp) (! (ap fst (inl-eq β2))))
            aux2 (inr _) β2 = rec⊥ (inl-neq-inr (! β2))
            
          aux1 (inr ((d3 , r3) , e1) , tt) β1 = aux2 _ (ap fst β1)
            module aux1-r where
            aux2 : (a2 : R dmin d22 ⊎ (xmin ≐ x2)) →
                   g-Deq-eq-data.aux x2 d22 a2 ≡ inr ((d3 , r3) , e1) →
                   d3 ≡ fst (f up (d22 , r2))
            aux2 (inl _) β2 = rec⊥ (inl-neq-inr β2)
            aux2 (inr _) β2 =
              ! (ap fst (ap fst (inr-eq β2))) ◾
              ap (λ r → fst (f up (d22 , r))) (rp _ _)

    module _ (s : Seg≤0 (l ◾ xmin)) where
      open Seg s

      open Seg (f-eqv (g-eqv s))
        renaming
        (D to D' ; dmin to dmin' ; dmax to dmax' ; R to R' ; rp to rp' ; up to up')
        using ()

      open PresegEqData
      
      ε-eqv : f-eqv (g-eqv s) ≡ s
      ε-eqv = seg-eq eq-data
        module ε-eqv where
        eq-data : PresegEqData (l ◾ xmin) refl fl
                   (preseg D' dmin' dmax' R'
                           (λ {x1} {d1} {x2} {d2} → rp' {x1} {d1} {x2} {d2}) up')
                   record { Seg s }
                   
        f (Deq eq-data x) (inl d , _) = d
        f (Deq eq-data x) (inr (d1 , e1) , n1) =
          rec⊥ (e1 (λ e2 → n1 (! (g lwhisk-eqv e2))))
        g (Deq eq-data x) d = inl d , (λ e → bm1 (tpt D (! e ◾ ! (ηl xmin)) d))
        η (Deq eq-data x) (inl d , _) =
          ap (λ n → (inl d , n)) (is-prop-pi (λ _ ()) _ _)
        η (Deq eq-data x) (inr (d1 , e1) , n1) =
          rec⊥ (e1 (λ e2 → n1 (! (g lwhisk-eqv e2))))
        h (Deq eq-data x) = g (Deq eq-data x)
        ε (Deq eq-data x) d = refl 

        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl
        
        dmineq eq-data = ap (λ n → (inl dmin , n)) (is-prop-pi (λ _ ()) _ _)
        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl

        dmaxeq eq-data = ap (λ n → (inl dmax , n)) (is-prop-pi (λ _ ()) _ _)
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl

        Req eq-data = id , id
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → rp' {x1} {d1} {x2} {d2})
                 rp (id , id)
        Reqcoh eq-data = refl

        rpeq' eq-data = rel-is-prop-eq (Deq eq-data) refl (id , id) refl

        upeq eq-data d22 r1 r2 = ap (λ r → fst (f up (d22 , r))) (rp r1 r2)

    eqv : Seg<0 xmin ≃ Seg≤0 (l ◾ xmin)
    f eqv = f-eqv
    g eqv = g-eqv
    η eqv = η-eqv
    h eqv = g eqv
    ε eqv = ε-eqv

