{-# OPTIONS --without-K --rewriting #-}
module IncrementMax where

open import S1TT
open import LoopS1LoopIsCentral
open import LoopS1HasDiv2Alg
open import Structure
open import Presegment
open import Asymmetry
open import Segment
open import LoopS1Segment


open _≃_
open EquivCoh
open SubEqv

module _ (xmax : b ≡ b) where
  incr-max-eqv : Seg≥0 xmax ≃ Seg>0 (l ◾ xmax)
  incr-max-eqv = eqv
    module incr-max-eqv where
    D-f-eqv : ((b ≡ b) → Set) → (b ≡ b) → Set
    D-f-eqv D x = D x ⊎ D (! l ◾ x) × (! l ◾ x ≐ xmax)

    D-g-eqv : ((b ≡ b) → Set) → (b ≡ b) → Set
    D-g-eqv D x = D x × (x ≢ l ◾ xmax)

    module _ (s : Seg≥0 xmax) where
      open Seg s
      f-eqv : Seg>0 (l ◾ xmax)
      Seg≠.D f-eqv = D-f-eqv D
  
      Seg≠.dmin f-eqv = inl dmin

      Seg≠.dmax f-eqv = inr (tpt D (! (ηl xmax)) dmax , λ k → k (ηl xmax))

      Seg≠.as f-eqv n (inl d1) (inl d2) = as n d1 d2
      Seg≠.as f-eqv {x1 = x1} n (inl d1) (inr (d2 , e2)) = aux (dimx d1)
        module as-f-eqv-l-r where
        aux : R d1 dmax ⊎ (x1 ≐ xmax) → ⊥
        aux (inl r1) =
          as (λ e3 → smn {d1 = d1}
              (ri (λ k → k refl)
                  (λ k → e2 (λ e2 → k
                    (! e2 ◾ ! !-comp ◾ ap ! (com-l x1) ◾ ap ! e3)))
                  r1))
             (fst (f up (d1 , r1)))
             (tpt D (! !-comp ◾ ap ! (com-l x1)) d2)
        aux (inr e3) = e2 (λ e2 → e3 (λ e3 →
          even-neq-odd (div2-dbl x1) div2-!l
                       (! (f (eqv-adj (!e (rcomp-eqv x1))) (e2 ◾ ! e3)))))

      Seg≠.as f-eqv {x1 = x1} n (inr (d1 , e1)) (inl d2) = aux (dimx d2)
        module as-f-eqv-r-l where
        aux : R d2 dmax ⊎ (! x1 ≐ xmax) → ⊥
        aux (inl r1) =
          as (λ e2 → smn {d1 = d2}
              (ri (λ k → k refl)
                  (λ k → e1 (λ e1 → k (! e1 ◾ e2)))
                  r1))
             d1
             (tpt D (! (com-l (! x1)) ◾ ! (! x1 [1,0,2] !!) ◾ ! !-comp)
                  (fst (f up (d2 , r1))))
        aux (inr e2) = e1 (λ e1 → e2 (λ e2 →
          even-neq-odd (div2-dbl (! x1)) div2-!l
                       (! (f (eqv-adj (rcomp-eqv x1)) (e1 ◾ ! e2)))))

      Seg≠.as f-eqv {x} n (inr (d1 , e1)) (inr (d2 , e2)) =
        e1 (λ e1 → e2 (λ e2 →
          n (no-2tor (g (eqv-adj (lcomp-eqv x))
                        (g lwhisk-eqv (e1 ◾ ! e2) ◾ ! ◾unitr)))))

      Seg≠.R f-eqv (inl d1) (inl d2) = R d1 d2
      Seg≠.R f-eqv (inl _) (inr _) = ⊤
      Seg≠.R f-eqv (inr _) _ = ⊥

      Seg≠.rp f-eqv {d1 = inl _} {d2 = inl _} = rp
      Seg≠.rp f-eqv {d1 = inl _} {d2 = inr _} = ⊤-is-prop
      Seg≠.rp f-eqv {d1 = inr _} {d2 = inl _} ()
      Seg≠.rp f-eqv {d1 = inr _} {d2 = inr _} ()

      Seg≠.rd f-eqv {d1 = inl _} {d2 = inl _} = rd
      Seg≠.rd f-eqv {d1 = inl _} {d2 = inr _} _ = tt
      Seg≠.rd f-eqv {d1 = inr _} {d2 = inl _} r = r (λ ())
      Seg≠.rd f-eqv {d1 = inr _} {d2 = inr _} r = r (λ ())

      Seg≠.ir f-eqv {d1 = inl _} {inl _} = ir
      Seg≠.ir f-eqv {d1 = inl d1} {inr (d2 , e2)} _ =
        e2 (λ e2 → om1 (tpt D (g (!e (eqv-adj (!e leqv))) e2) d1))

      Seg≠.tr f-eqv {d1 = inl _} {d21 = inl _} {inl _} {d3 = inl _} r1 r2 = tr r1 r2
      Seg≠.tr f-eqv {d1 = inl _} {d21 = inl _} {inl _} {d3 = inr _} _ _ = tt
      Seg≠.tr f-eqv {d1 = inl _} {d21 = inr (d21 , e1)} {inl d22} {d3 = inl _} _ _ =
        rec⊥ (e1 (λ e1 → om1 (tpt D (f (eqv-adj (!e leqv)) e1) d22)))
      Seg≠.tr f-eqv {d1 = inl _} {d21 = inr _} {inl _} {d3 = inr _} r1 r2 = tt

      Seg≠.tc f-eqv (inl d1) (inl d2) = tc d1 d2
      Seg≠.tc f-eqv (inl _) (inr _) = inl tt
      Seg≠.tc f-eqv (inr _) (inl _) = inr (inr tt)
      Seg≠.tc f-eqv {x1} (inr (d1 , e1)) {x2} (inr (d2 , e2)) =
        inr (inl (λ k → e1 (λ e1 → e2 (λ e2 → k (g lwhisk-eqv (e1 ◾ ! e2))))))

      Seg≠.mn f-eqv (inl d1) n = mn d1 n
      Seg≠.mn f-eqv (inr _) _ = tt

      Seg≠.mx f-eqv (inl _) _ = tt
      Seg≠.mx f-eqv (inr (d , e)) n =
        e (λ e → n (! (f (eqv-adj (!e leqv)) e)))

      Seg≠.gn f-eqv (inl d1) (inl d2) = gn d1 d2
      Seg≠.gn f-eqv (inl _) (inr _) = tt
      Seg≠.gn f-eqv (inr (d1 , e1)) (inl d2) =
        e1 (λ e1 → over-max-2 ll-neq-refl lll-neq-refl as R rp ir tr tc mn mx gn up
                    (tpt D (f lwhisk-eqv (f (eqv-adj (!e leqv)) e1)) d2))
      Seg≠.gn f-eqv {x1} (inr (d1 , e1)) (inr (d2 , e2)) =
        e1 (λ e1 → om1 (tpt D (ηl x1 ◾ ! (εl x1) ◾ ap fl e1) d2))

      Seg≠.ds f-eqv {d1 = inl d1} {d2 = inl d2} {inl d3} r1 r2 = ds r1 r2
      Seg≠.ds f-eqv {x1} {d1 = inl d1} {d2 = inl d2} {inr (d3 , e3)} r1 _ =
        e3 (λ e3 → smx {d1 = d2} (ri (λ k → k (! (ηl x1) ◾ e3)) (λ k → k refl) r1))

      f (Seg≠.up f-eqv {x2 = x}) (inl d , _) = aux (dimx d)
        module f-up-f-eqv where
        aux : R d dmax ⊎ (x ≐ xmax) →
              Σ (Seg≠.D f-eqv (fl x))
                (Seg≠.R f-eqv (Seg≠.dmin f-eqv))
        aux (inl r) = inl (fst (f up (d , r))) , snd (f up (d , r))
        aux (inr e) = inr (tpt D (! (ηl x)) d , nn-map (λ e → ηl x ◾ e) e) , tt

      g (Seg≠.up f-eqv {x2 = x}) (inl d , r) =
        inl (fst (g up (d , r))) , tt
      g (Seg≠.up f-eqv {x2 = x}) (inr (d , r) , _) =
        inl (tpt D (ηl x) d) , tt

      η (Seg≠.up f-eqv {x2 = x}) (inl d , tt) = aux (dimx d)
        module η-up-f-eqv where
        aux : (a1 : R d dmax ⊎ (x ≐ xmax)) →
              fst (g (Seg≠.up f-eqv) (f-up-f-eqv.aux d tt a1)) ≡ inl d
        aux (inl r) = ap inl (η^ up d r _)
        aux (inr e) = ap inl (ε (tpt-eqv D (ηl x)) d)

      h (Seg≠.up f-eqv) = g (Seg≠.up f-eqv)

      ε (Seg≠.up f-eqv {x2 = x}) (inl d1 , r1) = aux (dimx (fst (g up (d1 , r1))))
        module ε-up-f-eqv-l where
        aux : (a1 : R (fst (g up (d1 , r1))) dmax ⊎ (x ≐ xmax)) →
              fst (f-up-f-eqv.aux (fst (g up (d1 , r1))) tt a1) ≡ inl d1
        aux (inl r2) = ap inl (ε'^ up d1 r1 r2)
        aux (inr e1) = rec⊥ (e1 (λ e1 → om1 (tpt D (f lwhisk-eqv e1) d1)))

      ε (Seg≠.up f-eqv {x2 = x1}) (inr (d1 , e1) , r1) = aux (dimx (tpt D (ηl x1) d1))
        module ε-up-f-eqv-r where
        aux : (a1 : R (tpt D (ηl x1) d1) dmax ⊎ (x1 ≐ xmax)) →
              fst (f-up-f-eqv.aux (tpt D (η (lcomp-eqv l) x1) d1) tt a1) ≡
              inr (d1 , e1)
        aux (inl r2) = rec⊥ (stnn r2 (nn-map (λ e1 → ! (ηl x1) ◾ e1) e1))
        aux (inr e2) =
          ap inr (pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                               (η (tpt-eqv D (ηl x1)) d1))

      Seg≠.r0 f-eqv = tt

    module _ (s : Seg>0 (l ◾ xmax)) where
      open Seg≠ s
      g-eqv : Seg≥0 xmax
      Seg.D g-eqv = D-g-eqv D
      Seg.dmin g-eqv = dmin , st r0
      Seg.dmax g-eqv = fst (g up (dmax , r0)) , st (snd (g up (dmax , r0)))
      Seg.as g-eqv n (d1 , _) (d2 , _) = as n d1 d2
      Seg.R g-eqv (d1 , _) (d2 , _) = R d1 d2
      Seg.rp g-eqv = rp
      Seg.rd g-eqv = rd
      Seg.ir g-eqv = ir
      Seg.tr g-eqv = tr
      Seg.tc g-eqv (d1 , _) (d2 , _) = tc d1 d2
      Seg.mn g-eqv (d1 , _) n = mn d1 n
      Seg.mx g-eqv {x} (d , e1) n =
        dv r0 (mx d (λ e2 → e1 (! e2))) (λ e2 → n (! e2))
      Seg.gn g-eqv (d1 , _) (d2 , _) = gn d1 d2
      Seg.ds g-eqv = ds

      f (Seg.up g-eqv {x}) ((d1 , e1) , r1) =
        (fst (f up (d1 , mx d1 (λ e2 → e1 (! e2)))) ,
         st (ub (mx d1 (λ e2 → e1 (! e2))) (mx d1 (λ e2 → e1 (! e2)))
                    (λ e → st r1 e))) ,
        snd (f up (d1 , mx d1 (λ e2 → e1 (! e2))))
      g (Seg.up g-eqv {x}) ((d1 , e1) , r1) =
        (fst (g up (d1 , r1)) , st (snd (g up (d1 , r1)))) ,
        dmon r1 r0 (mx d1 (λ e2 → e1 (! e2)))
      η (Seg.up g-eqv {x}) ((d1 , e1) , r1) =
        pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                     (η^ up d1 (mx d1 (λ e2 → e1 (! e2))) _)
      h (Seg.up g-eqv) = g (Seg.up g-eqv)
      ε (Seg.up g-eqv {x}) ((d1 , _) , r2) =
        pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                     (ε'^ up d1 r2 _)


    module _ (s : Seg≥0 xmax) where
      open Seg s

      open Seg (g-eqv (f-eqv s))
        renaming
        (D to D' ; dmin to dmin' ; dmax to dmax' ; R to R' ; rp to rp' ;
         tc to tc' ; up to up' ; ri to ri' ; ub to ub')
        using ()

      open PresegEqData      
      η-eqv : g-eqv (f-eqv s) ≡ s
      η-eqv = seg-eq eq-data
        module η-eqv where
        Deq-eq-data : (x : b ≡ b) → D' x ≃ D x
        f (Deq-eq-data x) (inl d , e) = d
        f (Deq-eq-data x) (inr (d , e) , n) =
          rec⊥ (e (λ e → (n (f (eqv-adj (!e leqv)) e))))
        g (Deq-eq-data x) d = inl d , (λ e → om1 (tpt D e d))
        η (Deq-eq-data x) (inl d , e) =
          pair-prop-eq (λ _ → is-prop-pi (λ _ ())) refl
        η (Deq-eq-data x) (inr (d , e) , n) =
          rec⊥ (e (λ e → (n (f (eqv-adj (!e leqv)) e))))
        h (Deq-eq-data x) = g (Deq-eq-data x)
        ε (Deq-eq-data x) d = refl

        eq-data : PresegEqData refl xmax fl
                               (preseg D' dmin' dmax' R'
                                       (λ {x1} {d1} {x2} {d2} →
                                          rp' {x1} {d1} {x2} {d2}) up')
                               record { Seg s }
        Deq eq-data = Deq-eq-data
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl
        
        dmineq eq-data = ap (λ n → (inl dmin , n)) (is-prop-pi (λ _ ()) _ _)
        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl
        dmaxeq eq-data = pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                                      (ap inl (! (ε (tpt-eqv D (ηl xmax)) dmax)))
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl

        Req eq-data = id , id
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → rp' {x1} {d1} {x2} {d2})
                 rp (id , id)
        Reqcoh eq-data = refl

        rpeq' eq-data = rel-is-prop-eq (Deq eq-data) refl (id , id) refl

        -----
        upeq eq-data {x2 = x2} d2 r2 r3 = aux1 _ refl
          module upeq-eq-data where
          aux1 : (a1 : Σ (D' (l ◾ x2)) (R' dmin')) →
                 f up' ((inl d2 , (λ e → om1 (tpt D e d2))) , r2) ≡ a1 →
                 f (Deq-eq-data (l ◾ x2)) (fst a1) ≡ fst (f up (d2 , r3))
          aux1 ((inr (d4 , n) , e1) , r4) β1 =
            rec⊥ (n (λ e → e1 (! (η' (!e leqv) (l ◾ x2)) ◾ ap fl e)))
          aux1 ((inl d4 , _) , r4) β1 = aux2 (dimx d2) (ap fst (ap fst β1))
            module aux1 where
            aux2 : (a1 : R d2 dmax ⊎ (x2 ≐ xmax)) →
                   fst (f-up-f-eqv.aux s d2 tt a1) ≡ inl d4 →
                   f (Deq-eq-data (l ◾ x2))
                     (inl d4 , (λ e → om1 (tpt D e d4))) ≡
                   fst (f up (d2 , r3))
            aux2 (inl _) β2 = ! (inl-eq β2) ◾ ap (λ r → fst (f up (d2 , r))) (rp _ _)
            aux2 (inr _) β2 = rec⊥ (inl-neq-inr (! β2))


    module _ (s : Seg>0 (l ◾ xmax)) where
      open Seg≠ s

      open Seg≠ (f-eqv (g-eqv s))
        renaming
        (D to D' ; dmin to dmin' ; dmax to dmax' ; R to R' ; rp to rp' ; up to up' ;
         dimx to dimx')
        using ()

      open PresegEqData
      
      ε-eqv : f-eqv (g-eqv s) ≡ s
      ε-eqv = seg≠-eq eq-data
        module ε-eqv where
        f-Deq-eq-data : (x : b ≡ b) → D' x → D x
        f-Deq-eq-data x (inl (d , _)) = d
        f-Deq-eq-data x (inr ((d , n) , e)) =
          fst (f su (d , (mx d (λ e → n (! e)))))

        eq-data : PresegEqData refl (l ◾ xmax) fl
                                 (preseg D' dmin' dmax' R'
                                         (λ {x1} {d1} {x2} {d2} →
                                            rp' {x1} {d1} {x2} {d2}) up')
                                 record { Seg≠ s }
        f (Deq eq-data x) = f-Deq-eq-data x
        g (Deq eq-data x) d = aux (dimx d)
          module g-Deq-eq-data where
          aux : R d dmax ⊎ (x ≐ l ◾ xmax) →
                D x × (x ≡ l ◾ xmax → ⊥) ⊎
                (D (! l ◾ x) × (! l ◾ x ≢ l ◾ xmax)) × (! l ◾ x ≐ xmax)
          aux (inl r) = inl (d , st r)
          aux (inr e) =
            inr ((fst (g su (d , ri (λ k → k refl) (nn-map ! e) r0)) ,
                 (λ e → om1 (tpt D (f (eqv-adj (!e leqv)) e) d))) ,
                 nn-map (g (eqv-adj (!e leqv))) e)
        η (Deq eq-data x) (inl (d , n)) = aux _
          module η-Deq-eq-data-l where
          aux : (a1 : R d dmax ⊎ (x ≐ l ◾ xmax)) →
                g-Deq-eq-data.aux x d a1 ≡ inl (d , n)
          aux (inl _) = ap (λ n → inl (d , n)) (is-prop-pi (λ _ ()) _ _)
          aux (inr e) = rec⊥ (e n)
          
        η (Deq eq-data x) (inr ((d , n) , e)) = aux _
          module η-Deq-eq-data-r where
          aux : (a1 : R (f-Deq-eq-data x (inr ((d , n) , e))) dmax ⊎
                      (x ≐ l ◾ xmax)) →
                g-Deq-eq-data.aux x _ a1 ≡ inr ((d , n) , e)
          aux (inl r) = rec⊥ (e (f (neg-eqv (eqv-adj (!e leqv))) (st r)))
          aux (inr _) =
            ap inr (pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                                 (pair-prop-eq (λ _ → is-prop-pi (λ _ ()))
                                               (η^ su d _ _))) 
        h (Deq eq-data x) = g (Deq eq-data x)
        ε (Deq eq-data x) d = aux (dimx d)
          module ε-Deq-eq-data where
          aux : (a1 : R d dmax ⊎ (x ≐ l ◾ xmax)) →
                f-Deq-eq-data x (g-Deq-eq-data.aux x d a1) ≡ d
          aux (inl _) = refl
          aux (inr _) = ε'^ su d _ _
        Deq' eq-data = g fam-eqv (Deq eq-data)
        Deqcoh eq-data = refl
        
        dmineq eq-data = aux (dimx dmin)
          module dmineq-eq-data where
          aux : (a1 : R dmin dmax ⊎ (refl ≐ l ◾ xmax)) →
                g-Deq-eq-data.aux refl dmin a1 ≡ dmin'
          aux (inl _) = ap inl (pair-prop-eq (λ _ → is-prop-pi (λ _ ())) refl)
          aux (inr e) = rec⊥ (stnn r0 e)

        dmineq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmineq eq-data)
        dmineqcoh eq-data = refl
        
        dmaxeq eq-data = aux (dimx dmax)
          module dmaxeq-eq-data where
          coh : {x1 x2 x3 : b ≡ b} → {d1 : D (l ◾ x3)} →
                (r1 : R dmin d1) → (r2 : R dmin d1) → (r3 : R dmin d1) →
                (e1 : l ◾ x1 ≡ x2) → (e2 : ! l ◾ x2 ≡ x3) →
                {e3 : ! l ◾ l ◾ x1 ≡ ! l ◾ x2} → {e4 : l ◾ ! l ◾ x2 ≡ l ◾ x3} →
                ap gl e1 ≡ e3 → ap fl e2 ≡ e4 → 
                fst (g up
                 (tpt (λ x → Σ (D x) (R dmin))
                      (! (! (ap (λ y → l ◾ ! l ◾ y) e1) ◾ ap fl e3 ◾ e4))
                      (d1 , r1))) ≡
                fst (tpt (λ x → D x × (x ≢ l ◾ xmax))
                         (! e2)
                         (fst (g up (d1 , r2)) , st (snd (g up (d1 , r3)))))
          coh r1 r2 r3 refl refl refl refl =
            ap (λ r → fst (g up (_ , r))) (rp _ _)
          
          aux : (a1 : R dmax dmax ⊎ (l ◾ xmax ≐ l ◾ xmax)) →
                g-Deq-eq-data.aux (l ◾ xmax) dmax a1 ≡ dmax'
          aux (inl r) = rec⊥ (ir r)
          aux (inr e) =
            ap inr (pair-prop-eq
                    (λ _ → is-prop-pi (λ _ ()))
                    (pair-prop-eq
                     (λ _ → is-prop-pi (λ _ ()))
                     (coh _ _ _ _ (ηl xmax) (νl (l ◾ xmax)) (τl xmax))))
          
        dmaxeq' eq-data = elem-fam-eq (Deq eq-data) (Deqcoh eq-data) (dmaxeq eq-data)
        dmaxeqcoh eq-data = refl
        
        fst (Req eq-data) {x1} {x2} {d1} {d2} = aux (dimx d1) (dimx d2)
          module fst-Req-eq-data where
          aux : (a1 : R d1 dmax ⊎ (x1 ≐ l ◾ xmax)) →
                (a2 : R d2 dmax ⊎ (x2 ≐ l ◾ xmax)) →
                R' (g-Deq-eq-data.aux x1 d1 a1) (g-Deq-eq-data.aux x2 d2 a2) →
                R d1 d2
          aux (inl _) (inl _) r = r
          aux (inl r) (inr e) _ = ri (λ k → k refl) (nn-map ! e) r
          aux (inr _) _ ()
          
        snd (Req eq-data) {x1} {x2} {d1} {d2} = aux (dimx d1) (dimx d2)
          module snd-Req-eq-data where
          aux : (a1 : R d1 dmax ⊎ (x1 ≐ l ◾ xmax)) →
                (a2 : R d2 dmax ⊎ (x2 ≐ l ◾ xmax)) →
                R d1 d2 →
                R' (g-Deq-eq-data.aux x1 d1 a1) (g-Deq-eq-data.aux x2 d2 a2)
          aux (inl _) (inl _) r = r
          aux (inl _) (inr _) _ = tt
          aux (inr e) (inl r1) r2 = smx {d1 = d2} (ri e (λ k → k refl) r2)
          aux (inr e1) (inr e2) r = ir {d1 = dmax} {d2 = dmax} (ri e1 e2 r)
          
        Req' eq-data =
          rel-eq (Deq eq-data) refl
                 (λ {x1} {d1} {x2} {d2} → rp' {x1} {d1} {x2} {d2}) rp (Req eq-data)
        Reqcoh eq-data = refl

        rpeq' eq-data = rel-is-prop-eq (Deq eq-data) refl (Req eq-data) refl
        
        upeq eq-data {x2 = x2} d22 r1 r2 = aux1 (dimx d22) r1
          module upeq-eq-data where
          aux1 : (a1 : R d22 dmax ⊎ (x2 ≐ l ◾ xmax)) →
                 (r1 : R' (g-Deq-eq-data.aux x2 d22 a1) dmax') →
                 f-Deq-eq-data (l ◾ x2)
                   (fst (f up' (g-Deq-eq-data.aux x2 d22 a1 , r1))) ≡
                 fst (f up (d22 , r2))
          aux1 (inl r3) r1 = aux2 (Seg.dimx (g-eqv s) (d22 , st r3))
            module aux1 where
            coh : {x1 x2 : b ≡ b} → (e1 : ! l ◾ l ◾ x2 ≡ x1) →
                  (e2 : l ◾ ! l ◾ l ◾ x2 ≡ l ◾ x1) → ap fl e1 ≡ e2 →
                  {d1 : D x1} → {r1 : R d1 dmax} → {r2 : R d1 dmax} →
                  fst (tpt (λ x₁ → Σ (D x₁) (R dmin)) e2
                           (f up (fst (tpt (λ x → D x × (x ≢ l ◾ xmax))
                                      (! e1) (d1 , strict R ir r1)) ,
                            mx (fst (tpt (λ x → D x × (x ≢ l ◾ xmax))
                                         (! e1) (d1 , strict R ir r1)))
                               (λ e → snd (tpt (λ x → D x × (x ≢ l ◾ xmax))
                                           (! e1) (d1 , strict R ir r1)) (! e))))) ≡
                  fst (f up (d1 , r2))
            coh refl _ refl {d1} = ap (λ r → fst (f up (d1 , r))) (rp _ _)

            aux2 : (a2 : Seg.R (g-eqv s)
                           (d22 , strict (λ {x1} → R) (λ {x1} {d1} {d2} → ir) r3)
                           (Seg.dmax (g-eqv s))
                           ⊎ (x2 ≐ xmax)) →
                   f-Deq-eq-data (l ◾ x2)
                     (fst (f-up-f-eqv.aux
                            (g-eqv s) (d22 , strict R ir r3) r1 a2)) ≡
                   fst (f up (d22 , r2))
            aux2 (inl _) = ap (λ r → fst (f up (d22 , r))) (rp _ _)
            aux2 (inr _) =
              coh (ηl x2) _ (! ◾unitl ◾
                             f rwhisk-eqv
                               (! ◾invl ◾
                                f rwhisk-eqv
                                  (ap ! (! (ap (ap fl) (inv-comm ηl x2)) ◾
                                         ! (ap-fn-comp fl gl (ap fl (ηl x2)))))) ◾
                             ◾assoc ◾
                             ap (λ e → ! (ap (λ y → l ◾ ! l ◾ y) e) ◾
                                        ap (λ e2 → l ◾ e2)
                                           (η (lcomp-eqv l) (! l ◾ l ◾ x2)) ◾ e)
                                (τl x2))
                   

    eqv : Seg≥0 xmax ≃ Seg>0 (l ◾ xmax)
    f eqv = f-eqv
    g eqv = g-eqv
    η eqv = η-eqv
    h eqv = g eqv
    ε eqv = ε-eqv
