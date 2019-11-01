{-# OPTIONS --without-K --rewriting #-}
module LoopS1Segment where

open import S1TT
open import LoopS1LoopIsCentral
open import LoopS1HasDiv2Alg
open import Structure
open import Presegment
open import Asymmetry
open import Segment


open _≃_
open SubEqv
open Seg
open Seg≠
open Seg=

leqv = lcomp-eqv l {b}
open _≃_ leqv
  renaming (f to fl ; g to gl ; η to ηl ; ε to εl) using ()
  public
τl = lcomp-τ l {b}
νl = lcomp-ν l {b}


{- by "0" we mean refl -}

Seg<0 : (xmin : b ≡ b) → Set1
Seg<0 xmin = Seg≠ xmin refl leqv

Seg≤0 : (xmin : b ≡ b) → Set1
Seg≤0 xmin = Seg xmin refl leqv

Seg-0 : (xmin : b ≡ b) → Set1
Seg-0 xmin = Seg= xmin refl leqv

Seg+0 : (xmax : b ≡ b) → Set1
Seg+0 xmax = Seg= refl xmax leqv

Seg≥0 : (xmax : b ≡ b) → Set1
Seg≥0 xmax = Seg refl xmax leqv

Seg>0 : (xmax : b ≡ b) → Set1
Seg>0 xmax = Seg≠ refl xmax leqv


seg-refl : Seg≥0 refl
D seg-refl x = x ≡ refl
dmin seg-refl = refl
dmax seg-refl = refl
as seg-refl n e _ = n e
R seg-refl _ _ = ⊥
-- rp seg-refl ()
rd seg-refl n = n (λ ())
-- ir seg-refl ()
-- tr seg-refl ()
tc seg-refl e1 e2 = inr (inl (λ k → k (e1 ◾ ! e2)))
mn seg-refl e1 n = n (! e1)
mx seg-refl e1 n = n (! e1)
gn seg-refl e1 e2 = l-neq-refl (g rwhisk-eqv (e2 ◾ ! e1 ◾ ! ◾unitl))
--  ds seg-refl ()
f (up seg-refl) (_ , ())
g (up seg-refl) (_ , ())
η (up seg-refl) (_ , ())
h (up seg-refl) = g (up seg-refl)
ε (up seg-refl) (_ , ())

module Seg0Eqv (x : b ≡ b) where
  open Seg=
  open PresegEqData

  f-seg0-eqv : Seg-0 x → Seg+0 x
  D (f-seg0-eqv s) = D s
  dmin (f-seg0-eqv s) = dmax s
  dmax (f-seg0-eqv s) = dmin s
  as (f-seg0-eqv s) = as s
  R (f-seg0-eqv s) = R s
  rp (f-seg0-eqv s) = rp s
  rd (f-seg0-eqv s) = rd s
  ir (f-seg0-eqv s) = ir s
  tr (f-seg0-eqv s) = tr s
  tc (f-seg0-eqv s) = tc s
  mn (f-seg0-eqv s) d1 n1 = rec⊥ (R-⊥ s (mx s d1 n1))
  mx (f-seg0-eqv s) d1 n1 = rec⊥ (R-⊥ s (mn s d1 n1))
  gn (f-seg0-eqv s) = gn s
  ds (f-seg0-eqv s) = ds s
  
  f (up (f-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  g (up (f-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  η (up (f-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  h (up (f-seg0-eqv s))         = g (up (f-seg0-eqv s))
  ε (up (f-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  
  nr (f-seg0-eqv s) = R-⊥ s

  g-seg0-eqv : Seg+0 x → Seg-0 x
  D (g-seg0-eqv s) = D s
  dmin (g-seg0-eqv s) = dmax s
  dmax (g-seg0-eqv s) = dmin s
  as (g-seg0-eqv s) = as s
  R (g-seg0-eqv s) = R s
  rp (g-seg0-eqv s) = rp s
  rd (g-seg0-eqv s) = rd s
  ir (g-seg0-eqv s) = ir s
  tr (g-seg0-eqv s) = tr s
  tc (g-seg0-eqv s) = tc s
  mn (g-seg0-eqv s) d1 n1 = rec⊥ (R-⊥ s (mx s d1 n1))
  mx (g-seg0-eqv s) d1 n1 = rec⊥ (R-⊥ s (mn s d1 n1))
  gn (g-seg0-eqv s) = gn s
  ds (g-seg0-eqv s) = ds s

  f (up (g-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  g (up (g-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  η (up (g-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)
  h (up (g-seg0-eqv s))         = g (up (g-seg0-eqv s))
  ε (up (g-seg0-eqv s)) (d , r) = rec⊥ (R-⊥ s r)

  nr (g-seg0-eqv s) = R-⊥ s

  η-seg0-eqv : (s : Seg-0 x) → g-seg0-eqv (f-seg0-eqv s) ≡ s
  η-seg0-eqv s = seg=-eq p where
    p : PresegEqData x refl fl
          (record { Seg= (g-seg0-eqv (f-seg0-eqv s)) })
          (record { Seg= s })
    Deq p x = ide (D s x)
    Deq' p = _
    Deqcoh p = refl
    dmineq p = refl
    dmineq' p = _
    dmineqcoh p = refl
    dmaxeq p = refl
    dmaxeq' p = _
    dmaxeqcoh p = refl
    Req p = id , id
    Req' p = _
    Reqcoh p = refl
    rpeq' p = rel-is-prop-eq (Deq p) (Deqcoh p) (Req p) (Reqcoh p)
    upeq p d r _ = rec⊥ (R-⊥ s r)
  
  ε-seg0-eqv : (s : Seg+0 x) → f-seg0-eqv (g-seg0-eqv s) ≡ s
  ε-seg0-eqv s = seg=-eq p where
    p : PresegEqData refl x fl
          (record { Seg= (f-seg0-eqv (g-seg0-eqv s)) })
          (record { Seg= s })
    Deq p x = ide (D s x)
    Deq' p = _
    Deqcoh p = refl
    dmineq p = refl
    dmineq' p = _
    dmineqcoh p = refl
    dmaxeq p = refl
    dmaxeq' p = _
    dmaxeqcoh p = refl
    Req p = id , id
    Req' p = _
    Reqcoh p = refl
    rpeq' p = rel-is-prop-eq (Deq p) (Deqcoh p) (Req p) (Reqcoh p)
    upeq p d r _ = rec⊥ (R-⊥ s r)

  seg0-eqv : Seg-0 x ≃ Seg+0 x
  f seg0-eqv = f-seg0-eqv
  g seg0-eqv = g-seg0-eqv
  η seg0-eqv = η-seg0-eqv
  h seg0-eqv = g-seg0-eqv
  ε seg0-eqv = ε-seg0-eqv

open Seg0Eqv using (seg0-eqv) public



module _ (x : b ≡ b) where
  shift-seg≥0 : (Seg+0 x ⊎ Seg>0 x) ≃ Seg≥0 x
  shift-seg≥0 = eqv
    module shift-seg≥0 where
    f-eqv : (Seg+0 x ⊎ Seg>0 x) → Seg≥0 x
    f-eqv (inl s) = record { Seg= s }
    f-eqv (inr s) = record { Seg≠ s }

    g-eqv : (s : Seg≥0 x) →
            R s (dmin s) (dmax s) ⊎ (refl ≐ x) →
            (Seg+0 x ⊎ Seg>0 x)
    g-eqv s (inl r) = inr record { Seg s ; r0 = r }
    g-eqv s (inr e) = inl record { Seg s ; nr = (λ r → Seg.stnn s r e) }

    η-eqv-l : (s : Seg+0 x) →
              (a : R s (dmin s) (dmax s) ⊎ (refl ≐ x)) →
              g-eqv (f-eqv (inl s)) a ≡ inl s
    η-eqv-l s (inl r) = rec⊥ (nr s r)
    η-eqv-l s (inr e) =
      ap (λ n → inl (record { Seg= s hiding (nr) ; nr = n }))
         (is-prop-pi (λ _ ()) _ _)

    η-eqv-r : (s : Seg>0 x) →
              (a1 : R (f-eqv (inr s)) (dmin s) (dmax s) ⊎ (refl ≐ x)) →
              g-eqv (f-eqv (inr s)) a1 ≡ inr s
    η-eqv-r s (inl r) =
      ap (λ r0 → inr (record { Seg≠ s hiding (r0) ; r0 = r0}))
         (rp s r (r0 s))
    η-eqv-r s (inr e) = rec⊥ (Seg≠.stnn s (r0 s) e)

    ε-eqv : (s : Seg≥0 x) → (a : R s (dmin s) (dmax s) ⊎ (refl ≐ x)) →
            f-eqv (g-eqv s a) ≡ s
    ε-eqv s (inl r) = refl
    ε-eqv s (inr e) = refl

    eqv : (Seg+0 x ⊎ Seg>0 x) ≃ Seg≥0 x
    f eqv = f-eqv
    g eqv s = g-eqv s (Seg.dimx s (dmin s))
    η eqv (inl s) = η-eqv-l s (Seg.dimx (f-eqv (inl s)) (dmin s))
    η eqv (inr s) = η-eqv-r s (Seg≠.dimx s (dmin s))
    h eqv = g eqv
    ε eqv s = ε-eqv s (Seg.dimx s (dmin s))


module _ (x : b ≡ b) where
  shift-seg≤0 : (Seg<0 x ⊎ Seg-0 x) ≃ Seg≤0 x
  shift-seg≤0 = eqv
    module shift-seg≤0 where
    f-eqv : Seg<0 x ⊎ Seg-0 x → Seg≤0 x
    f-eqv (inl s) = record { Seg≠ s }
    f-eqv (inr s) = record { Seg= s }

    g-eqv : (s : Seg≤0 x) → R s (dmin s) (dmax s) ⊎ (x ≐ refl) → Seg<0 x ⊎ Seg-0 x
    g-eqv s (inl r) = inl (record { Seg s ; r0 = r })
    g-eqv s (inr e) = inr (record { Seg s ; nr = λ r → Seg.stnn s r e})

    η-eqv-l : (s : Seg<0 x) → (a : R (f-eqv (inl s)) (dmin (f-eqv (inl s)))
                             (dmax (f-eqv (inl s))) ⊎ (x ≐ refl)) →
               g-eqv (f-eqv (inl s)) a ≡ inl s
    η-eqv-l s (inl r) =
      ap (λ r → inl (record { Seg≠ s hiding (r0) ; r0 = r})) (rp s _ _)
    η-eqv-l s (inr e) = rec⊥ (Seg≠.stnn s (r0 s) e)

    η-eqv-r : (s : Seg-0 x) →
              (a : R (f-eqv (inr s)) (dmin (f-eqv (inr s))) (dmax (f-eqv (inr s))) ⊎
                   (x ≐ refl)) → g-eqv (f-eqv (inr s)) a ≡ inr s
    η-eqv-r s (inl r) = rec⊥ (nr s r)
    η-eqv-r s (inr e) =
      ap (λ r → inr (record { Seg= s hiding (nr) ; nr = r})) 
         (is-prop-pi (λ _ ()) _ _)
         
    ε-eqv : (s : Seg≤0 x) → (a : R s (dmin s) (dmax s) ⊎ (x ≐ refl)) →
            f-eqv (g-eqv s a) ≡ s
    ε-eqv s (inl r) = refl
    ε-eqv s (inr e) = refl

    eqv : (Seg<0 x ⊎ Seg-0 x) ≃ Seg≤0 x
    f eqv = f-eqv
    g eqv s = g-eqv s (Seg.dimx s (dmin s))
    η eqv (inl s) = η-eqv-l s (Seg.dimx (f-eqv (inl s)) (dmin (f-eqv (inl s))))
    η eqv (inr s) = η-eqv-r s (Seg.dimx (f-eqv (inr s)) (dmin (f-eqv (inr s))))
    h eqv = g eqv
    ε eqv s = ε-eqv s (Seg.dimx s (dmin s))
