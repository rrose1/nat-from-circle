{-# OPTIONS --without-K --no-import-sorts #-}
module UTT where

open import Agda.Primitive renaming (Set to Type) public


variable
  l1 l2 l3 l4 l5 l6 : Level


infixr 4 _,_
record Σ (X : Type l1) (P : X -> Type l2) : Type (l1 ⊔ l2) where
  constructor _,_
  field
    fst : X
    snd : P fst
open Σ public

infixr 6 _×_
_×_ : (X : Type l1) -> (Y : Type l2) -> Type (l1 ⊔ l2)
X × Y = Σ X (λ _ -> Y)

data ⊥ {l1} : Type l1 where

module _ {Y : Type l2} where
  rec⊥ : ⊥ {l1} -> Y
  rec⊥ ()

module _ {l1} where
  infix 10 ¬
  ¬ : Type l1 -> Type l1
  ¬ X = X -> ⊥ {l1}

module _ {l1} where
  nn : Type l1 -> Type l1
  nn X = ¬ (¬ X)

module _ {X Y : Type l1} where
  nn-map : (X -> Y) -> nn X -> nn Y
  nn-map f X k = X (λ x -> k (f x))

data ⊤ : Type where
  tt : ⊤

infixr 5 _⊎_
data _⊎_ {l1 l2} (X : Type l1) (Y : Type l2) : Type (l1 ⊔ l2) where
  inl : X -> X ⊎ Y
  inr : Y -> X ⊎ Y

infix 4 _≡_
data _≡_ {X : Type l1} (x : X) : X -> Type l1 where
  refl : x ≡ x

module _ {X : Type l1} where
  infix 4 _≢_
  _≢_ : X -> X -> Type l1
  x ≢ x' = ¬ (x ≡ x')

  infix 4 _≐_
  _≐_ : X -> X -> Type l1
  _≐_ x1 x2 = nn (x1 ≡ x2)

infix 4 _≃_
record _≃_ (X : Type l1) (Y : Type l2) : Type (l1 ⊔ l2) where
  constructor biinv
  field
    f : X -> Y
    g : Y -> X
    η : (x : X) -> g (f x) ≡ x
    h : Y -> X
    ε : (y : Y) -> f (h y) ≡ y
open _≃_ public

record Retraction (X : Type l1) (Y : Type l2) : Type (l1 ⊔ l2) where
  constructor retr
  field
    f : X -> Y
    g : Y -> X
    ε : (y : Y) -> f (g y) ≡ y

module _ {X : Type l1} {Y : Type l2} (f : X -> Y) where
  ap : {x1 x2 : X} -> x1 ≡ x2 -> f x1 ≡ f x2
  ap refl = refl

module _ {X : Type l1} where
  infix 10 !
  ! : {x1 x2 : X} -> x1 ≡ x2 -> x2 ≡ x1
  ! refl = refl

  !-eqv : {x1 x2 : X} -> (x1 ≡ x2) ≃ (x2 ≡ x1)
  f !-eqv = !
  g !-eqv = !
  η !-eqv refl = refl
  h !-eqv = g !-eqv
  ε !-eqv = η !-eqv

  !! : {x1 x2 : X} -> {e : x1 ≡ x2} -> ! (! e) ≡ e
  !! {e = e} = η !-eqv e

module _ {X : Type l1} (P : X -> Type l2) where
  tpt : {x1 x2 : X} -> (e : x1 ≡ x2) -> P x1 -> P x2
  tpt refl p = p

  tpt-eqv : {x1 x2 : X} -> (e : x1 ≡ x2) -> P x1 ≃ P x2
  f (tpt-eqv e)      = tpt e
  g (tpt-eqv e)      = tpt (! e)
  η (tpt-eqv refl) p = refl
  h (tpt-eqv e)      = g (tpt-eqv e)
  ε (tpt-eqv refl) p = refl


module _ {X Y : Type l1} where
  postulate
    ua : X ≃ Y -> X ≡ Y
    ua-tpt-eqv-id : (e1 : X ≡ Y) -> ua (tpt-eqv (λ X -> X) e1) ≡ e1
    tpt-eqv-id-ua : (e1 : X ≃ Y) -> tpt-eqv (λ X -> X) (ua e1) ≡ e1
    
  tpt-id-eqv : (X ≡ Y) ≃ (X ≃ Y)
  f tpt-id-eqv = tpt-eqv (λ X -> X)
  g tpt-id-eqv = ua
  η tpt-id-eqv = ua-tpt-eqv-id
  h tpt-id-eqv = g tpt-id-eqv
  ε tpt-id-eqv = tpt-eqv-id-ua

  module _ (e1 : X ≃ Y) where
    tpt-id-ua : tpt (λ X -> X) (ua e1) ≡ f e1
    tpt-id-ua = ap f (tpt-eqv-id-ua e1)
  
    tpt-id-!-ua : tpt (λ X -> X) (! (ua e1)) ≡ g e1
    tpt-id-!-ua = ap g (tpt-eqv-id-ua e1)

module _ {X : Type l1} (P : X -> Type l2) (f : (x : X) -> P x) where
  apd : {x1 x2 : X} -> (e : x1 ≡ x2) -> tpt P e (f x1) ≡ f x2
  apd refl = refl

module _ {X : Type l1} where
  infixr 8 _•_
  _•_ : {x1 x2 : X} -> x1 ≡ x2 -> {x3 : X} -> x2 ≡ x3 -> x1 ≡ x3
  refl • refl = refl

  •unitr : {x1 x2 : X} -> {e : x1 ≡ x2} -> e • refl ≡ e
  •unitr {e = refl} = refl

  •unitl : {x1 x2 : X} -> {e : x1 ≡ x2} -> refl • e ≡ e
  •unitl {e = refl} = refl

  •assoc : {w x x2 x3 : X} -> {p : w ≡ x} -> {q : x ≡ x2} -> {r : x2 ≡ x3}
           -> (p • q) • r ≡ p • q • r
  •assoc {p = refl} {refl} {refl} = refl

  •invl : {x1 x2 : X} -> {e : x1 ≡ x2} -> ! e • e ≡ refl
  •invl {e = refl} = refl

  •invr : {x1 x2 : X} -> {e : x1 ≡ x2} -> e • ! e ≡ refl
  •invr {e = refl} = refl

  !-comp : {x y z : X} -> {p : x ≡ y} -> {q : y ≡ z} -> ! (p • q) ≡ ! q • ! p
  !-comp {p = refl} {refl} = refl

module _ {X : Type l1} {Y : Type l2} (Q : X -> Y -> Type l3) where
  tpt2-cart : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> {y1 y2 : Y} -> (e2 : y1 ≡ y2) ->
              Q x1 y1 -> Q x2 y2
  tpt2-cart refl refl q = q
  
  tpt2-cart-eqv : {x1 x2 : X} -> (e1 : x1 ≡ x2) ->
                  {y1 y2 : Y} -> (e2 : y1 ≡ y2) ->
                  Q x1 y1 ≃ Q x2 y2
  f (tpt2-cart-eqv e1 e2)       = tpt2-cart e1 e2
  g (tpt2-cart-eqv e1 e2)       = f (tpt2-cart-eqv (! e1) (! e2))
  η (tpt2-cart-eqv refl refl) q = refl
  h (tpt2-cart-eqv e1 e2)       = g (tpt2-cart-eqv e1 e2)
  ε (tpt2-cart-eqv refl refl) q = refl

module _ {X : Type l1} {P : X -> Type l2} (Q : (x : X) -> P x -> Type l3) where
  tpt2 : {x1 x2 : X} -> (e1 : x1 ≡ x2) ->
         {p1 : P x1} -> {p2 : P x2} -> (e2 : tpt P e1 p1 ≡ p2) ->
         Q x1 p1 -> Q x2 p2
  tpt2 refl refl q = q
  
  tpt2-eqv : {x1 x2 : X} -> (e1 : x1 ≡ x2) ->
             {p1 : P x1} -> {p2 : P x2} -> (e2 : tpt P e1 p1 ≡ p2) ->
             Q x1 p1 ≃ Q x2 p2
  f (tpt2-eqv e1 e2)       = tpt2 e1 e2
  g (tpt2-eqv refl refl) q = q
  η (tpt2-eqv refl refl) q = refl
  h (tpt2-eqv e1 e2)       = g (tpt2-eqv e1 e2)
  ε (tpt2-eqv refl refl) q = refl

module _ {X : Type l1} where
  lcomp-eqv : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> {x3 : X} -> (x2 ≡ x3) ≃ (x1 ≡ x3)
  f (lcomp-eqv e1) e2 = e1 • e2
  g (lcomp-eqv e1) e2 = ! e1 • e2
  η (lcomp-eqv refl) refl = refl
  h (lcomp-eqv e1)     = g (lcomp-eqv e1)
  ε (lcomp-eqv refl) refl = refl

  lwhisk-coh : {x1 x2 : X} -> {e1 e2 : x1 ≡ x2} -> (e4 : e1 ≡ e2) ->
         ap (λ e2 -> refl • e2) e4 ≡
         f (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitl) (! •unitl)) e4
  lwhisk-coh {e1 = refl} refl = refl

  lwhisk-eqv : {x1 x2 : X} -> {e1 : x1 ≡ x2} ->
               {x3 : X} -> {e2 e3 : x2 ≡ x3} ->
               (e2 ≡ e3) ≃ (e1 • e2 ≡ e1 • e3)
  f (lwhisk-eqv {e1 = e1}) = ap (f (lcomp-eqv e1))
  g (lwhisk-eqv {e1 = refl}) =
    g (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitl) (! •unitl))
  η (lwhisk-eqv {e1 = refl}) e4 =
    ap (f (tpt2-cart-eqv _≡_ (! (! •unitl)) (! (! •unitl)))) (lwhisk-coh e4) •
    η (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitl) (! •unitl)) e4
  h lwhisk-eqv               = g (lwhisk-eqv)
  ε (lwhisk-eqv {e1 = refl}) e4 =
    lwhisk-coh (f (tpt2-cart-eqv _≡_ (! (! •unitl)) (! (! •unitl))) e4) •
    ε (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitl) (! •unitl)) e4

  infixr 8 _[1,0,2]_
  _[1,0,2]_ : {x1 x2 x3 : X} ->
              (e1 : x1 ≡ x2) ->
              {e2 e3 : x2 ≡ x3} -> e2 ≡ e3 ->
              e1 • e2 ≡ e1 • e3
  _[1,0,2]_ e1 = f (lwhisk-eqv {e1 = e1})

  rcomp-eqv : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> {x3 : X} -> (x3 ≡ x1) ≃ (x3 ≡ x2)
  f (rcomp-eqv e1) e2 = e2 • e1
  g (rcomp-eqv e1) e2 = e2 • ! e1
  η (rcomp-eqv refl) refl = refl
  h (rcomp-eqv e1)      = g (rcomp-eqv e1)
  ε (rcomp-eqv refl) refl = refl

  rwhisk-coh : {x1 x2 : X} -> {e1 e2 : x1 ≡ x2} -> (e4 : e1 ≡ e2) ->
               ap (λ e2 -> e2 • refl) e4 ≡
               f (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitr) (! •unitr)) e4
  rwhisk-coh {e1 = refl} refl = refl

  rwhisk-eqv : {x1 x2 : X} -> {e1 : x1 ≡ x2} ->
               {x3 : X} -> {e2 e3 : x3 ≡ x1} ->
               (e2 ≡ e3) ≃ (e2 • e1 ≡ e3 • e1)
  f (rwhisk-eqv {e1 = e1}) = ap (f (rcomp-eqv e1))  
  g (rwhisk-eqv {e1 = refl}) =
    g (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitr) (! •unitr))
  η (rwhisk-eqv {e1 = refl}) e4 =
    ap (f (tpt2-cart-eqv _≡_ (! (! •unitr)) (! (! •unitr)))) (rwhisk-coh e4) •
    η (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitr) (! •unitr)) e4
  h rwhisk-eqv               = g (rwhisk-eqv)
  ε (rwhisk-eqv {e1 = refl}) e4 =
    rwhisk-coh (f (tpt2-cart-eqv _≡_ (! (! •unitr)) (! (! •unitr))) e4) •
    ε (tpt2-cart-eqv (λ x1 x2 -> x1 ≡ x2) (! •unitr) (! •unitr)) e4

  infixr 8 _[2,0,1]_
  _[2,0,1]_ : {x1 x2 x3 : X} ->
              {e1 e2 : x1 ≡ x2} -> e1 ≡ e2 ->
              (e3 : x2 ≡ x3) ->
              e1 • e3 ≡ e2 • e3
  _[2,0,1]_ e4 e3 = f (rwhisk-eqv {e1 = e3}) e4

  infixr 8 _[2,0,2]_
  _[2,0,2]_ : {x1 x2 x3 : X} ->
              {e1 e2 : x1 ≡ x2} -> e1 ≡ e2 ->
              {e3 e4 : x2 ≡ x3} -> e3 ≡ e4 ->
              e1 • e3 ≡ e2 • e4
  _[2,0,2]_ e5 e6 = (e5 [2,0,1] _) • (_ [1,0,2] e6)

module _ {X : Type l1} {Y : Type l2} {Z : Type l3}
         (g : Y -> Z) (f : X -> Y) where
  ap-fn-comp : {x x2 : X} -> (p : x ≡ x2) -> ap (λ x -> g (f x)) p ≡ ap g (ap f p)
  ap-fn-comp {x} {x2} refl = refl

module _ {X : Type l1} where
  ap-id : {x y : X} -> (p : x ≡ y) -> ap (λ x -> x) p ≡ p
  ap-id refl = refl

module _ {X : Type l1} {Y : Type l2} where
  ap-! : {x y : X} -> (f : X -> Y) -> (p : x ≡ y) -> ap f (! p) ≡ ! (ap f p)
  ap-! f refl = refl

module _ {X : Type l1} {Y : Type l2} {f : X -> Y} where
  ap-comp : {x x2 x2' : X} -> (p : x ≡ x2) -> (q : x2 ≡ x2') ->
            ap f (p • q) ≡ ap f p • ap f q
  ap-comp refl refl = refl

  ap-comp3 : {x1 x2 x3 x4 : X} ->
             (e1 : x1 ≡ x2) -> (e2 : x1 ≡ x3) -> (e3 : x3 ≡ x4) ->
             ap f (! e1 • e2 • e3) ≡ ! (ap f e1) • ap f e2 • ap f e3
  ap-comp3 refl refl refl = refl

module _ {X : Type l1} {Y : Type l2} where
  tpt-const : {x1 x2 : X} -> (e : x1 ≡ x2) ->
              (y : Y) -> tpt (λ _ -> Y) e y ≡ y
  tpt-const refl y = refl

module _ {X : Type l1} {Y : Type l2} (f : X -> Y) where
  tpt-fn-eq-const : (y : Y) ->
                    {x1 x2 : X} -> (e1 : x1 ≡ x2) -> (e2 : f x1 ≡ y) ->
                    tpt (λ x -> f x ≡ y) e1 e2 ≡ ! (ap f e1) • e2
  tpt-fn-eq-const _ refl refl = refl

  tpt-const-eq-fn : (y : Y) ->
                    {x1 x2 : X} -> (e1 : x1 ≡ x2) -> (e2 : y ≡ f x1) ->
                    tpt (λ x -> y ≡ f x) e1 e2 ≡ e2 • ap f e1
  tpt-const-eq-fn y refl refl = refl

module _ {X : Type l1} {Y : Type l2} (f g : X -> Y) where
  tpt-fn-eq-fn : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> (e2 : f x1 ≡ g x1) ->
                 tpt (λ x -> f x ≡ g x) e1 e2 ≡ ! (ap f e1) • e2 • ap g e1
  tpt-fn-eq-fn refl e2 = ! •unitr • ! •unitl

module _ {X : Type l1} {x0 : X} where
  tpt-const-eq-var : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> (e2 : x0 ≡ x1) ->
                     tpt (λ x -> x0 ≡ x) e1 e2 ≡ e2 • e1
  tpt-const-eq-var refl refl = refl

  tpt-var-eq-const : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> (e2 : x1 ≡ x0) ->
                     tpt (λ x -> x ≡ x0) e1 e2 ≡ ! e1 • e2
  tpt-var-eq-const refl refl = refl

module _ {X : Type l1} {P : X -> Type l2} {Q : X -> Type l3} where
  tpt-fn : {x1 x2 : X} -> (e : x1 ≡ x2) ->
           (f : P x1 -> Q x1) -> (p : P x2) ->
           tpt (λ x -> P x -> Q x) e f p ≡ tpt Q e (f (tpt P (! e) p))
  tpt-fn refl f p = refl

module _ {X : Type l1} (P : X -> Type l2) where
  tpt-comp : {x1 x2 x3 : X} -> (e1 : x1 ≡ x2) -> (e2 : x2 ≡ x3) ->
             {p : P x1} -> tpt P (e1 • e2) p ≡ tpt P e2 (tpt P e1 p)
  tpt-comp refl refl = refl

module _ {X : Type l1} {Y : Type l2} {f : X -> Y} (P : Y -> Type l3) where
  tpt-fn-comp : {x1 x2 : X} -> (e : x1 ≡ x2) ->
                (p : P (f x1)) -> tpt (λ x -> P (f x)) e p ≡ tpt P (ap f e) p
  tpt-fn-comp refl p = refl

module _ where
  is-prop : Type l1 -> Type l1
  is-prop X = (x x2 : X) -> x ≡ x2

  is-set : Type l1 -> Type l1
  is-set X = {x x2 : X} -> (p q : x ≡ x2) -> p ≡ q

module _ where
  prop-is-set : {X : Type l1} -> is-prop X -> is-set X
  prop-is-set ϕ {x1} {x2} e1 e2 =
    g lwhisk-eqv
      (! (tpt-const-eq-var e1 (ϕ x1 x1)) •
       apd _ (ϕ x1) e1 •
       ! (apd _ (ϕ x1) e2)
       • tpt-const-eq-var e2 (ϕ x1 x1))

⊤-is-prop : is-prop ⊤
⊤-is-prop tt tt = refl

module _ {X : Type l1} {Y : Type l2}
         {f : X -> Y} {g : Y -> X}
         (η : (x : X) -> g (f x) ≡ x)
         where
  inv-sq : {x1 x2 : X} -> (e1 : x1 ≡ x2) ->
           ! (η x1) • ap g (ap f e1) • η x2 ≡ e1
  inv-sq {x1} = coh2
    module inv-sq where
    coh1 : {x1 x2 : X} -> (e : x1 ≡ x2) -> ! e • refl • e ≡ refl
    coh1 refl = refl

    coh2 = λ { refl -> coh1 (η _) }

  inv-comm : (x : X) -> ap g (ap f (η x)) ≡ η (g (f x))
  inv-comm x1 = _≃_.g rwhisk-eqv (coh (η x1))
    module inv-comm where
    coh : {x1 x2 : X} -> (e1 : x1 ≡ x2) -> ap g (ap f e1) • η x2 ≡ η x1 • e1
    coh refl = •unitl • ! •unitr

module _ {X : Type l1} {Y : Type l2}
         (f : X -> Y) (g : Y -> X)
         (η : (x : X) -> g (f x) ≡ x)
         where
  ap-sect-eq : {x1 x2 : X} -> {e1 e2 : x1 ≡ x2} ->
               ap f e1 ≡ ap f e2 -> e1 ≡ e2
  ap-sect-eq {x1} {x2} {e1} {e2} α =
    ! (inv-sq η e1) •
    (! (η x1) [1,0,2] ap (ap g) α [2,0,1] (η x2)) •
    inv-sq η e2

module _ {X : Type l1} {Y : Type l2}
         (f : X -> Y) (g : Y -> X)
         (ε : (y : Y) -> f (g y) ≡ y)
         where
  ap-retr-eq : {y1 y2 : Y} -> {e1 e2 : y1 ≡ y2} ->
               ap g e1 ≡ ap g e2 -> e1 ≡ e2
  ap-retr-eq {y1} {y2} {e1} {e2} α =
    ! (inv-sq ε e1) •
    (! (ε y1) [1,0,2] ap (ap f) α [2,0,1] (ε y2)) •
    inv-sq ε e2

module _ {X : Type l1} {Y : Type l2}
         (f : X -> Y) (g : Y -> X)
         (η : (x : X) -> g (f x) ≡ x)
         (ε : (y : Y) -> f (g y) ≡ y)
         where
  ap-qinv-sq : {x1 x2 : X} -> (e1 : f x1 ≡ f x2) ->
               ap f (! (η x1) • ap g e1 • η x2) ≡ e1
  ap-qinv-sq {x1} {x2} e1 = ap-retr-eq f g ε (coh e1)
    module ap-qinv-sq where
    coh : {x1 x2 : X} -> (e1 : f x1 ≡ f x2) ->
            ap g (ap f (! (η x1) • ap g e1 • η x2)) ≡ ap g e1
    coh {x1} {x2} e1 =
      ap (ap g) (ap-comp3 (η x1) (ap g e1) (η x2)) •
      ap-comp3 (ap f (η x1)) (ap f (ap g e1)) (ap f (η x2)) •
      (ap ! (inv-comm η x1) [2,0,2] ap g (ap f (ap g e1)) [1,0,2] inv-comm η x2) •
      inv-sq η (ap g e1)

  ap-qinv-sq' : {x1 x2 : X} -> (e1 : f x1 ≡ f x2) ->
                ap f (η x2) ≡ ! (ap (λ y -> f (g y)) e1) • ap f (η x1) • e1
  ap-qinv-sq' {x1} {x2} e1 = aux e1 (! (η x1) • ap g e1 • η x2) (ap-qinv-sq e1)
    module ap-qinv-sq' where
    aux :  {x1 x2 : X} -> (e1 : f x1 ≡ f x2) -> (e2 : x1 ≡ x2) -> ap f e2 ≡ e1 ->
           ap f (η x2) ≡ ! (ap (λ y -> f (g y)) e1) • ap f (η x1) • e1
    aux e2 refl refl = ! •unitr • ! •unitl

module _ {X : Type l1} {Y : Type l2} (e : X ≃ Y) where
  ε' : (y : Y) -> f e (g e y) ≡ y
  ε' y = ! (ap (λ y -> f e (g e y)) (ε e y)) • ap (f e) (η e (h e y)) • ε e y

  η' : (x : X) -> h e (f e x) ≡ x
  η' x = ! (η e (h e (f e x))) • ap (g e) (ε e (f e x)) • η e x

  τ : (x : X) -> ap (f e) (η' x) ≡ ε e (f e x)
  τ x = ap-qinv-sq (f e) (g e) (η e) ε' (ε e (f e x))

  τ' : (x : X) -> ap (f e) (η e x) ≡ ε' (f e x)
  τ' x = ap-qinv-sq' (f e) (g e) (η e) ε' (ε e (f e x))

  ν : (y : Y) -> ap (h e) (ε e y) ≡ η' (h e y)
  ν y = ap-sect-eq (f e) (g e) (η e) (inv-comm (ε e) y • ! (τ (h e y)))

  ν' : (y : Y) -> ap (g e) (ε' y) ≡ η e (g e y)
  ν' y = ap-sect-eq (f e) (g e) (η e) (inv-comm ε' y • ! (τ' (g e y)))


id : {X : Type l1} -> X -> X
id x = x

{- TODO : include derivation of funext from ua -}
module _ {X : Type l1} {P : X -> Type l2} {m1 m2 : (x : X) -> P x} where
  postulate
    funext : ((x : X) -> m1 x ≡ m2 x) -> m1 ≡ m2
    funext-happly : (e : m1 ≡ m2) -> funext (λ x -> ap (λ f -> f x) e) ≡ e
    happly-funext : (ϕ : ((x : X) -> m1 x ≡ m2 x)) ->
                    (λ x -> ap (λ f -> f x) (funext ϕ)) ≡ ϕ
                    
  happly-eqv : (m1 ≡ m2) ≃ ((x : X) -> m1 x ≡ m2 x)
  f happly-eqv e x = ap (λ a -> a x) e
  g happly-eqv = funext 
  η happly-eqv = funext-happly
  h happly-eqv = g happly-eqv
  ε happly-eqv = happly-funext


module _ {X : Type l1} {P : X -> Type l2} {m1 m2 : {x : X} -> P x} where
  postulate
    funext' : ({x : X} -> m1 {x} ≡ m2 {x}) -> (λ {x} -> m1 {x}) ≡ m2
    funext-happly' : (e : (λ {x} -> m1 {x}) ≡ m2) ->
                     funext' (λ {x} -> ap (λ f -> f {x}) e) ≡ e
    happly-funext' : (ϕ : ({x : X} -> m1 {x} ≡ m2 {x})) ->
                     (λ {x} -> ap (λ f -> f {x}) (funext' ϕ)) ≡ ϕ

  happly'-eqv : ((λ {x} -> m1 {x}) ≡ m2) ≃ ({x : X} -> m1 {x} ≡ m2 {x})
  f happly'-eqv e {x} = ap (λ a -> a {x}) e 
  g happly'-eqv = funext'
  η happly'-eqv = funext-happly'
  h happly'-eqv = g happly'-eqv
  ε happly'-eqv = happly-funext'


module _ {X : Type l1} {P : X -> Type l2} where
  is-prop-pi : ((x : X) -> is-prop (P x)) -> is-prop ((x : X) -> P x)
  is-prop-pi ϕ m1 m2 = funext (λ x -> ϕ x (m1 x) (m2 x))

  is-prop-pi' : ({x : X} -> is-prop (P x)) -> is-prop ({x : X} -> P x)
  is-prop-pi' ϕ m1 m2 = funext' (λ {x} -> ϕ {x} (m1 {x}) (m2 {x}))


module _ (X : Type l1) where
  is-prop-is-prop : is-prop (is-prop X)
  is-prop-is-prop ϕ ϕ' =
    funext (λ x ->
    funext (λ x' ->
      prop-is-set ϕ (ϕ x x') (ϕ' x x')))


module _ {X : Type l1} {Y : Type l2} (e : X ≃ Y) where
  pi-eqv-1 : {Z : Type l3} -> (Y -> Z) ≃ (X -> Z)
  f pi-eqv-1 k x = k (f e x)
  g pi-eqv-1 k y = k (g e y)
  η pi-eqv-1 k = funext (λ y -> ap k (ε' e y))
  h pi-eqv-1 = g pi-eqv-1
  ε pi-eqv-1 k = funext (λ x -> ap k (η e x))

  neg-eqv = pi-eqv-1 {Z = ⊥ {l1 ⊔ l2}}

  pi-eqv-1' : {P : Y -> Type l3} -> ((x : X) -> P (f e x)) ≃ ((y : Y) -> P y)
  f (pi-eqv-1' {P = P}) k y = tpt P (ε e y) (k (h e y))
  g (pi-eqv-1' {P = P}) k x = k (f e x)
  η (pi-eqv-1' {P = P}) k =
    funext (λ x ->
      ap (λ e1 -> tpt P e1 (k (h e (f e x))))
         (! (τ e x)) •
      ! (tpt-fn-comp P (η' e x) (k (h e (f e x)))) •
      apd (λ x -> P (f e x)) k (η' e x))
  h (pi-eqv-1' {P = P}) = g (pi-eqv-1' {P = P})
  ε (pi-eqv-1' {P = P}) k = funext (λ y -> apd P k (ε e y))


module _ {X : Type l1}
         {P : X -> Type l2} {Q : X -> Type l3}
         (ϕ : (x : X) -> (P x) ≃ (Q x)) where
  pi-eqv-2 : ((x : X) -> P x) ≃ ((x : X) -> Q x)
  f pi-eqv-2 f1 x1 = f (ϕ x1) (f1 x1) 
  g pi-eqv-2 f1 x1 = g (ϕ x1) (f1 x1)
  η pi-eqv-2 f1    = funext (λ x1 -> η (ϕ x1) (f1 x1))
  h pi-eqv-2 f1 x1 = h (ϕ x1) (f1 x1)
  ε pi-eqv-2 f1    = funext (λ x1 -> ε (ϕ x1) (f1 x1))


module _ {X : Type l1} {P : X -> Type l2} where
  ap-snd : {x1 x2 : X} -> {p1 : P x1} -> {p2 : P x2} ->
           (e : _≡_ {X = Σ X P} (x1 , p1) (x2 , p2)) ->
           tpt P (ap fst e) p1 ≡ p2
  ap-snd refl = refl


module _ {X : Type l1} {P : X -> Type l2} where
  pair-eq : {x1 x2 : X} -> {p1 : P x1} -> {p2 : P x2} ->
            (Σ (x1 ≡ x2) (λ p -> tpt P p p1 ≡ p2)) ->
            ((x1 , p1) ≡ (x2 , p2))
  pair-eq (refl , refl) = refl

  pair-eqv : {x1 x2 : X} -> {p1 : P x1} -> {p2 : P x2} ->
             (Σ (x1 ≡ x2) (λ p -> tpt P p p1 ≡ p2)) ≃
             ((x1 , p1) ≡ (x2 , p2))
  f pair-eqv                = pair-eq
  g pair-eqv e1             = ap fst e1 , ap-snd e1
  η pair-eqv (refl , refl)  = refl
  h pair-eqv                = g pair-eqv
  ε pair-eqv refl           = refl


module _ {X : Type l1} {P : X -> Type l2}
         {Y : Type l3} {Q : Y -> Type l4} (ψ : {y : Y} -> is-prop (Q y))
         (e : Σ X P ≃ Σ Y Q)
         where
  ηs : (x : X) -> (p : P x) -> (q : Q (fst (f e (x , p)))) ->
       fst (g e (fst (f e (x , p)) , q)) ≡ x
  ηs x p q = ap (λ y -> fst (g e y)) (pair-eq (refl , (ψ _ _))) •
             ap fst (η e (x , p))

module _ {X : Type l1} {P : X -> Type l2} (ϕ : {x : X} -> is-prop (P x))
         {Y : Type l3} {Q : Y -> Type l4}
         (e : Σ X P ≃ Σ Y Q)
         where
  εs : (y : Y) -> (q : Q y) -> (p : P (fst (g e (y , q)))) ->
       fst (f e (fst (g e (y , q)) , p)) ≡ y
  εs y q p = ap (λ x -> fst (f e x)) (pair-eq (refl , ϕ _ _)) •
             ap fst (ε' e (y , q))

module _ {X : Type l1} {Y : Type l2} {P : Y -> Type l3} (e : X ≃ Y) where
  sigma-eqv-1 : (Σ X (λ x -> P (f e x))) ≃ (Σ Y P)
  f sigma-eqv-1 (x , p) = f e x , p
  g sigma-eqv-1 (y , p) = h e y , g (tpt-eqv P (ε e y)) p
  η sigma-eqv-1 (x , p) =
    pair-eq
      (η' e x ,
       tpt-fn-comp P (η' e x) (g (tpt-eqv P (ε e (f e x))) p) •
       ! (tpt-comp P (! (ε e (f e x))) (ap (f e) (η' e x)) {p}) •
       ap (λ e -> tpt P e p)
          ((! (ε e (f e x)) [1,0,2] τ e x) • •invl))
  h sigma-eqv-1 (y , p) = h e y , g (tpt-eqv P (ε e y)) p
  ε sigma-eqv-1 (y , p) = pair-eq (ε e y , ε (tpt-eqv P (ε e y)) p)

module _ {X : Type l1}
         {P : X -> Type l2} {Q : X -> Type l3}
         (ϕ : (x : X) -> P x ≃ Q x)
         where
  sigma-eqv-2 : (Σ X P) ≃ (Σ X Q)
  f sigma-eqv-2 (x , p) = x , f (ϕ x) p
  g sigma-eqv-2 (x , q) = x , g (ϕ x) q
  η sigma-eqv-2 (x , p) = pair-eq (refl , η (ϕ x) p)
  h sigma-eqv-2 (x , q) = x , h (ϕ x) q
  ε sigma-eqv-2 (x , q) = pair-eq (refl , ε (ϕ x) q)


module _ where
  is-contr : Type l1 -> Type l1
  is-contr X = Σ X (λ x0 -> (x : X) -> x ≡ x0)

module _ {X : Type l1} where
  contr-is-prop : is-contr X -> is-prop X
  contr-is-prop (x , ϕ) x1 x2 = ϕ x1 • ! (ϕ x2)

module _ {X : Type l1} where
  is-contr-is-contr : is-contr X -> is-contr (is-contr X)
  is-contr-is-contr (x0 , ϕ0) =
    (x0 , ϕ0) ,
    (λ {(x1 , ϕ1) -> pair-eq (ϕ0 x1 , funext (λ x2 ->
                      prop-is-set (contr-is-prop (x0 , ϕ0))
                        (tpt (λ x3 -> (x : X) -> x ≡ x3) (ϕ0 x1) ϕ1 x2) (ϕ0 x2))) })


module _ {X : Type l1} {Y : Type l2} (ϕ : is-contr Y) where
  ×unitr : X × Y ≃ X
  f ×unitr = fst
  g ×unitr x = x , fst ϕ
  η ×unitr (x , y) = ap (λ y -> (x , y)) (! (snd ϕ y))
  h ×unitr = g ×unitr
  ε ×unitr x = refl


module EqualityInCoproduct (X Y : Type l1) where
  code : X ⊎ Y -> X ⊎ Y -> Type l1
  code (inl x) (inl x') = x ≡ x'
  code (inl x) (inr y)  = ⊥
  code (inr y) (inl x)  = ⊥
  code (inr y) (inr y') = y ≡ y'

  r : (a : X ⊎ Y) -> code a a
  r (inl x) = refl
  r (inr y) = refl

  enc : (a b : X ⊎ Y) -> a ≡ b -> code a b
  enc a b p = tpt (code a) p (r a)

  dec : (a b : X ⊎ Y) -> code a b -> a ≡ b
  dec (inl x) (inl x') p = ap inl p
  dec (inl x) (inr y)  a = rec⊥ a
  dec (inr y) (inl x)  a = rec⊥ a
  dec (inr y) (inr y') p = ap inr p

module _ {X Y : Type l1} where
  open EqualityInCoproduct
  
  inl-eq : {x x' : X} -> _≡_ {X = X ⊎ Y} (inl x) (inl x') -> x ≡ x'
  inl-eq {x} {x'} = enc X Y (inl x) (inl x')

  inr-eq : {y y' : Y} -> _≡_ {X = X ⊎ Y} (inr y) (inr y') -> y ≡ y'
  inr-eq {y} {y'} = enc X Y (inr y) (inr y')

  inl-neq-inr : {x : X} -> {y : Y} -> _≡_ {X = X ⊎ Y} (inl x) (inr y) -> ⊥
  inl-neq-inr {x} {y} = enc X Y (inl x) (inr y)

module _ {i j} {X : Type i} {P Q : X -> Type j} where
  tpt-coprod-l : {x y : X} -> (p : x ≡ y) -> (px : P x)
                 -> tpt (λ x -> P x ⊎ Q x) p (inl px) ≡ inl (tpt P p px)
  tpt-coprod-l refl px = refl

  tpt-coprod-r : {x y : X} -> (p : x ≡ y) -> (qx : Q x)
                 -> tpt (λ x -> P x ⊎ Q x) p (inr qx) ≡ inr (tpt Q p qx)
  tpt-coprod-r refl qx = refl

module _ {X : Type l1} {Y : Type l2}
         (ϕ : is-prop X) (ψ : is-prop Y)
         (d : X -> Y -> ⊥ {l1 ⊔ l2}) where
  is-prop-coprod : is-prop (X ⊎ Y)
  is-prop-coprod (inl x) (inl x') = ap inl (ϕ x x')
  is-prop-coprod (inl x) (inr y) = rec⊥ (d x y)
  is-prop-coprod (inr y) (inl x) = rec⊥ (d x y)
  is-prop-coprod (inr y) (inr y') = ap inr (ψ y y')


module _ {l1} where
  is-dec : Type l1 -> Type l1
  is-dec X = X ⊎ (X -> ⊥ {l1})

  has-dec-eq : Type l1 -> Type l1
  has-dec-eq X = (x1 x2 : X) -> is-dec (x1 ≡ x2)

module _ {X : Type l1} (ϕ : has-dec-eq X) where
  has-dec-eq->is-set : is-set X
  has-dec-eq->is-set {x1} {x2} = aux _ refl
    module has-dec-eq->is-set where
    aux : (a : is-dec (x1 ≡ x1)) -> ϕ x1 x1 ≡ a -> is-prop (x1 ≡ x2)
    aux (inl e3) e4 e1 e2 =
      g lwhisk-eqv (inl-eq (ap inl (! (tpt-const-eq-var e1 e3)) •
                            ! (tpt-coprod-l e1 e3) •
                            ! (ap (tpt _ e1) e4) •
                            apd _ (ϕ x1) e1 •
                            ! (apd _ (ϕ x1) e2) •
                            ap (tpt _ e2) e4 •
                            tpt-coprod-l e2 e3 •
                            ap inl (tpt-const-eq-var e2 e3)))  
    aux (inr n) = rec⊥ (n refl)

module _ {X : Type l1} (ϕ : {x1 x2 : X} -> x1 ≐ x2 -> x1 ≡ x2) where
  stab-eq->is-set : {x1 x2 : X} -> is-prop (x1 ≡ x2)
  stab-eq->is-set {x1} {x2} e1 e2 =
    g lwhisk-eqv
      (! (coh e1 λ k -> k e1) •
      f happly-eqv (apd _ (λ x2 -> ϕ {x1} {x2}) e1) (λ k -> k e1) •
      ! (f happly-eqv (apd _ (λ x2 -> ϕ {x1} {x2}) e2) (λ k -> k e1)) •
      coh e2 (λ k -> k e1))
    module stab-eq->is-set where
    coh : {x2 : X} -> (e1 : x1 ≡ x2) -> (v : x1 ≐ x2) ->
          tpt (λ z -> x1 ≐ z -> x1 ≡ z) e1 ϕ v ≡ ϕ (λ k -> k refl) • e1
    coh refl v = ap ϕ (is-prop-pi (λ _ ()) _ _) • ! •unitr

⊎-eq : {X1 X2 : Type l1} -> X1 ≡ X2 ->
       {Y1 Y2 : Type l2} -> Y1 ≡ Y2 ->
       (X1 ⊎ Y1) ≡ (X2 ⊎ Y2)
⊎-eq refl refl = refl

module _ {X : Type l1} {Y : Type l2} (n : X -> ⊥ {l1}) where
  ⊎-unitl : (X ⊎ Y) ≃ Y
  f ⊎-unitl (inl x) = rec⊥ (n x)
  f ⊎-unitl (inr y) = y
  g ⊎-unitl         = inr
  η ⊎-unitl (inl x) = rec⊥ (n x)
  η ⊎-unitl (inr y) = refl
  h ⊎-unitl         = g ⊎-unitl
  ε ⊎-unitl _       = refl

module _ {X : Type l1} {Y : Type l2} (n : Y -> ⊥ {l2}) where
  ⊎-unitr : (X ⊎ Y) ≃ X
  f ⊎-unitr (inl x) = x
  f ⊎-unitr (inr y) = rec⊥ (n y)
  g ⊎-unitr         = inl
  η ⊎-unitr (inl x) = refl
  η ⊎-unitr (inr y) = rec⊥ (n y)
  h ⊎-unitr         = g ⊎-unitr
  ε ⊎-unitr _       = refl

module _ {X : Type l1} {Y : Type l2} {Z : Type l3} where
  ⊎-assoc : ((X ⊎ Y) ⊎ Z) ≃ (X ⊎ Y ⊎ Z)
  f ⊎-assoc (inl (inl x)) = inl x
  f ⊎-assoc (inl (inr y)) = inr (inl y)
  f ⊎-assoc (inr z) = inr (inr z)
  g ⊎-assoc (inl x) = inl (inl x)
  g ⊎-assoc (inr (inl y)) = inl (inr y)
  g ⊎-assoc (inr (inr z)) = inr z
  η ⊎-assoc (inl (inl x)) = refl
  η ⊎-assoc (inl (inr y)) = refl
  η ⊎-assoc (inr z) = refl
  h ⊎-assoc = g ⊎-assoc
  ε ⊎-assoc (inl x) = refl
  ε ⊎-assoc (inr (inl y)) = refl
  ε ⊎-assoc (inr (inr z)) = refl

module _ {X : Type l1} {Y : Type l2} where
  ⊎-com : (X ⊎ Y) ≃ (Y ⊎ X)
  f ⊎-com (inl x) = inr x
  f ⊎-com (inr y) = inl y
  g ⊎-com (inl y) = inr y
  g ⊎-com (inr x) = inl x
  η ⊎-com (inl x) = refl
  η ⊎-com (inr y) = refl
  h ⊎-com = g ⊎-com
  ε ⊎-com (inl y) = refl
  ε ⊎-com (inr x) = refl

module _ {X1 : Type l1} {X2 : Type l2} {Y1 : Type l3} {Y2 : Type l4}
         (e1 : X1 ≃ Y1) (e2 : X2 ≃ Y2) where
  infixr 5 _⊎e_
  _⊎e_ : (X1 ⊎ X2) ≃ (Y1 ⊎ Y2)
  f _⊎e_ (inl x) = inl (f e1 x)
  f _⊎e_ (inr y) = inr (f e2 y)
  g _⊎e_ (inl x) = inl (g e1 x)
  g _⊎e_ (inr y) = inr (g e2 y)
  η _⊎e_ (inl x) = ap inl (η e1 x)
  η _⊎e_ (inr y) = ap inr (η e2 y)
  h _⊎e_ (inl x) = inl (h e1 x)
  h _⊎e_ (inr y) = inr (h e2 y)
  ε _⊎e_ (inl x) = ap inl (ε e1 x)
  ε _⊎e_ (inr y) = ap inr (ε e2 y)


module _ {X : Type l1} {Y : Type l2} {P : X ⊎ Y -> Type l3}
         (y0 : Y) (p0 : P (inr y0)) where
  open Retraction
  sigma-coprod-retr-r : Retraction (Σ (X ⊎ Y) (λ w -> P w))
                                   (Σ Y (λ y -> P (inr y)))
  f sigma-coprod-retr-r (inl x , p) = y0 , p0
  f sigma-coprod-retr-r (inr y , p) = y , p
  g sigma-coprod-retr-r (y , p) = inr y , p
  ε sigma-coprod-retr-r (y , p) = refl

module _ {X : Type l1} {Y : Type l2} (r : Retraction X Y) where
  open Retraction
  
  is-prop-retr : is-prop X -> is-prop Y
  is-prop-retr ϕ y1 y2 = ! (ε r y1) • ap (f r) (ϕ (g r y1) (g r y2)) • ε r y2

module _ {X : Type l1} (P : X -> Type l2) (Q : X -> Type l3) where
  sigma-distr : Σ X (λ x -> P x ⊎ Q x) ≃ (Σ X P) ⊎ (Σ X Q)
  f sigma-distr (x , inl p) = inl (x , p)
  f sigma-distr (x , inr q) = inr (x , q)
  g sigma-distr (inl (x , p)) = x , inl p
  g sigma-distr (inr (x , q)) = x , inr q
  η sigma-distr (x , inl p) = refl
  η sigma-distr (x , inr q) = refl
  h sigma-distr = g sigma-distr
  ε sigma-distr (inl (x , p)) = refl
  ε sigma-distr (inr (x , q)) = refl


module _ {X : Type l1} {Y : Type l2} (P : X ⊎ Y -> Type l3) where
  open _≃_
  coprod-adj : ((w : X ⊎ Y) -> P w) ≃
               ((x : X) -> P (inl x)) × ((y : Y) -> P (inr y))
  f coprod-adj s = (λ x -> s (inl x)) , (λ y -> s (inr y))
  g coprod-adj (t1 , t2) (inl x) = t1 x
  g coprod-adj (t1 , t2) (inr y) = t2 y
  η coprod-adj s = funext aux
    module η-coprod-adj where
    aux : (w : X ⊎ Y) -> g coprod-adj (f coprod-adj s) w ≡ s w
    aux (inl x) = refl
    aux (inr y) = refl
  h coprod-adj = g coprod-adj
  ε coprod-adj (t1 , t2) = refl

module _ (X : Type l1) where
  ide : X ≃ X
  f ide x = x
  g ide x = x
  η ide x = refl
  h ide = g ide
  ε ide x = refl

module _ {X : Type l1} {Y : Type l2} {Z : Type l3}
         (e1 : Y ≃ Z) (e2 : X ≃ Y)
         where
  infixr 5 _∘e_
  _∘e_ : X ≃ Z
  f _∘e_ x = f e1 (f e2 x)
  g _∘e_ z = g e2 (g e1 z)
  η _∘e_ x = ap (g e2) (η e1 (f e2 x)) • η e2 x
  h _∘e_ z = h e2 (h e1 z)
  ε _∘e_ z = ap (f e1) (ε e2 (h e1 z)) • ε e1 z

module _ {X : Type l1} {Y : Type l2} (e : X ≃ Y) where
  
  !e : Y ≃ X
  f !e = g e
  g !e = f e
  η !e = ε' e
  h !e = f e
  ε !e = η e


module _ {X : Type l1} {Y : Type l2} (e1 : X ≃ Y) where
  embed : {x1 x2 : X} -> (x1 ≡ x2) ≃ (f e1 x1 ≡ f e1 x2)
  f embed                = ap (f e1)
  g (embed {x1} {x2}) e3 = ! (η e1 x1) • ap (g e1) e3 • η e1 x2
  η embed                = inv-sq (η e1)
  h embed                = g embed
  ε embed                = ap-qinv-sq (f e1) (g e1) (η e1) (ε' e1)

module _ {X : Type l1} {Y : Type l2} (e1 : X ≃ Y) where
  adj : {x1 : X} -> {y1 : Y} -> (f e1 x1 ≡ y1) ≃ (x1 ≡ g e1 y1)
  f (adj {x1 = x1}) e2 = ! (η e1 x1) • ap (g e1) e2
  g (adj {y1 = y1}) e2 = ap (f e1) e2 • ε' e1 y1
  η (adj {x1 = x1}) refl = coh (η e1 x1) (τ' e1 x1)
    module η-adj where
    coh : {x1 x2 : X} -> (e3 : x1 ≡ x2) ->
          {e4 : f e1 x1 ≡ f e1 x2} -> (α1 : ap (f e1) e3 ≡ e4) ->
          ap (f e1) (! e3 • refl) • e4 ≡ refl
    coh refl refl = refl
  h adj = g adj
  ε (adj {y1 = y1}) refl = coh _ (ν' e1 y1)
    module ε'-eqv-adj where
    coh : {y1 y2 : Y} -> (e3 : y1 ≡ y2) ->
          {e4 : g e1 y1 ≡ g e1 y2} -> (α1 : ap (g e1) e3 ≡ e4) ->
          ! e4 • ap (g e1) (refl • e3) ≡ refl
    coh refl refl = refl

  adj' : {x1 : X} -> {y1 : Y} -> (y1 ≡ f e1 x1) ≃ (g e1 y1 ≡ x1)
  adj' = !-eqv ∘e adj ∘e !-eqv

module _ {X : Type l1} {P : X -> Type l2}
         {Y : Type l3} {Q : Y -> Type l4}
         (e : X ≃ Y)
         (ϕ : (x : X) -> (P x) ≃ (Q (_≃_.f e x)))
         where
  sigma-eqv : (Σ X P) ≃ (Σ Y Q)
  sigma-eqv = sigma-eqv-1 e ∘e sigma-eqv-2 ϕ

module _ {X : Type l1} {P : X -> Type l2}
         {Y : Type l3} {Q : Y -> Type l4}
         (e : X ≃ Y)
         (ϕ : (x : X) -> (P x) ≃ (Q (_≃_.f e x)))
         where
  pi-eqv : ((x : X) -> P x) ≃ ((y : Y) -> Q y)
  pi-eqv = pi-eqv-1' e ∘e pi-eqv-2 ϕ

module _ {X : Type l1} {P Q : X -> Type l2} where
  fam-eqv : (P ≡ Q) ≃ ((x : X) -> (P x) ≃ (Q x))
  fam-eqv = pi-eqv-2 (λ _ -> tpt-id-eqv) ∘e happly-eqv

module _ {X : Type l1} {Y : Type l2} (e : X ≃ Y) where
  is-prop-eqv : (is-prop X) ≃ (is-prop Y)
  f is-prop-eqv ϕ y1 y2 = g (embed (!e e)) (ϕ (g e y1) (g e y2))
  g is-prop-eqv ϕ x1 x2 = g (embed e) (ϕ (f e x1) (f e x2))
  η is-prop-eqv ϕ = is-prop-is-prop X (g is-prop-eqv (f is-prop-eqv ϕ)) ϕ
  h is-prop-eqv = g is-prop-eqv
  ε is-prop-eqv ϕ = is-prop-is-prop Y (f is-prop-eqv (h is-prop-eqv ϕ)) ϕ
  
  is-contr-eqv : (is-contr X) ≃ (is-contr Y)
  f is-contr-eqv (x , ϕ) =
    f e x , (λ y -> g (adj' e) (ϕ (g e y)))
  g is-contr-eqv (y , ϕ) =
    g e y , (λ x -> f (adj e) (ϕ (f e x)))
  η is-contr-eqv (x , ϕ) = snd (is-contr-is-contr (x , ϕ)) (_ , _)
  h is-contr-eqv = g is-contr-eqv
  ε is-contr-eqv (y , ϕ) = snd (is-contr-is-contr (y , ϕ)) (_ , _)

module _ {X : Type l1} {Y : Type l2} {Z : Type l3} where
  flip-eqv : (X -> Y -> Z) ≃ (Y -> X -> Z)
  f flip-eqv k y x = k x y
  g flip-eqv k x y = k y x
  η flip-eqv k = refl
  h flip-eqv = g flip-eqv
  ε flip-eqv k = refl

  flip : (X -> Y -> Z) -> (Y -> X -> Z)
  flip = f flip-eqv

module _ {X : Type l1} {Y : Type l2}
         (f : X -> Y) (g : Y -> X)
         (η : (x : X) -> g (f x) ≡ x)
         (ε : (y : Y) -> f (g y) ≡ y)
         where
  qinv-is-cfn : (y : Y) -> is-contr (Σ X (λ x -> f x ≡ y))
  fst (qinv-is-cfn y) = g y , ε y
  snd (qinv-is-cfn y) (x , e) =
    pair-eq (! (η x) • ! (ap g (ε (f x))) • ap g (ap f (η x)) • ap g e ,
             coh1 (η x) (ap g (ε (f x))) (ap g (ap f (η x))) (ap g e) e •
             coh2 e (η x))
    module qinv-is-cfn where
    coh1 : {x1 x2 x3 x4 x5 : X} -> {y1 : Y} ->
           (p1 : x1 ≡ x2) -> (p2 : x3 ≡ x1) -> (p3 : x3 ≡ x4) ->
           (p4 : x4 ≡ x5) -> (p5 : f x2 ≡ y1) ->
           tpt (λ x -> f x ≡ y1) (! p1 • ! p2 • p3 • p4) p5 ≡
           ! (ap f p4) • ! (ap f p3) • ap f p2 • ap f p1 • p5
    coh1 refl refl refl refl refl = refl

    coh2 : {x1 x2 : X} -> {y1 : Y} ->
           (e1 : f x2 ≡ y1) ->
           (e2 : g (f x1) ≡ x2) ->
           ! (ap f (ap g e1)) •
           ! (ap f (ap g (ap f e2))) •
           ap f (ap g (ε (f x1))) •
           ap f e2 •
           e1 ≡ ε y1
    coh2 {x1} refl refl = •unitl • •unitl • •unitr • inv-comm ε (f x1) 


module _ {W : Type l1} {X : Type l2} {Y : Type l3} where
  qinv-is-cfn-2 : (k1 : W -> X -> Y) -> (k2 : W -> Y) ->
                  (k3 : (W -> Y) -> X) ->
                  (ϕ1 : (x : X) -> k3 (λ w -> k1 w x) ≡ x) ->
                  (ϕ2 : (k2 : W -> Y) -> (λ w -> k1 w (k3 k2)) ≡ k2) ->
                  is-contr (Σ X (λ x -> (w : W) -> k1 w x ≡ k2 w))
  qinv-is-cfn-2 k1 k2 k3 ϕ1 ϕ2 =
    f (is-contr-eqv (sigma-eqv-2 (λ _ -> happly-eqv)))
      (qinv-is-cfn (flip k1) k3 ϕ1 ϕ2 k2)


module _ {X : Type l1} {Y : Type l2} where
  biinv-eq : {e1 e2 : X ≃ Y} -> f e1 ≡ f e2 -> e1 ≡ e2
  biinv-eq {e1@(biinv _ g1 η1 h1 ε1)} {biinv f2 g2 η2 h2 ε2} refl =
    ap (λ w -> biinv f2 (fst w) (snd w) h1 ε1)
      (contr-is-prop
        (qinv-is-cfn-2
          (λ x g -> g (f2 x)) id (λ k y -> k (h1 y))
          (λ g3 -> funext (λ y -> ap g3 (ε1 y)))
          (λ k -> funext (λ x -> ap k (η' e1 x)))) _ _) •
    ap (λ w -> biinv f2 g2 η2 (fst w) (snd w))
      (contr-is-prop
        (qinv-is-cfn-2
          (λ y h -> f2 (h y)) id (λ k y -> g1 (k y))
          (λ g3 -> funext (λ y -> η1 (g3 y)))
          (λ k -> funext (λ y -> ε' e1 (k y)))) _ _)
      

module _ {X : Type l1} {Y : Type l1} (ψ : is-prop Y) where
  hprop-is-set : (e1 e2 : X ≡ Y) -> e1 ≡ e2
  hprop-is-set e1 e2 =
    g (embed tpt-id-eqv) (biinv-eq (is-prop-pi (λ _ -> ψ) _ _))

module _ {X : Type l1} {Y : Type l2} where
  !e-eqv : (X ≃ Y) ≃ (Y ≃ X)
  f !e-eqv = !e
  g !e-eqv = !e
  η !e-eqv e = biinv-eq refl
  h !e-eqv = g !e-eqv
  ε !e-eqv e = biinv-eq refl

module _ {W : Type l1} {X : Type l2} {Y : Type l3} {Z : Type l4}
         (e1 : Y ≃ Z) (e2 : X ≃ Y) (e3 : W ≃ X) where
  ∘e-assoc : (e1 ∘e e2) ∘e e3 ≡ e1 ∘e e2 ∘e e3
  ∘e-assoc = biinv-eq refl

module _ {X : Type l1} {Y : Type l2} (e : X ≃ Y) where
  ∘e-unitl : ide Y ∘e e ≡ e
  ∘e-unitl = biinv-eq refl

  ∘e-unitr : e ∘e ide X ≡ e
  ∘e-unitr = biinv-eq refl

  ∘e-invl : !e e ∘e e ≡ ide X
  ∘e-invl = biinv-eq (funext (η e))
  
  ∘e-invr : e ∘e !e e ≡ ide Y
  ∘e-invr = biinv-eq (funext (ε' e))


module _ {X : Type l1} {Y : Type l2} {Z : Type l3} (e1 : X ≃ Y) where
  ∘e-precomp-eqv : (Y ≃ Z) ≃ (X ≃ Z)
  f ∘e-precomp-eqv e2 = e2 ∘e e1
  g ∘e-precomp-eqv e2 = e2 ∘e !e e1
  η ∘e-precomp-eqv e2 =
    ∘e-assoc e2 e1 (!e e1) •
    ap (λ e -> e2 ∘e e) (∘e-invr e1) •
    ∘e-unitr e2 
  h ∘e-precomp-eqv = g ∘e-precomp-eqv
  ε ∘e-precomp-eqv e2 =
    ∘e-assoc e2 (!e e1) e1 •
    ap (λ e -> e2 ∘e e) (∘e-invl e1) •
    ∘e-unitr e2 

module _ {X : Type l1} {Y : Type l2} {Z : Type l3} (e1 : Y ≃ Z) where
  ∘e-postcomp-eqv : (X ≃ Y) ≃ (X ≃ Z)
  f ∘e-postcomp-eqv e2 = e1 ∘e e2
  g ∘e-postcomp-eqv e2 = !e e1 ∘e e2
  η ∘e-postcomp-eqv e2 =
    ! (∘e-assoc (!e e1) e1 e2) •
    ap (λ e -> e ∘e e2) (∘e-invl e1) •
    ∘e-unitl e2
  h ∘e-postcomp-eqv = g ∘e-postcomp-eqv
  ε ∘e-postcomp-eqv e2 =
    ! (∘e-assoc e1 (!e e1) e2) •
    ap (λ e -> e ∘e e2) (∘e-invr e1) •
    ∘e-unitl e2

module _ {W : Type l1} {X : Type l2} {Y : Type l3} {Z : Type l4}
         (e1 : W ≃ X) (e2 : Y ≃ Z)
         where
  ∘e-bicomp-eqv : (X ≃ Y) ≃ (W ≃ Z)
  ∘e-bicomp-eqv = ∘e-postcomp-eqv e2 ∘e ∘e-precomp-eqv e1

module _ {X : Type l1} {P : X -> Type l2} {Q : {x : X} -> (p : P x) -> Type l3}
         (ϕ : {x : X} -> (p : P x) -> is-prop (Q p))
         (ρ : {x : X} -> {p1 : P x} -> Q p1 -> {p2 : P x} -> Q p2)
         where
  improper-subtype : {x : X} -> {p : P x} -> Q p -> Σ (P x) (Q {x}) ≃ P x
  f (improper-subtype q1) (p2 , q2) = p2
  g (improper-subtype q1) p2 = p2 , ρ q1
  η (improper-subtype q1) (p2 , q2) = pair-eq (refl , ϕ _ _ _)
  h (improper-subtype q1) = g (improper-subtype  q1)
  ε (improper-subtype q1) p2 = refl
