{-# OPTIONS --without-K #-}
module Bool where

open import Core
open import Path
open import Empty


module BoolIsSet where
  code : Bool → Bool → Set
  code false false = ⊤
  code true false = ⊥
  code false true = ⊥
  code true true = ⊤

  r : (x : Bool) → code x x
  r false = tt
  r true = tt

  enc : (x y : Bool) → x ≡ y → code x y
  enc x y p = tpt (code x) p (r x)

  dec : (x y : Bool) → code x y → x ≡ y
  dec false false _ = refl
  dec false true = rec⊥
  dec true false = rec⊥
  dec true true _ = refl

  enc-dec : {x y : Bool} → (p : x ≡ y) → dec x y (enc x y p) ≡ p
  enc-dec {y = false} refl = refl
  enc-dec {y = true} refl = refl


module _ where
  open BoolIsSet
  
  Bool-is-set : is-set Bool
  Bool-is-set {false} {false} p q = ! (enc-dec p) ◾ enc-dec q
  Bool-is-set {false} {true} p q =
    ! (enc-dec p) ◾ ap (dec false true) (rec⊥ (enc false true p)) ◾ enc-dec q
  Bool-is-set {true} {false} p q =
    ! (enc-dec p) ◾ ap (dec true false) (rec⊥ (enc true false p)) ◾ enc-dec q
  Bool-is-set {true} {true} p q = ! (enc-dec p) ◾ enc-dec q


[_] : Bool → Set
[ b ] = b ≡ true
