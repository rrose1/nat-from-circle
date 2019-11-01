{-# OPTIONS --without-K --rewriting #-}
module Test where

open import S1TT
open import LoopS1HasDiv2Alg
open import Structure
open import Presegment
open import Asymmetry
open import Segment
open import LoopS1Segment
open import IncrementMin
open import IncrementMax
open import LoopS1HasDecEq
open import Nat
open import ApproximationDefinition
open import ApproximationCoherence
open import Approximation


open _≃_

open import Agda.Builtin.Nat renaming (suc to s)

g-test : Nat → N
g-test 0 = z
g-test (s n) = suc (g-test n)

ε-test : (n : Nat) → indN (λ _ → Nat) 0 (λ _ → s) (g-test n) ≡ n
ε-test 0 = refl
ε-test (s n) = indN-s (λ _ → Nat) 0 (λ _ → s) (g-test n) ◾ ap s (ε-test n)

test : N ≃ Nat
f test = indN (λ _ → Nat) 0 (λ _ → s)
g test = g-test
η test = indN (λ n → g test (f test n) ≡ n) refl
              (λ n e → ap g-test (indN-s (λ _ → Nat) 0 (λ _ → s) n) ◾ ap suc e)
h test = g-test
ε test = ε-test
