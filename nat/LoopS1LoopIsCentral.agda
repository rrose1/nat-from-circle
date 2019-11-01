{-# OPTIONS --without-K --rewriting #-}
module LoopS1LoopIsCentral where

open import S1TT


open SectionOnLoopS1

l-is-central : SectionOnLoopS1
P-b l-is-central x = x ◾ l ≡ l ◾ x
p0  l-is-central = ◾unitl ◾ ! ◾unitr
P-l l-is-central x = lcomp-eqv ◾assoc ∘e lwhisk-eqv

com-l = s (l-is-central)
com-l-cmpt = cmpt (l-is-central)

