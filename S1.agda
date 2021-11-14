{-# OPTIONS --without-K --rewriting #-}
module S1 where

open import UTT
{-# BUILTIN REWRITE _≡_ #-}

postulate
  S1 : Type
  b : S1
  l : b ≡ b

postulate
  ind-s1 : (P : S1 -> Type l1) -> (b* : P b) -> (l* : tpt P l b* ≡ b*) ->
           (x : S1) -> P x

postulate
  ind-s1-b : (P : S1 -> Type l1) -> (b* : P b) -> (l* : tpt P l b* ≡ b*) ->
             ind-s1 P b* l* b ≡ b*
{-# REWRITE ind-s1-b #-}

postulate
  ind-s1-l : (P : S1 -> Type l1) -> (b* : P b) -> (l* : tpt P l b* ≡ b*) ->
             apd P (ind-s1 P b* l*) l ≡ l*
