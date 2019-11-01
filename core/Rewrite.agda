{-# OPTIONS --without-K --rewriting #-}
module Rewrite where

module _ {i} where
  infix 3 _↦_
  postulate 
    _↦_ : {X Y : Set i} → X → Y → Set i
{-# BUILTIN REWRITE _↦_ #-}
