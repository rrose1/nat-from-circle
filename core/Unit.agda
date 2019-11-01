{-# OPTIONS --without-K #-}
module Unit where

open import Core
open import Path

⊤-is-prop : is-prop ⊤
⊤-is-prop tt tt = refl

