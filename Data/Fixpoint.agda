module Data.Fixpoint where

open import Data.IDesc

data μ {I : Set}(R : I → IDesc I)(i : I) : Set where
  con : ⟦ R i ⟧ (μ R) → μ R i
