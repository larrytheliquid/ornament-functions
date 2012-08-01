module Diff where

data `Set : Set₁ where
  `⊤ : `Set
  _`×_ : (l r : `Set) → `Set

data Diff : (S : `Set) → Set₁ where
  `⊤ : Diff `⊤
  _`×_ : ∀{S T} → Diff S → Diff T → Diff (S `× T)
