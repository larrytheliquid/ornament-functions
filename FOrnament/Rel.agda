module FOrnament.Rel where

open import Relation.Binary.PropositionalEquality

open import Function

open import Data.Unit
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra
open import Ornament.Reornament

open import FOrnament.Functions
open import FOrnament.FunOrnament

rel : Type → ∃ IDesc
rel (μ D [ i ]→ T) = {!!}
rel (μ D [ i ]× T) = {!!}
rel `⊤ = {!!}
