module Main where

-- * Universe of data-types

open import Data.IDesc
open import Data.Fixpoint
open import Data.Induction
open import Data.Cata

-- * Universe of ornaments

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra
open import Ornament.AlgebraicOrnament
open import Ornament.Reornament

-- * Universe of functional ornaments

open import FOrnament.Functions
open import FOrnament.FunOrnament
open import FOrnament.Patch
open import FOrnament.Lifter

-- * Examples

open import Examples.Nat
open import Examples.List
open import Examples.Bool
open import Examples.Maybe
open import Examples.IdOrnament

open import Examples.LookupAuto
-- Manual mode(s): open import Examples.Lookup

open import Examples.RenameKit
