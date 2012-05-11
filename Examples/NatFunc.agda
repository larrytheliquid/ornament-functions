module Examples.NatFunc where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint
open import FOrnament.Functions

open import Relation.Binary.PropositionalEquality

NatD : ⊤ → IDesc ⊤
NatD i = `1 `+ `X i

Nat : Set
Nat = ⟦ μ NatD [ tt ]× `⊤ ⟧Type

ze : Nat
ze = (con (inj₁ tt)) , tt

su : ⟦ μ NatD [ tt ]→ μ NatD [ tt ]× `⊤ ⟧Type
su n = con (inj₂ n) , tt
