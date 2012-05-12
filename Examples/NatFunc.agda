module Examples.NatFunc where

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint
open import Functions

open import Relation.Binary.PropositionalEquality

NatD : ⊤ → IDesc ⊤
NatD i = `1 `+ `X i

Nat : Type
Nat = `μ NatD tt

ze : ⟦ Nat ⟧Type
ze = con (inj₁ tt)

su : ⟦ Nat `→ Nat ⟧Type
su n = con (inj₂ n)

plus : ⟦ Nat `→ Nat `→ Nat ⟧Type
plus (con (inj₁ tt)) n = n
plus (con (inj₂ m)) n = su (plus m n)
