module Data.IDesc where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

data IDesc (I : Set) : Set₁ where
  `1 : IDesc I
  `X : (i : I) → IDesc I
  _`×_ : (l r : IDesc I) → IDesc I
  _`+_ : (l r : IDesc I) → IDesc I
  `Σ : (S : Set)(T : S → IDesc I) → IDesc I
  `Π : (S : Set)(T : S → IDesc I) → IDesc I

⟦_⟧ : {I : Set} → IDesc I → (I → Set) → Set
⟦ `1 ⟧ X = ⊤
⟦ `X i ⟧ X = X i
⟦ T `× T' ⟧ X = ⟦ T ⟧ X × ⟦ T' ⟧ X
⟦ T `+ T' ⟧ X = ⟦ T ⟧ X ⊎ ⟦ T' ⟧ X
⟦ `Σ S T ⟧ X =  Σ[ s ∶ S ] ⟦ T s ⟧ X
⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X

⟦_⟧map : {I : Set} → (D : IDesc I) → {X Y : I → Set} → (f : ∀{i} → X i → Y i) → ⟦ D ⟧ X → ⟦ D ⟧ Y
⟦ `1 ⟧map f tt = tt
⟦ `X i ⟧map f xs = f xs
⟦ l `× r ⟧map f (ls , rs) = ⟦ l ⟧map f ls  , ⟦ r ⟧map f rs
⟦ l `+ r ⟧map f (inj₁ x) = inj₁ (⟦ l ⟧map f x)
⟦ l `+ r ⟧map f (inj₂ y) = inj₂ (⟦ r ⟧map f y)
⟦ `Σ S T ⟧map f (s , xs) = s , ⟦ T s ⟧map f xs
⟦ `Π S T ⟧map f xs = λ s → ⟦ T s ⟧map f (xs s)