module Larry.Poly where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum

infix 1 `μ_

data Poly : Set₁ where
  `⊥ `⊤ `X : Poly
  _`×_ _`⊎_ : (S T : Poly) → Poly
  -- `Σ `Π : (S : Set)(T : S → Poly) → Poly

El : Poly → Set → Set
El `⊥ X = ⊥
El `⊤ X = ⊤
El `X X = X
El (S `× T) X = El S X × El T X
El (S `⊎ T) X = El S X ⊎ El T X
-- El (`Σ S T) X =  Σ[ s ∶ S ] El (T s) X
-- El (`Π S T) X = (s : S) → El (T s) X

data μ (R : Poly) : Set where
  [_] : El R (μ R) → μ R

data Type : Set₁
⟦_⟧ : Type → Set

data Type where
  _`→_ : (S T : Type) → Type -- _`×_ 
  `Σ : (S : Type) (T : ⟦ S ⟧ → Type) → Type -- `Π 
  `μ_ : (R : Poly) → Type

⟦ S `→ T ⟧ = ⟦ S ⟧ → ⟦ T ⟧
-- ⟦ S `× T ⟧ = ⟦ S ⟧ × ⟦ T ⟧
-- ⟦ `Π S T ⟧ = (s : ⟦ S ⟧) → ⟦ T s ⟧
⟦ `Σ S T ⟧ = Σ[ s ∶ ⟦ S ⟧ ] ⟦ T s ⟧
⟦ `μ R ⟧ = μ R

--------------------------------------------------------------------------------

`ℕ : Type
`ℕ = `μ `⊤ `⊎ `X

ze : ⟦ `ℕ ⟧
ze = [ inj₁ tt ]

su : ⟦ `ℕ `→ `ℕ ⟧
su n = [ inj₂ n ]

--------------------------------------------------------------------------------

`Fin : Type
`Fin = `Σ `ℕ (λ n → `μ f n) where
  f : ⟦ `ℕ ⟧ → Poly
  f [ inj₁ tt ] = `⊥
  f [ inj₂ n ] = `⊤ `⊎ f n

-- hm : ⟦ `ℕ ⟧ → ⟦ `Fin ⟧
-- hm n = n , {!!}

fone : ⟦ `Fin ⟧
fone = su ze , [ inj₁ tt ]

-- fsuc : ⟦ `ℕ `→ `Fin




