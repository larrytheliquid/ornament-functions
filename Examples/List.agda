module Examples.List where
open import Data.Unit
open import Data.Fin
open import Data.Sum
open import Data.Product
open import Data.IDesc
open import Data.Fixpoint
open import Ornament.Ornament

open import Examples.Nat


ListO : Set → Orn (λ tt → tt) NatD
ListO A _ = `1 `+ insert A (λ _ → `X (inv tt))

ListD : (A : Set) → ⊤ → IDesc ⊤
ListD A i  = `1 `+ `Σ A (λ _ → `X i)

List : ∀ A → Set
List A = μ (ListD A) tt

nil : ∀ {A} → List A
nil = con (inj₁ tt)

cons : ∀ {A} → A → List A → List A
cons x xs = con (inj₂ (x , xs))

data List-View {A} : List A → Set where
  [] : List-View nil
  _∷_ : (x : A) (xs : List A) → List-View (cons x xs)

List-view : ∀ {A} (xs : List A) → List-View xs
List-view (con (inj₁ tt)) = []
List-view (con (inj₂ (x , xs))) = x ∷ xs
