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
ListD A i  = `Σ (Fin 2) f
  where f : Fin 2 → IDesc ⊤
        f zero = `1
        f (suc zero) = `Σ A (λ _ → `X i)
        f (suc (suc ()))

List : ∀ A → Set
List A = μ (ListD A) tt

nil : ∀ {A} → List A
nil = con (# 0 , tt)

cons : ∀ {A} → A → List A → List A
cons x xs = con (# 1 , x , xs)

data List-View {A} : List A → Set where
  [] : List-View nil
  _∷_ : (x : A) (xs : List A) → List-View (cons x xs)

List-view : ∀ {A} (xs : List A) → List-View xs
List-view (con (zero , tt)) = []
List-view (con (suc zero , x , xs)) = x ∷ xs
List-view (con (suc (suc ()) , _))
