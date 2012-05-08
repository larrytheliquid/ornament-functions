module Data.Induction where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum

open import Data.IDesc
open import Data.Fixpoint

open import Relation.Binary.PropositionalEquality

□ : ∀{I X} → (D : IDesc I)(xs : ⟦ D ⟧ X)(P : ∀ {i} → X i → Set) → Set
□ `1 tt P = ⊤
□ (`X i) xs P = P xs
□ (T `× T') (t , t') P = □ T t P × □ T' t' P
□ (T `+ T') (inj₁ t) P = □ T t P
□ (T `+ T') (inj₂ t') P = □ T' t' P
□ (`Σ S T) (s , xs) P = □ (T s) xs P
□ (`Π S T) f P = (s : S) → □ (T s) (f s) P

all : ∀{I X} → (D : IDesc I)(P : {i : I} → X i → Set)(R : ∀{i} → (x : X i) → P x)(xs : ⟦ D ⟧ X) → □ D xs P
all `1 P R tt = tt
all (`X i) P R xs = R xs
all (T `× T') P R (t , t') = all T P R t , all T' P R t'
all (T `+ T') P R (inj₁ t) = all T P R t 
all (T `+ T') P R (inj₂ t') = all T' P R t'
all (`Σ S T) P R (s , xs) = all (T s) P R xs
all (`Π S T) P R f = λ s → all (T s) P R (f s)

module Elim {I : Set}
            (R : I → IDesc I)
            (P : ∀{i} → μ R i → Set)
            (m : {i : I}
                 (xs : ⟦ R i ⟧ (μ R))
                 (hs : □ (R i) xs P) →
                 P (con xs))
       where

  mutual
    induction : {i : I}(x : μ R i) → P x
    induction (con xs) = m xs (hyps (R _) xs)

    hyps : (D : IDesc I) → (xs : ⟦ D ⟧ (μ R)) → □ D xs P
    hyps `1 tt = tt
    hyps (`X i) xs = induction xs
    hyps (T `× T') (t , t') = hyps T t , hyps T' t'
    hyps (T `+ T') (inj₁ t) = hyps T t
    hyps (T `+ T') (inj₂ t') = hyps T' t'
    hyps (`Σ S T) (s , xs) = hyps (T s) xs
    hyps (`Π S T) f = λ s → hyps (T s) (f s)

induction : ∀{I} →
              (R : I → IDesc I)
              (P : {i : I} → μ R i → Set)
              (m : {i : I}(xs : ⟦ R i ⟧ (μ R)) → □ (R i) xs P → P (con xs))
              {i : I}(xs : μ R i) → P xs
induction R P m x = Elim.induction R P m x
