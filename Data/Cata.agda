module Data.Cata where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum


open import Data.IDesc
open import Data.Fixpoint
open import Data.Induction

open import Relation.Binary.PropositionalEquality


module Fold {I : Set}
            (R : I → IDesc I)
            {X : I → Set}
            (α : {i : I} → ⟦ R i ⟧ X → X i)
       where

  mutual
    foldID : {i : I} → μ R i → X i
    foldID (con xs) = α (hyps (R _) xs)

    hyps : (D : IDesc I) → 
           (xs : ⟦ D ⟧ (μ R)) →
           ⟦ D ⟧ X
    hyps `1 tt = tt
    hyps (`X i) xs = foldID xs
    hyps (T `× T') (t , t') = hyps T t , hyps T' t'
    hyps (T `+ T') (inj₁ t) = inj₁ (hyps T t)
    hyps (T `+ T') (inj₂ t') = inj₂ (hyps T' t')
    hyps (`Σ S T) (s , xs) = s , hyps (T s) xs
    hyps (`Π S T) f = λ s → hyps (T s) (f s)

foldID : ∀{I} →
           (R : I → IDesc I)
           {X : I → Set}
           (α : {i : I} → ⟦ R i ⟧ X → X i)
           {i : I}(xs : μ R i) → X i
foldID = Fold.foldID


foldID' : ∀{I} →
           (R : I → IDesc I)
           (X : I → Set)
           (α : {i : I} → ⟦ R i ⟧ X → X i)
           {i : I}(xs : μ R i) → X i
foldID' {I} R X α xs = induction R (λ {i} _ → X i) (λ {i} xs hyps → α (help {R i}{i} xs hyps)) xs
         where help : {D : IDesc I}{i : I}(xs : ⟦ D ⟧ (μ R)) → □ D xs (λ {i} _ → X i) → ⟦ D ⟧ X
               help {`1} tt m = tt
               help {`X i} t m = m
               help {T `× T'}{i} (t , t') mm' = help {T}{i} t (proj₁ mm') , help {T'}{i} t' (proj₂ mm')
               help {T `+ T'}{i} (inj₁ t) m = inj₁ (help {T}{i} t m)
               help {T `+ T'}{i} (inj₂ t') m' = inj₂ (help {T'}{i} t' m')
               help {`Σ S T}{i} (s , xs) m = s , help {T s}{i} xs m
               help {`Π S T}{i} fun m = λ s → help {T s}{i} (fun s) (m s)

