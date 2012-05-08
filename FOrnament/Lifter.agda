module FOrnament.Lifter where

open import Function

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint
open import Data.Cata
open import Data.Induction

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra
import Ornament.Reornament
open import Ornament.AlgebraicOrnament

open import FOrnament.Functions
open import FOrnament.FunOrnament
open import FOrnament.Patch

-- * 

-- TODO: specialize to a patching situation

module Adj {I : Set}
           (D : I → IDesc I)
           (X : I → Set)
           (α : ∀{i} → ⟦ D i ⟧ X → X i)
  where

  leftAdjoint : (E : Σ I X → IDesc (Σ I X)) →
                (∀{i} → (m : μ D i) → μ E (i , (foldID D α m))) →
                (∀{ix} → μ (algData D X α) ix → μ E ix)
  leftAdjoint E f {(i , x)} x⁺ = subst (λ x' → μ E (i , x')) 
                                       (sym (OAAO⊢ D X α x⁺)) 
                                       (f (forgetOrnament D proj₁ (algOrn D X α) x⁺))

  rightAdjoint : (E : Σ I X → IDesc (Σ I X)) →
                 (∀{ix} → μ (algData D X α) ix → μ E ix) ->
                (∀{i} → (m : μ D i) → μ E (i , (foldID D α m)))
  rightAdjoint E f {i} m = f (makeAlg D X α m)


module LiftConstructor {I I⁺ : Set}
                       (R : I → IDesc I)
                       (f : I⁺ → I)
                       (O : Orn f R)
       where

  open Ornament.Reornament R f O

  added : {i : I}(i⁻¹ : f ⁻¹ i)(x : ⟦ R i ⟧ (μ R)) → Set
  added (inv i⁺) x = Added (O i⁺) x

  args : {i : I}(i⁻¹ : f ⁻¹ i)(x : ⟦ R i ⟧ (μ R))(a : added i⁻¹ x) → Set
  args (inv i⁺) x a = ⟦ ⟦ Args (O i⁺) x a ⟧Orn ⟧ (μ (λ i → ⟦ ornamentalOrnament i ⟧Orn ))

  liftConstructor : {i : I}
                    (x : ⟦ R i ⟧ (μ R))
                    (i⁻¹ : f ⁻¹ i)
                    (T : Type)(T⁺ : FunctionOrn T)
                    (t : ⟦ T ⟧Type) →
                    (a : added i⁻¹ x) →
                    args i⁻¹ x a →
                    patch t T⁺ →
                    patch (con x , t) (μ⁺[ R , f ] O [ i⁻¹ ]× T⁺)
  liftConstructor x (inv i⁺) T T⁺ t e a p = con (e , a) , p

module LiftAlg {I I⁺ : Set}
               (R : I → IDesc I)
               (f : I⁺ → I)
               (O : Orn f R)
       where

  open Ornament.Reornament R f O

  liftAlgType : {T : Type} → (∀{i} → ⟦ R i ⟧ (λ _ → ⟦ T ⟧Type) → ⟦ T ⟧Type) → (T⁺ : FunctionOrn T) → Set
  liftAlgType α T⁺ = ∀{ix : Σ I⁺ (μ R ∘ f)} → 
                         ⟦ ornamentalData ix ⟧ (λ ix → patch (foldID R α (proj₂ ix)) T⁺) → 
                         patch (foldID R α (proj₂ ix)) T⁺

  liftAlg : {i : I}
            (i⁻¹ : f ⁻¹ i)
            {T : Type}(T⁺ : FunctionOrn T)
            (α : ∀{i} → ⟦ R i ⟧ (λ _ → ⟦ T ⟧Type) → ⟦ T ⟧Type)
            (β : liftAlgType α T⁺) →
    patch (foldID R α) (μ⁺[ R , f ] O [ i⁻¹ ]→ T⁺)
  liftAlg (inv i⁺) T⁺ α β = λ x x⁺⁺ → 
                              foldID ornamentalData 
                                     (λ {ix} ih → β {ix} ih) 
                                     x⁺⁺

  liftIndType : {T : Type} → 
                (α : ∀{i} → (xs : ⟦ R i ⟧ (μ R)) → □ (R i) xs (λ _ → ⟦ T ⟧Type) → ⟦ T ⟧Type) →
                (T⁺ : FunctionOrn T) → Set
  liftIndType α T⁺ = ∀{ix : Σ I⁺ (μ R ∘ f)} → 
                      (xs : ⟦ ornamentalData ix ⟧ (μ ornamentalData)) →
                      □ (ornamentalData ix) xs (λ {ix} _ → patch (induction R _ α (proj₂ ix)) T⁺) →
                      patch (induction R _ α (proj₂ ix)) T⁺

  liftInd : {i : I}
            (i⁻¹ : f ⁻¹ i)
            {T : Type}(T⁺ : FunctionOrn T)
            (α : ∀{i} → (xs : ⟦ R i ⟧ (μ R)) → □ (R i) xs (λ _ → ⟦ T ⟧Type) → ⟦ T ⟧Type)
            (β : liftIndType α T⁺)  →
    patch (induction R (λ _ → ⟦ T ⟧Type) α) (μ⁺[ R , f ] O [ i⁻¹ ]→ T⁺)
  liftInd (inv i⁺) T⁺ α β = λ x x⁺⁺ → induction ornamentalData (λ {ix} _ → patch (induction R _ α (proj₂ ix)) T⁺) (λ {ix} → β {ix}) x⁺⁺

  liftCaseType : {T : Type} → 
                (α : ∀{i} → (xs : ⟦ R i ⟧ (μ R)) → ⟦ T ⟧Type) →
                (T⁺ : FunctionOrn T) → Set
  liftCaseType {T} α T⁺ = ∀{ix : Σ I⁺ (μ R ∘ f)} → 
                      (xs : ⟦ ornamentalData ix ⟧ (μ ornamentalData)) →
                      patch (induction R (λ _ → ⟦ T ⟧Type) (λ {i} xs _ → α {i} xs) (proj₂ ix)) T⁺

  liftCase : {i : I}
            (i⁻¹ : f ⁻¹ i)
            {T : Type}(T⁺ : FunctionOrn T)
            (α : ∀{i} → (xs : ⟦ R i ⟧ (μ R)) → ⟦ T ⟧Type)
            (β : liftCaseType α T⁺)  →
    patch (induction R (λ _ → ⟦ T ⟧Type) (λ xs _ → α xs)) (μ⁺[ R , f ] O [ i⁻¹ ]→ T⁺)
  liftCase (inv i⁺) {T} T⁺ α β = λ x x⁺⁺ → induction ornamentalData 
                                                 (λ {ix} _ → patch (induction R (λ _ → ⟦ T ⟧Type) (λ xs _ → α xs) (proj₂ ix)) T⁺)
                                                 (λ {ix} xs _ → β {ix} xs) x⁺⁺


qed : patch tt `⊤
qed = tt
