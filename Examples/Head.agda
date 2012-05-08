module Examples.Head where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint
open import Data.Cata

open import Ornament.Ornament

open import FOrnament.Functions
open import FOrnament.FunOrnament
open import FOrnament.Patch
open import FOrnament.Lifter

open import Examples.Nat
open import Examples.Bool
open import Examples.List
open import Examples.Maybe


isSucType : Type
isSucType = μ NatD [ tt ]→ μ BoolD [ tt ]× `⊤

isSucAlg : ⟦ NatD tt ⟧ (λ _ → Bool × ⊤) → Bool × ⊤
isSucAlg (inj₁ tt) = false , tt
isSucAlg (inj₂ xs) = true , tt

isSuc : ⟦ isSucType ⟧Type
isSuc = foldID NatD isSucAlg


headType : Set → FunctionOrn isSucType
headType A = μ⁺[ NatD , (λ tt → tt) ] ListO A [ inv tt ]→ 
             μ⁺[ BoolD , (λ tt → tt) ] MaybeO A [ inv tt ]× `⊤


headPatchAlg : {A : Set} → LiftAlg.liftAlgType NatD (λ tt → tt) (ListO A)
                                isSucAlg 
                                (μ⁺[ BoolD , (λ tt → tt) ] MaybeO A [ inv tt ]× `⊤) 
headPatchAlg {A} {tt , con (inj₁ tt)} (tt , tt) = 
  LiftConstructor.liftConstructor BoolD (λ tt → tt) (MaybeO A) (inj₂ tt) (inv tt) _ `⊤  tt tt tt qed
headPatchAlg {A} {tt , con (inj₂ n)} ((a , tt) , vs) = 
  LiftConstructor.liftConstructor BoolD (λ tt → tt) (MaybeO A) (inj₁ tt) (inv tt) _ `⊤ tt (a , tt) tt qed

headPatch : {A : Set} → patch isSuc (headType A)
headPatch {A} = LiftAlg.liftAlg NatD (λ tt → tt) (ListO A) (inv tt) (μ⁺[ BoolD , (λ tt → tt) ] MaybeO A [ inv tt ]× `⊤) 
                                isSucAlg 
                                (λ {i} → headPatchAlg {A} {i})

