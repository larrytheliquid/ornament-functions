module FOrnament.Patch where

open import Relation.Binary.PropositionalEquality

open import Function

open import Data.Unit
open import Data.Product

open import Data.IDesc
open import Data.Fixpoint

open import Ornament.Ornament
open import Ornament.OrnamentalAlgebra
open import Ornament.Reornament

open import FOrnament.Functions
open import FOrnament.FunOrnament


-- * Patch function

patch : ∀{T} → ⟦ T ⟧Type → FunctionOrn T → Set
patch {μ D [ .(f i⁺) ]→ T} fun (μ⁺[ .D , f ] O [ (inv i⁺) ]→ T⁺) = 
      (x : μ D (f i⁺)) → 
         μ (ornamentalData D f O) (i⁺ , x) → patch (fun x) T⁺
patch {μ D [ .(f i⁺) ]× T} (x , t) (μ⁺[ .D , f ] O [ inv i⁺ ]× T⁺) =
      μ (ornamentalData D f O) (i⁺ , x) × patch t T⁺
patch {`⊤} tt `⊤ = ⊤


-- * Implementation of the projections

forget : ∀{T} → (FO : FunctionOrn T)(fun : ⟦ T ⟧Type) → patch fun FO → ⟦ FO ⟧FunctionOrn
forget (μ⁺[ D , f ] O [ inv i⁺ ]→ T⁺) fun p = λ x → forget T⁺ (fun (forgetOrnament D f O x)) 
                                                              (p (forgetOrnament D f O x)
                                                                 (makeOrnAlg D f O x))
forget (μ⁺[ D , f ] O [ inv i⁺ ]× T⁺) (x , xs) (x⁺⁺ , p) = forgetOrnAlg D f O x⁺⁺ , forget T⁺ xs p
forget `⊤ tt tt = tt

⊢Coherence : ∀{T} → (FO : FunctionOrn T)(fun : ⟦ T ⟧Type)(p : patch fun FO) → ⟦ FO ⟧Coherence fun (forget FO fun p)
⊢Coherence (μ⁺[ D , f ] O [ inv i⁺ ]→ T⁺) fun fun⁺ = λ x → ⊢Coherence T⁺ 
                                                                      (fun (forgetOrnament D f O x)) 
                                                                      (fun⁺ (forgetOrnament D f O x) (makeOrnAlg D f O x))
⊢Coherence (μ⁺[ D , f ] O [ inv i⁺ ]× T⁺) (x , xs) (x⁺ , xs⁺) = ornOAAO⊢ D f O x⁺ , ⊢Coherence T⁺ xs xs⁺
⊢Coherence `⊤ tt tt = tt

