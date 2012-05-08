module Examples.LookupAuto where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum

open import Function

open import Relation.Binary.PropositionalEquality

open import Data.IDesc
open import Data.Fixpoint
open import Data.Induction
open import Data.Cata

open import Ornament.Ornament
import Ornament.OrnamentalAlgebra
import Ornament.Reornament

open import FOrnament.Functions
open import FOrnament.FunOrnament
open import FOrnament.Patch
open import FOrnament.Lifter

open import Examples.Nat
open import Examples.Bool
open import Examples.IdOrnament
open import Examples.List
open import Examples.Maybe

-- * _<_

<Type : Type
<Type = μ NatD [ tt ]→ μ NatD [ tt ]→ μ BoolD [ tt ]× `⊤

module <def where

  αm : (Nat → Bool × ⊤) → (xs : ⟦ NatD tt ⟧ (μ NatD)) → □ {X = μ NatD} (NatD tt) xs (λ _ → Bool × ⊤) → Bool × ⊤
  αm ihn (inj₁ tt) _ = true , tt
  αm ihn (inj₂ m) _ = ihn m

  αn : (xs : ⟦ NatD tt ⟧ (μ NatD)) → □ {X = μ NatD} (NatD tt) xs (λ _ → Nat → Bool × ⊤) → Nat → Bool × ⊤
  αn (inj₁ tt) _ = λ m → false , tt
  αn (inj₂ n) ihn = λ m → induction NatD (λ _ → Bool × ⊤) (αm ihn) m

--  αn (inj₁ tt) = λ m → false , tt
--  αn (inj₂ ihn) = λ m → induction NatD (λ _ → Bool × ⊤) (αm ihn) m

  _<_ : ⟦ <Type ⟧Type
  _<_ = λ m n → induction NatD (λ _ → Nat → Bool × ⊤) αn n m
--foldID NatD (λ _ → Nat → Bool × ⊤) αn n m


open <def hiding (αm ; αn)


module <def1 where

  _<'_ : ⟦ <Type ⟧Type
  m <' n with Nat-view n
  m <' .(con (inj₁ tt)) 
      | see-ze = false , tt
  m <' .(con (inj₂ n)) 
      | see-su n with Nat-view m 
  .(con (inj₁ tt)) <' .(con (inj₂ n)) 
      | see-su n 
      | see-ze = true , tt
  .(con (inj₂ m)) <' .(con (inj₂ n)) 
      | see-su n 
      | see-su m = m <' n

open <def1

module <def2 where

module <def3 where

  αm : (Nat → Bool × ⊤) → (xs : ⟦ NatD tt ⟧ (μ NatD)) → □ {X = μ NatD} (NatD tt) xs (λ _ → Bool × ⊤) → Bool × ⊤
  αm ihn (inj₁ tt) _ = true , tt
  αm ihn (inj₂ m) _ = ihn m

  αn : ⟦ NatD tt ⟧ (λ _ → Nat → Bool × ⊤) → Nat → Bool × ⊤
  αn (inj₁ tt) = λ m → false , tt
  αn (inj₂ ihn) = λ m → induction NatD (λ _ → Bool × ⊤) (αm ihn) m

  _<3_ : ⟦ <Type ⟧Type
  _<3_ = λ m n → foldID NatD αn n m

open <def3 hiding (αm ; αn)

-- * lookup type


-- ** Lookup as functional ornament

lookupFunOrn : Set → FunctionOrn <Type
lookupFunOrn A = μ⁺[ NatD , (λ _ → tt) ] IdO NatD [ inv tt ]→ 
                 (μ⁺[ NatD , (λ _ → tt) ] ListO A [ inv tt ]→ 
                  (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤))


-- * ilookup implementation

module ilookupdef (A : Set) where 

  NatId = Ornament.Reornament.ornamentalData NatD (λ tt → tt) (IdO NatD)
  NatList = Ornament.Reornament.ornamentalData NatD (λ tt → tt) (ListO A)
  BoolMaybe = Ornament.Reornament.ornamentalData BoolD (λ tt → tt) (MaybeO A)

  zeze : μ NatId (tt , ze)
  zeze = con (tt , tt)

  susu : {n : Nat} → μ NatId (tt , n) → μ NatId (tt , su n)
  susu n' = con (tt , n')

  data NatId-View : {n : Nat} → μ NatId (tt , n) → Set where
    see-zeze : NatId-View zeze
    see-susu : {n : Nat}(n' : μ NatId (tt , n)) → NatId-View (susu n')

  NatId-view : {n : Nat}(n' : μ NatId (tt , n)) → NatId-View n'
  NatId-view {n} n' with Nat-view n
  NatId-view (con (tt , tt)) | see-ze = see-zeze
  NatId-view (con (tt , n')) | see-su n = see-susu n'

  vnil : μ NatList (tt , ze)
  vnil = con (tt , tt)

  vcons : {n : Nat} → A → μ NatList (tt , n) → μ NatList (tt , su n)
  vcons a vs = con ((a , tt) , vs)

  data NatList-View : {n : Nat} → μ NatList (tt , n) → Set where
    see-vnil : NatList-View vnil
    see-vcons : {n : Nat}(a : A)(vs : μ NatList (tt , n)) → NatList-View (vcons a vs)

  NatList-view : {n : Nat}(vs : μ NatList (tt , n)) → NatList-View vs
  NatList-view {n} vs with Nat-view n
  NatList-view (con (tt , tt)) | see-ze = see-vnil
  NatList-view (con ((a , tt) , vs)) | see-su n = see-vcons a vs

  inothing : μ BoolMaybe (tt , false)
  inothing = con (tt , tt)

  ijust : A → μ BoolMaybe (tt , true)
  ijust a = con ((a , tt) , tt)

{-

  -- * All manual, on pattern-matching definition

  ilookup0 : patch _<'_ (lookupFunOrn A)
  ilookup0 m m' n vs with NatList-view vs
  ilookup0 m m' .(con (inj₁ tt)) .(con (tt , tt)) 
      | see-vnil = inothing , tt
  ilookup0 m m' .(con (inj₂ n)) .(con ((a , tt) , vs)) 
      | see-vcons {n} a vs with NatId-view m'
  ilookup0 .(con (inj₁ tt)) .(con (tt , tt)) .(con (inj₂ n)) .(con ((a , tt) , vs)) 
      | see-vcons {n} a vs 
      | see-zeze = ijust a , tt
  ilookup0 .(con (inj₂ m)) .(con (tt , m')) .(con (inj₂ n)) .(con ((a , tt) , vs)) 
      | see-vcons {n} a vs 
      | see-susu {m} m' = ilookup0 m m' n vs

  -- * Manually lifting algebras, starting point is 2 inductions

  ilookup1 : patch _<_ (lookupFunOrn A)
  ilookup1 = λ m m' n vs → 
               induction NatList 
                         (λ {ix} x → (m : Nat) → 
                                        μ NatId (tt , m) → 
                                        μ BoolMaybe (tt , proj₁ (m < proj₂ ix)) × ⊤) 
                         (λ {ix} → help0 {ix}) vs m m'
           where 
             help1 : (n : Nat)
                     (xs : ⟦ NatList (tt , su n) ⟧ (μ NatList))
                     (ihn : □ {X = μ NatList} (NatList (tt , su n)) xs ((λ {ix} x → (m : Nat) → 
                                        μ NatId (tt , m) → 
                                        μ BoolMaybe (tt , proj₁ (m < proj₂ ix)) × ⊤))) 
                     {ix : ⊤ × Nat} →
                     (xs : ⟦ NatId ix ⟧ (μ NatId)) →
                     □ (NatId ix) xs ((λ{ix} x → μ BoolMaybe (tt , proj₁ (proj₂ ix < (su n))) × ⊤)) →
                     μ BoolMaybe (tt , proj₁ (proj₂ ix < (su n))) × ⊤
             help1 n ((a , tt) , _) ihn {tt , con (inj₁ tt)} xs' box = ijust a , tt
             help1 n xs ihn {tt , con (inj₂ m)} (tt , m') _ = ihn m m'

             help0 : {ix : ⊤ × Nat} →
                     (xs : ⟦ NatList ix ⟧ (μ NatList)) →
                     □ (NatList ix) xs ((λ {ix} x → (m : Nat) → 
                                        μ NatId (tt , m) → 
                                        μ BoolMaybe (tt , proj₁ (m < proj₂ ix)) × ⊤)) →
                     (m : Nat) → μ NatId (tt , m) → 
                     μ BoolMaybe (tt , proj₁ (m < proj₂ ix)) × ⊤ 
             help0 {tt , con (inj₁ tt)} xs ih m m' = inothing , tt
             help0 {tt , con (inj₂ n)} xs ih m m' = 
               induction NatId 
                         (λ{ix} x → μ BoolMaybe (tt , proj₁ (proj₂ ix < (su n))) × ⊤)
                         (λ {ix} → help1 n xs ih {ix}) m'

  -- * Manual lifting of the desired function

  ilookup2 : patch _<3_ (lookupFunOrn A)
  ilookup2 = λ m m' n vs → 
               foldID NatList 
                      (λ x → (m : Nat) → μ NatId (tt , m) → μ BoolMaybe (tt , proj₁ (m <3 proj₂ x)) × ⊤) 
                      (λ {ix} → help0 {ix})  vs m m'  
           where help1 : (n0 : Nat) →
                         (⟦ NatList (tt , (con (inj₂ n0))) ⟧ 
                            (λ x → (m : Nat) → μ NatId (tt , m) → μ BoolMaybe (tt , proj₁ (m <3 proj₂ x)) × ⊤)) →
                         { m : ⊤ × Nat } →
                         (xs : ⟦ NatId m ⟧ (μ NatId)) →
                         □ (NatId m) xs ((λ{ix} x → μ BoolMaybe (tt , proj₁ (proj₂ ix <3 (su n0))) × ⊤) ) →
                         μ BoolMaybe (tt , proj₁ (proj₂ m <3 (su n0))) × ⊤
                 help1 n0 ((a , tt) , ihn) {tt , con (inj₁ tt)} (tt , tt) tt = ijust a , tt
                 help1 n0 ((a , tt) , ihn) {tt , con (inj₂ m)} (tt , m') h = ihn m m'

                 help0 : { n : ⊤ × Nat } →
                         ⟦ NatList n ⟧ (λ x → (m : Nat) → μ NatId (tt , m) → μ BoolMaybe (tt , proj₁ (m <3 (proj₂ x))) × ⊤) →
                         (m : Nat) → μ NatId (tt , m) → μ BoolMaybe (tt , proj₁ (m <3 (proj₂ n))) × ⊤
                 help0 {tt , con (inj₁ tt)} xs = λ m m' → inothing , tt
                 help0 {tt , con (inj₂ n)} xs = 
                   λ m m' → induction NatId 
                                      (λ{ix} x → μ BoolMaybe (tt , proj₁ (proj₂ ix <3 (su n))) × ⊤)
                                      (λ {ix} → help1 n xs {ix}) m'

-}

  -- * Automated lifting


  helpαm : (ih : Nat → Bool × ⊤)
           (n0 : Nat) →
           (⟦ NatList (tt , (su n0)) ⟧ 
                (λ x → patch ih
                             ((μ⁺[ NatD , (λ _ → tt) ] (IdO NatD) [ inv tt ]→ 
                             (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤))))) →
           LiftAlg.liftIndType NatD (λ tt → tt) (IdO NatD) (<def3.αm ih)
                               (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)
  helpαm  ih n0 ((a , tt) , ihn) {(tt , con (inj₁ tt))} xs box = 
          LiftConstructor.liftConstructor BoolD (λ tt → tt) (MaybeO A) (inj₁ tt) (inv tt) _ `⊤ _ (a , tt) tt qed
  helpαm  ih n0 ((a , tt) , ihn) {(tt , con (inj₂ m))} (tt , m') box = ihn m m'

  liftαm : (ih : Nat → Bool × ⊤)
           (n : Nat) →
           ⟦ NatList (tt , su n) ⟧ 
               (λ ix → patch ih
                             ((μ⁺[ NatD , (λ _ → tt) ] (IdO NatD) [ inv tt ]→ 
                             (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)))) →
           patch (induction NatD (λ _ → Bool × ⊤) (<def3.αm ih))
                 (μ⁺[ NatD , (λ _ → tt) ] (IdO NatD) [ inv tt ]→ 
                     (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤))
  liftαm ih n xs = LiftAlg.liftInd NatD (λ tt → tt) (IdO NatD) (inv tt) 
                                   ((μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)) 
                                   (<def3.αm ih) 
                                   (λ {ix'} xss box → helpαm ih n xs {ix'} xss box)


  helpαn : LiftAlg.liftAlgType NatD (λ tt → tt) (ListO A) <def3.αn 
                               ((μ⁺[ NatD , (λ _ → tt) ] (IdO NatD) [ inv tt ]→ 
                                  (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)))
  helpαn {tt , con (inj₁ tt)} (tt , tt) = λ m m' → 
         LiftConstructor.liftConstructor BoolD (λ tt → tt) (MaybeO A) (inj₂ tt) (inv tt) _ `⊤ _ _ tt qed
  helpαn {tt , con (inj₂ n)} xs = liftαm (foldID NatD <def3.αn n) n xs


  liftαn : patch _<3_ (μ⁺[ NatD , (λ _ → tt) ] IdO NatD [ inv tt ]→ 
                         (μ⁺[ NatD , (λ _ → tt) ] ListO A [ inv tt ]→ 
                           (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)))
  liftαn = λ m m' n vs → LiftAlg.liftAlg NatD (λ tt → tt) (ListO A) (inv tt)
                                (μ⁺[ NatD , (λ _ → tt) ] (IdO NatD) [ inv tt ]→ 
                                   (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)) 
                                <def3.αn
                                (λ {ix} → helpαn {ix}) n vs m m'

  ilookup3 :  patch _<3_ (μ⁺[ NatD , (λ _ → tt) ] IdO NatD [ inv tt ]→ 
                         (μ⁺[ NatD , (λ _ → tt) ] ListO A [ inv tt ]→ 
                           (μ⁺[ BoolD , (λ _ → tt) ] (MaybeO A) [ (inv tt) ]× `⊤)))
  ilookup3 = liftαn