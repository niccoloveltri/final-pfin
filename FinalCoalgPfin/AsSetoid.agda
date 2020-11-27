{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalgPfin.AsSetoid where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients renaming ([_] to eqCl)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary hiding (Rel)
open BinaryRelation
open isEquivRel

open import Preliminaries
open import ListRelations
open import Trees


-- the finite powerset functor on setoids

PfinS : Setoid₀ → Setoid₀
PfinS (setoid A R propR eqrR) =
  setoid (List A) (Relator R) (isPropRelator R) (isEquivRelRelator eqrR)

-- the final coalgebra of PfinS
νPfinS : Setoid₀
νPfinS = setoid (Tree ∞) (ExtEq ∞) isPropExtEq isEquivRelExtEq

forceS : νPfinS →S PfinS νPfinS
forceS = (λ x → force x) , (λ r → forceExt r)

mapPfinS : {S₁ S₂ : Setoid₀} (f : S₁ →S S₂)
  → PfinS S₁ →S PfinS S₂
mapPfinS {_}{S₂} (f , fr) = mapList f ,
  (λ { (p , q) →
     (λ x mx →
       ∥map∥
         (λ { (y , my , r) → f y , ∈mapList my ,
              S₂ .eqrRel .transitive _ _ _ (subst (S₂ .Rel x) (sym (pre∈mapList mx .snd .snd)) (S₂ .eqrRel .reflexive _)) (fr r) })
         (p _ (pre∈mapList mx .snd .fst))) ,
     (λ x mx →
       ∥map∥
         (λ { (y , my , r) → f y , ∈mapList my ,
              S₂ .eqrRel .transitive _ _ _ (subst (S₂ .Rel x) (sym (pre∈mapList mx .snd .snd)) (S₂ .eqrRel .reflexive _)) (fr r) })
         (q _ (pre∈mapList mx .snd .fst))) })

module _
  (S : Setoid₀)
  (cS : S →S PfinS S)
  where

  c = cS .mor
  cRel = cS .morRel


-- the function anaTree is compatible (respects the relations)
  anaTreeRel : ∀ {x y} → S .Rel x y → (j : Size)
    → ExtEq j (anaTree c ∞ x) (anaTree c ∞ y)
  forceExt (anaTreeRel r j) {k} =
    (λ x mx →
      ∥map∥ (λ { (y , my , r') →
               anaTree c ∞ y  ,
               ∈mapList my ,
               subst (λ z → ExtEq k z (anaTree c ∞ y))
                     (pre∈mapList mx .snd .snd)
                     (anaTreeRel r' k)})
            (cRel r .fst _ (pre∈mapList mx .snd .fst))) ,
    (λ x mx →
      ∥map∥ (λ { (y , my , r') →
               anaTree c ∞ y  ,
               ∈mapList my ,
               subst (λ z → ExtEq k z (anaTree c ∞ y))
                     (pre∈mapList mx .snd .snd)
                     (anaTreeRel r' k)})
            (cRel r .snd _ (pre∈mapList mx .snd .fst))) 

-- existence of anamorphism in setoids
  anaPfinS : S →S νPfinS
  anaPfinS = anaTree c ∞ , λ r → anaTreeRel r ∞

  anaPfinSEq : forceS ∘S anaPfinS ≡S mapPfinS anaPfinS ∘S cS
  anaPfinSEq x = reflRelator (reflExtEq ∞) _

-- uniqueness
  anaPfinUniq' : (fS : S →S νPfinS)
    → (∀ x → Relator (ExtEq ∞) (force (fS .mor x)) (mapList (fS .mor) (c x)))
    → (j : Size) → ∀ x → ExtEq j (fS .mor x) (anaTree c ∞ x)
  forceExt (anaPfinUniq' fS fSeq j x) {k} =
    (λ t mt →
      ∥map∥ 
        (λ { (u , mu , r) →  _ , ∈mapList (pre∈mapList mu .snd .fst) ,
          transExtEq k r
            (transExtEq k (subst (ExtEq k u) (sym (pre∈mapList mu .snd .snd)) (reflExtEq ∞ u))
              (anaPfinUniq' fS fSeq k _)) })
        (fSeq x .fst t mt) ) ,
    λ t mt →
      ∥map∥
        (λ { (u , mu , r) → u , mu , subst (λ z → ExtEq k z u) (pre∈mapList mt .snd .snd)
          (transExtEq k (symExtEq k (anaPfinUniq' fS fSeq k _)) r) })
        (fSeq x .snd _ (∈mapList (pre∈mapList mt .snd .fst)))

  anaPfinUniq : (fS : S →S νPfinS)
    → forceS ∘S fS ≡S mapPfinS fS ∘S cS
    → fS ≡S anaPfinS
  anaPfinUniq fS fSeq = anaPfinUniq' fS fSeq ∞

