{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalgPfin.Set.AsCoindType where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients renaming (rec to recQ)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Preliminaries
open import ListRelations
open import Pfin.AsFreeJoinSemilattice
open BinaryRelation

-- final coalgebra of Pfin as a coinductive type
record νPfin (i : Size) : Type where
  coinductive
  field
    force : {j : Size< i} → Pfin (νPfin j)
open νPfin

-- bisimilarity
record Bisim (i : Size) (s t : νPfin ∞) : Type where
  coinductive
  field
    forceEq : {j : Size< i} → PfinRel (Bisim j) (force s) (force t)
open Bisim

symBisim : ∀{t t₁}(j : Size) → Bisim j t t₁ → Bisim j t₁ t
forceEq (symBisim j b) = forceEq b .snd , forceEq b .fst

-- anamorphism
anaPfin : {X : Type} (c : X → Pfin X) (j : Size) → X → νPfin j
force (anaPfin c j x) {k} = mapPfin (anaPfin c k) (c x)

anaPfinEq : {X : Type} (c : X → Pfin X) (x : X)
  → force (anaPfin c ∞ x) ≡ mapPfin (anaPfin c ∞) (c x)
anaPfinEq c x = refl

-- uniqueness
anaPfinUniqB : {X : Type} (c : X → Pfin X)
  → (f : X → νPfin ∞) (eq : ∀ x → force (f x) ≡ mapPfin f (c x))
  → (j : Size) → ∀ x → Bisim j (f x) (anaPfin c ∞ x)
anaPfinUniqB' : {X : Type} (c : X → Pfin X)
  → (f : X → νPfin ∞) (eq : ∀ x → force (f x) ≡ mapPfin f (c x))
  → (j : Size)
  → ∀ xs → PfinRel (Bisim j) (mapPfin f xs) (mapPfin (anaPfin c ∞) xs)

forceEq (anaPfinUniqB c f eq j x) {k} = 
  subst (λ z → PfinRel (Bisim k) z (mapPfin (anaPfin c ∞) (c x))) (sym (eq x))
        (anaPfinUniqB' c f eq k (c x))
        
anaPfinUniqB' c f eq j =
  elimPfinProp
    (λ xs → _ , isPropPfinRel _ (mapPfin f xs) (mapPfin (anaPfin c ∞) xs))
    ((λ { _ () }) , λ { _ () })
    (λ x →
      (λ y → ∥map∥ λ p → _ , ∣ refl ∣ , subst (λ z → Bisim j z _) (sym p) (anaPfinUniqB c f eq j x)) ,
      (λ y → ∥map∥ λ p → _ , ∣ refl ∣ , subst (λ z → Bisim j z _) (sym p) (symBisim j (anaPfinUniqB c f eq j x))))
    (λ {s}{t} → PfinRel∪ (Bisim j) (mapPfin f s) (mapPfin f t) (mapPfin (anaPfin c ∞) s) (mapPfin (anaPfin c ∞) t))
