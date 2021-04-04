{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalg.InTypesAsCoindType where

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
open import Basics
open import ListRelations
open import Pfin.AsFreeJoinSemilattice
open BinaryRelation

-- final coalgebra of Pfin as a coinductive type
record νPfin (i : Size) : Type where
  constructor buildP
  coinductive
  field
    subtreesP : {j : Size< i} → Pfin (νPfin j)
open νPfin

-- bisimilarity
record νPfinB (i : Size) (s t : νPfin i) : Type where
  coinductive
  field
    subtreesPB : {j : Size< i} → PfinRel (νPfinB j) (subtreesP s) (subtreesP t)
open νPfinB

-- bisimilarity is symmetric and reflexive
symνPfinB : ∀ (j : Size) {t t₁} → νPfinB j t t₁ → νPfinB j t₁ t
subtreesPB (symνPfinB j b) = subtreesPB b .snd , subtreesPB b .fst

reflνPfinB : (i : Size) (t : νPfin i) → νPfinB i t t
subtreesPB (reflνPfinB i t) {j} =
  (λ x m → ∣ x , m , reflνPfinB j x ∣) ,
  (λ x m → ∣ x , m , reflνPfinB j x ∣)

-- coinduction principle: bisimilarity implies path equality
bisim : (i : Size) (t u : νPfin i) → νPfinB i t u → t ≡ u
subtreesP (bisim s t u b i) {s'} =
  PfinEq→Eq {s = subtreesP t}{subtreesP u}
    ((λ x m → ∥map∥ (λ { (y , my , b') → y , my , bisim s' x y b' }) (subtreesPB b .fst x m)) ,
     (λ x m → ∥map∥ (λ { (y , my , b') → y , my , bisim s' x y b' }) (subtreesPB b .snd x m)))
    i

-- anamorphism
anaPfin : {X : Type} (c : X → Pfin X) (j : Size) → X → νPfin j
subtreesP (anaPfin c j x) {k} = mapPfin (anaPfin c k) (c x)

anaPfinEq : {X : Type} (c : X → Pfin X) (x : X)
  → subtreesP (anaPfin c ∞ x) ≡ mapPfin (anaPfin c ∞) (c x)
anaPfinEq c x = refl

-- uniqueness
anaPfinUniqB : {X : Type} (c : X → Pfin X)
  → (f : (s : Size) → X → νPfin s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtreesP (f s x) {s'} ≡ mapPfin (f s') (c x))
  → (s : Size) → ∀ x → νPfinB s (f s x) (anaPfin c s x)
anaPfinUniqB' : {X : Type} (c : X → Pfin X)
  → (f : (s : Size) → X → νPfin s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtreesP (f s x) {s'} ≡ mapPfin (f s') (c x))
  → (s : Size)
  → ∀ xs → PfinRel (νPfinB s) (mapPfin (f s) xs) (mapPfin (anaPfin c s) xs)
subtreesPB (anaPfinUniqB c f eq s x) {s'} = 
  subst (λ z → PfinRel (νPfinB s') z (mapPfin (anaPfin c s') (c x))) (sym (eq s s' x))
        (anaPfinUniqB' c f eq s' (c x))

anaPfinUniqB' c f eq s =
  elimPfinProp
    (λ xs → _ , isPropPfinRel _ (mapPfin (f s) xs) (mapPfin (anaPfin c s) xs))
    ((λ { _ () }) , λ { _ () })
    (λ x →
      (λ y → ∥map∥ λ p → _ , ∣ refl ∣ , subst (λ z → νPfinB s z _) (sym p) (anaPfinUniqB c f eq s x)) ,
      (λ y → ∥map∥ λ p → _ , ∣ refl ∣ , subst (λ z → νPfinB s z _) (sym p) (symνPfinB s (anaPfinUniqB c f eq s x)))) 
    (λ {x}{y} → PfinRel∪ (νPfinB s) (mapPfin (f s) x) (mapPfin (f s) y) (mapPfin (anaPfin c s) x) (mapPfin (anaPfin c s) y))

anaPfinUniq : {X : Type} (c : X → Pfin X)
  → (f : X → νPfin ∞)
  → (eq : ∀ (s : Size) x → subtreesP (f x) {s} ≡ mapPfin f (c x))
  → f ≡ anaPfin c ∞
anaPfinUniq c f eq =
  funExt λ x → bisim ∞ _ _ (anaPfinUniqB c (λ _ → f) (λ { _ _ → eq _ }) ∞ x)

-- νPfin is a set

νPfinIsSet : isSet (νPfin ∞)
subtreesP (νPfinIsSet x y p q j k) =
  trunc (subtreesP x) (subtreesP y)
        (λ i → subtreesP (p i)) (λ i → subtreesP (q i))
        j k


