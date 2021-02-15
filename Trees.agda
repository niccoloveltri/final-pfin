{-# OPTIONS --cubical --no-import-sorts #-}

module Trees where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming ([_] to eqCl)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open BinaryRelation

open import Basics
open import ListRelations

-- non-wellfounded trees with finite ordered branching
record Tree (i : Size) : Type where
  coinductive
  field
    subtrees : {j : Size< i} → List (Tree j)
open Tree public

-- tree bisimilarity
record Bisim (i : Size) (xs ys : Tree i) : Type where
  constructor thunkEq
  coinductive
  field
    subtreesB : {j : Size< i}
      → ListRel (Bisim j) (subtrees xs) (subtrees ys)
open Bisim public

-- coinduction principle: tree bisimilarity implies path equality
bisim : (i : Size) {t₁ t₂ : Tree i} → Bisim i t₁ t₂ → t₁ ≡ t₂
bisimL : (i : Size) {t₁ t₂ : List (Tree i)}
  → ListRel (Bisim i) t₁ t₂ → t₁ ≡ t₂
  
subtrees (bisim s b i) {s'} = bisimL s' (subtreesB b) i 

bisimL s [] i = []
bisimL s (b ∷ bs) i = bisim s b i ∷ bisimL s bs i

-- existence of anamorphism
anaTree : {X : Type} (c : X → List X) → (i : Size) → X → Tree i
subtrees (anaTree c s x) {s'} = mapList (anaTree c s') (c x)

-- the anamorphism is a coalgebra morphism (the corresponding square
-- commutes on the nose)
anaTreeEq : {X : Type} (c : X → List X) (x : X)
  → subtrees (anaTree c ∞ x) ≡ mapList (anaTree c ∞) (c x)
anaTreeEq c x = refl

-- uniqueness of universal property of final List-coalgebra
anaTreeUniqB : {X : Type} (c : X → List X)
  → (f : (s : Size) → X → Tree s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtrees (f s x) {s'} ≡ mapList (f s') (c x))
  → ∀ (s : Size) x → Bisim s (f s x) (anaTree c s x)
anaTreeUniqB' : {X : Type} (c : X → List X)
  → (f : (s : Size) → X → Tree s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtrees (f s x) {s'} ≡ mapList (f s') (c x))
  → (s : Size)
  → ∀ xs → ListRel (Bisim s) (mapList (f s) xs) (mapList (anaTree c s) xs)

subtreesB (anaTreeUniqB c f eq s x) {s'} =
  subst (λ z → ListRel (Bisim s') z (mapList (anaTree c s') (c x)))
        (sym (eq s s' x))
        (anaTreeUniqB' c f eq s' (c x))

anaTreeUniqB' c f eq s [] = []
anaTreeUniqB' c f eq s (x ∷ xs) =
  anaTreeUniqB c f eq s x ∷ anaTreeUniqB' c f eq s xs

anaTreeUniq : {X : Type} (c : X → List X)
  → (f : X → Tree ∞)
  → (eq : ∀ (s : Size) x → subtrees (f x) {s} ≡ mapList f (c x))
  → f ≡ anaTree c ∞
anaTreeUniq c f eq =
  funExt (λ x →
    bisim ∞ (anaTreeUniqB c (λ _ → f) (λ {_ _ → eq _}) ∞ x))

{- ================================================================ -}

-- coinductive closure of the relator, which gives a notion of
-- extensional equality of trees
record ExtEq (i : Size) (t₁ t₂ : Tree ∞) : Type where
  coinductive
  field
    subtreesE : {j : Size< i} → Relator (ExtEq j) (subtrees t₁) (subtrees t₂)
open ExtEq public

isPropExtEq : ∀ t₁ t₂ → isProp (ExtEq ∞ t₁ t₂)
subtreesE (isPropExtEq t₁ t₂ p q i) =
  isPropRelator (ExtEq _) (subtrees t₁) (subtrees t₂)
                (subtreesE p) (subtreesE q) i

ExtEqₚ : Tree ∞ → Tree ∞ → hProp₀
ExtEqₚ t₁ t₂ = ExtEq ∞ t₁ t₂ , isPropExtEq t₁ t₂

-- reflexivity, symmetry and transitivity of ExtEqS
reflExtEq : ∀ j t → ExtEq j t t
subtreesE (reflExtEq j t) {k} =
  reflRelator (reflExtEq k) (subtrees t)

symExtEq : ∀{t t'} (j : Size) → ExtEq j t t' → ExtEq j t' t
subtreesE (symExtEq j p) = subtreesE p .snd , subtreesE p .fst

transExtEq : ∀{t t₁ t₂}(j : Size)
  → ExtEq j t t₁ → ExtEq j t₁ t₂ → ExtEq j t t₂
subtreesE (transExtEq j p q) {k} =
  transRelator (transExtEq k) (subtreesE p) (subtreesE q)

isEquivRelExtEq : isEquivRel (ExtEq ∞)
isEquivRelExtEq =
  equivRel (reflExtEq ∞)
           (λ _ _ → symExtEq ∞)
           (λ _ _ _ → transExtEq ∞)

{-
-- reflexivity of bisimilarity
-- refl-Bisim : ∀ t → Bisim t t
-- refl-Bisim' : ∀ t → ListRel Bisim t t
-- subtreesB (refl-Bisim ts) = refl-Bisim' (subtrees ts)
-- refl-Bisim' [] = []
-- refl-Bisim' (t ∷ ts) = (refl-Bisim t) ∷ refl-Bisim' ts

refl-BisimS : ∀ t → BisimS ∞ t t
refl-BisimS' : ∀ t → ListRel (BisimS ∞) t t
forceEq (refl-BisimS ts) = refl-BisimS' (force ts)
refl-BisimS' [] = []
refl-BisimS' (t ∷ ts) = (refl-BisimS t) ∷ refl-BisimS' ts

-- transitivity of bisimilarity
transBisimS : ∀{t t₁ t₂} → BisimS ∞ t t₁ → BisimS ∞ t₁ t₂ → BisimS ∞ t t₂
transBisimS' : ∀{t t₁ t₂} → ListRel (BisimS ∞) t t₁ → ListRel (BisimS ∞) t₁ t₂
  → ListRel (BisimS ∞) t t₂
forceEq (transBisimS b b') = transBisimS' (forceEq b) (forceEq b')
transBisimS' [] [] = []
transBisimS' (b ∷ p) (b' ∷ p') = transBisimS b b' ∷ transBisimS' p p'

-- equality implies bisimilarity
misibS : {t₁ t₂ : TreeS ∞} → t₁ ≡ t₂ → BisimS ∞ t₁ t₂
misibS {t₁} = J (λ x p → BisimS ∞ t₁ x) (refl-BisimS t₁)    

misib : {t₁ t₂ : Tree} → t₁ ≡ t₂ → Bisim t₁ t₂
misib {t₁} = J (λ x p → Bisim t₁ x) (refl-Bisim t₁)    

-}
