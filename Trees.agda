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

open import Preliminaries
open import ListRelations

-- finitely-branching non-wellfounded trees
record Tree (i : Size) : Type where
  constructor thunk
  coinductive
  field
    force : {j : Size< i} → List (Tree j)
open Tree public

-- bisimilarity
record Bisim (i : Size) (xs ys : Tree ∞) : Type where
  coinductive
  field
    forceEq : {j : Size< i} → ListRel (Bisim j) (force xs) (force ys)
open Bisim public

-- reflexivity of bisimilarity
refl-Bisim : ∀ t → Bisim ∞ t t
refl-Bisim' : ∀ t → ListRel (Bisim ∞) t t
forceEq (refl-Bisim ts) = refl-Bisim' (force ts)
refl-Bisim' [] = []
refl-Bisim' (t ∷ ts) = (refl-Bisim t) ∷ refl-Bisim' ts

-- transitivity of bisimilarity
transBisim : ∀{t t₁ t₂} → Bisim ∞ t t₁ → Bisim ∞ t₁ t₂ → Bisim ∞ t t₂
transBisim' : ∀{t t₁ t₂} → ListRel (Bisim ∞) t t₁ → ListRel (Bisim ∞) t₁ t₂
  → ListRel (Bisim ∞) t t₂
forceEq (transBisim b b') = transBisim' (forceEq b) (forceEq b')
transBisim' [] [] = []
transBisim' (b ∷ p) (b' ∷ p') = transBisim b b' ∷ transBisim' p p'

-- equality implies bisimilarity
misib : {t₁ t₂ : Tree ∞} → t₁ ≡ t₂ → Bisim ∞ t₁ t₂
misib {t₁} = J (λ x p → Bisim ∞ t₁ x) (refl-Bisim t₁)    

-- bisimilarity implies equality (coinduction principle)
-- bisim : (t₁ t₂ : Tree ∞) → Bisim ∞ t₁ t₂ → t₁ ≡ t₂
-- bisim' : (t₁ t₂ : List (Tree ∞)) → ListRel (Bisim ∞) t₁ t₂ → t₁ ≡ t₂
-- force (bisim t₁ t₂ b i) = {!!}
-- bisim' t₁ t₂ [] = refl
-- bisim' ._ ._ (b ∷ bs) = cong₂ {C = λ _ _ → List (Tree ∞)} _∷_ (bisim _ _ b) (bisim' _ _ bs)

-- force (bisim b i) = bisim' (forceEq b) i

-- existence of anamorphism
anaTree : {X : Type} (c : X → List X) (j : Size) → X → Tree j
force (anaTree c j x) = mapList (anaTree c _) (c x)

anaTreeEq : {X : Type} (c : X → List X) (x : X)
  → force (anaTree c ∞ x) ≡ mapList (anaTree c ∞) (c x)
anaTreeEq c x = refl

-- uniqueness of anamorphism

anaTreeUniqB : {X : Type} (c : X → List X)
  → (f : X → Tree ∞) (eq : ∀ x → force (f x) ≡ mapList f (c x))
  → (j : Size) → ∀ x → Bisim j (f x) (anaTree c ∞ x)
anaTreeUniqB' : {X : Type} (c : X → List X)
  → (f : X → Tree ∞) (eq : ∀ x → force (f x) ≡ mapList f (c x))
  → (j : Size)
  → ∀ xs → ListRel (Bisim j) (mapList f xs) (mapList (anaTree c ∞) xs)
forceEq (anaTreeUniqB c f eq j x) {k}=
  subst (λ z → ListRel (Bisim k) z _) (sym (eq x))
         (anaTreeUniqB' c f eq _ (c x))
anaTreeUniqB' c f eq j [] = []
anaTreeUniqB' c f eq j (x ∷ xs) =
  anaTreeUniqB c f eq j x ∷ anaTreeUniqB' c f eq j xs

-- coinductive closure of the relator, which gives a notion of extensional
-- equality of trees
record ExtEq (i : Size) (t₁ t₂ : Tree ∞) : Type where
  coinductive
  field
    forceExt : {j : Size< i} → Relator (ExtEq j) (force t₁) (force t₂)
open ExtEq public

isPropExtEq : ∀ t₁ t₂ → isProp (ExtEq ∞ t₁ t₂)
forceExt (isPropExtEq t₁ t₂ p q i) =
  isPropRelator (ExtEq _) (force t₁) (force t₂) (forceExt p) (forceExt q) i

ExtEqₚ : Tree ∞ → Tree ∞ → hProp₀
ExtEqₚ t₁ t₂ = ExtEq ∞ t₁ t₂ , isPropExtEq t₁ t₂

-- reflexivity, symmetry and transitivity of ExtEq
reflExtEq : ∀ j t → ExtEq j t t
forceExt (reflExtEq j t) {k} =
  reflRelator (reflExtEq k) (force t)

symExtEq : ∀{t t'} (j : Size) → ExtEq j t t' → ExtEq j t' t
forceExt (symExtEq j p) = forceExt p .snd , forceExt p .fst

transExtEq : ∀{t t₁ t₂}(j : Size)
  → ExtEq j t t₁ → ExtEq j t₁ t₂ → ExtEq j t t₂
forceExt (transExtEq j p q) {k} =
  transRelator (transExtEq k) (forceExt p) (forceExt q)

isEquivRelExtEq : isEquivRel (ExtEq ∞)
isEquivRelExtEq =
  equivRel (reflExtEq ∞)
           (λ _ _ → symExtEq ∞)
           (λ _ _ _ → transExtEq ∞)
