{-# OPTIONS --cubical --no-import-sorts #-}

module Trees where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
open import Cubical.HITs.SetQuotients renaming ([_] to eqCl)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Preliminaries

-- finitel- branching non-wellfounded trees
record Tree : Type where
  constructor thunk
  coinductive
  field
    force : List Tree
open Tree public

-- canonical relation lifting on trees
data ListRel {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : List X → List Y → Type ℓ where
  [] : ListRel R [] []
  _∷_ : ∀{x y xs ys} → R x y → ListRel R xs ys
    → ListRel R (x ∷ xs) (y ∷ ys)

-- bisimilarity
record Bisim (xs ys : Tree) : Type where
  coinductive
  field
    forceEq : ListRel Bisim (force xs) (force ys)
open Bisim public

-- reflexivity of bisimilarity
refl-Bisim : ∀ t → Bisim t t
refl-Bisim' : ∀ t → ListRel Bisim t t
forceEq (refl-Bisim ts) = refl-Bisim' (force ts)
refl-Bisim' [] = []
refl-Bisim' (t ∷ ts) = (refl-Bisim t) ∷ refl-Bisim' ts

-- transitivity of bisimilarity
transBisim : ∀{t t₁ t₂} → Bisim t t₁ → Bisim t₁ t₂ → Bisim t t₂
transBisim' : ∀{t t₁ t₂} → ListRel Bisim t t₁ → ListRel Bisim t₁ t₂
  → ListRel Bisim t t₂
forceEq (transBisim b b') = transBisim' (forceEq b) (forceEq b')
transBisim' [] [] = []
transBisim' (b ∷ p) (b' ∷ p') = transBisim b b' ∷ transBisim' p p'

-- equality implies bisimilarity
misib : {t₁ t₂ : Tree} → t₁ ≡ t₂ → Bisim t₁ t₂
misib {t₁} = J (λ x p → Bisim t₁ x) (refl-Bisim t₁)    

-- bisimilarity implies equality (coinduction principle)
bisim : {t₁ t₂ : Tree} → Bisim t₁ t₂ → t₁ ≡ t₂
bisim' : {t₁ t₂ : List Tree} → ListRel Bisim t₁ t₂ → t₁ ≡ t₂
force (bisim b i) = bisim' (forceEq b) i
bisim' [] = refl
bisim' (b ∷ bs) = cong₂ {C = λ _ _ → List Tree} _∷_ (bisim b) (bisim' bs)

-- existence of anamorphism
anaTree : {X : Type} (c : X → List X) → X → Tree
anaTree' : {X : Type} (c : X → List X) → List X → List Tree

force (anaTree c x) = anaTree' c (c x) 

anaTree' c [] = []
anaTree' c (x ∷ xs) = anaTree c x ∷ anaTree' c xs

anaTree∈ : {X : Type} (c : X → List X) {x : X} {xs : List X}
  → x ∈ xs → anaTree c x ∈ anaTree' c xs
anaTree∈ c here = here
anaTree∈ c (there mx) = there (anaTree∈ c mx)

anaTreeEq : {X : Type} (c : X → List X) (x : X)
  → force (anaTree c x) ≡ mapList (anaTree c) (c x)
anaTreeEq' : {X : Type} (c : X → List X) (xs : List X)
  → anaTree' c xs ≡ mapList (anaTree c) xs

anaTreeEq c x = anaTreeEq' c (c x)

anaTreeEq' c [] = refl
anaTreeEq' c (x ∷ xs) = cong (_ ∷_) (anaTreeEq' c xs)

-- uniqueness of anamorphism
{-# TERMINATING #-}
anaTreeUniqB : {X : Type} (c : X → List X)
  → (f : X → Tree) (eq : ∀ x → force (f x) ≡ mapList f (c x))
  → ∀ x → Bisim (f x) (anaTree c x)
anaTreeUniqB' : {X : Type} (c : X → List X)
  → (f : X → Tree) (eq : ∀ x → force (f x) ≡ mapList f (c x))
  → ∀ xs → ListRel Bisim (mapList f xs) (mapList (anaTree c) xs)
forceEq (anaTreeUniqB c f eq x) = 
  subst (ListRel Bisim (force (f x))) (sym (anaTreeEq c x))
    (subst (λ z → ListRel Bisim z (mapList (anaTree c) (c x))) (sym (eq x))
    (anaTreeUniqB' c f eq (c x)))
anaTreeUniqB' c f eq [] = []
anaTreeUniqB' c f eq (x ∷ xs) =
  anaTreeUniqB c f eq x ∷ anaTreeUniqB' c f eq xs

-- another relation lifting: two lists are (Relator R)-related if for
-- each element in a list there merely exists an R-related element in
-- the other list
DRelator : ∀{ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → List X → List Y → Type ℓ 
DRelator R xs ys =
  ∀ x → x ∈ xs → ∃[ y ∈ _ ] y ∈ ys × R x y

Relator : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → List X → List X → Type ℓ 
Relator R xs ys =
  DRelator R xs ys × DRelator R ys xs

isPropRelator : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → ∀ xs ys → isProp (Relator R xs ys)
isPropRelator R _ _ =
  isProp× (isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))
          (isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))

Relatorₚ : ∀{ℓ}{X : Type ℓ} (R : X → X → hProp ℓ)
  → List X → List X → hProp ℓ 
Relatorₚ R xs ys =
  Relator (λ x y → ⟨ R x y ⟩) xs ys ,
  isPropRelator _ xs ys

-- coinductive closure of the Relator, giving a notion of extensional
-- equality of trees
record ExtEq (t₁ t₂ : Tree) : Type where
  coinductive
  field
    forceExt : Relator ExtEq (force t₁) (force t₂)
open ExtEq public

isPropExtEq : ∀ t₁ t₂ → isProp (ExtEq t₁ t₂)
forceExt (isPropExtEq t₁ t₂ p q i) =
  isPropRelator ExtEq (force t₁) (force t₂) (forceExt p) (forceExt q) i

ExtEqₚ : Tree → Tree → hProp₀
ExtEqₚ t₁ t₂ = ExtEq t₁ t₂ , isPropExtEq t₁ t₂

