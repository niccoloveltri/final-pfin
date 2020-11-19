{-# OPTIONS --cubical --no-import-sorts #-}

module FinalPfinAsSetoid where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming ([_] to eqCl)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Preliminaries
open import Trees

-- the finite powerset functor on setoids

PfinS : Setoid₀ → Setoid₀
PfinS (A , R) = List A , Relatorₚ R

-- the final coalgebra of PfinS
νPfinS : Setoid₀
νPfinS = Tree , ExtEqₚ

module _
  (S : Setoid₀)
  (cS : SetoidMor S (PfinS S))
  where

-- the function anaTree is compatible (respects the relations)
  anaTreeRel : ∀ {x y} → ⟨ S .Rel x y ⟩
    → ExtEq (anaTree (cS .mor) x) (anaTree (cS .mor) y)
  anaTreeRel' : ∀ {xs ys} → DRelator (λ x y → ⟨ S .Rel x y ⟩) xs ys
    → DRelator ExtEq (anaTree' (cS .mor) xs) (anaTree' (cS .mor) ys)
  anaTreeRel'' : ∀ {xs ys} (p : DRelator (λ x y → ⟨ S .Rel x y ⟩) xs ys) {x}
    → ∃[ y ∈ _ ] (y ∈ ys) × ⟨ S .Rel x y ⟩
    → ∃[ t ∈ _ ] (t ∈ anaTree' (cS .mor) ys) × ExtEq (anaTree (cS .mor) x) t
    
  forceExt (anaTreeRel r) =
    anaTreeRel' (cS .morRel r .fst) , anaTreeRel' (cS .morRel r .snd)

  anaTreeRel' {x ∷ xs} p ._ here = anaTreeRel'' p (p x here)
  anaTreeRel' {x ∷ xs} p t (there mt) =
    anaTreeRel' (λ y my → p y (there my)) t mt 

  anaTreeRel'' p ∣ (y , my , r) ∣ = ∣ _ , anaTree∈ (cS .mor) my , anaTreeRel r ∣
  anaTreeRel'' p (squash a b i) =
    squash (anaTreeRel'' p a) (anaTreeRel'' p b) i

-- existence of anamorphism in setoids
  anaPfinS : SetoidMor S νPfinS
  anaPfinS = anaTree (cS .mor) , anaTreeRel
