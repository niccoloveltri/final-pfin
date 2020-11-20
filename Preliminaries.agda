{-# OPTIONS --cubical --no-import-sorts #-}

module Preliminaries where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.Sigma
open import Cubical.Functions.Logic 

hProp₀ = hProp ℓ-zero

-- list membership
data _∈_ {ℓ}{X : Type ℓ} (x : X) : List X → Type ℓ where
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

hereEq : ∀{ℓ}{X : Type ℓ}{x y : X}{xs} → x ≡ y → x ∈ (y ∷ xs)
hereEq = J (λ z _ → _ ∈ (z ∷ _)) here

-- properties of membership in the image of a list
∈mapList : {A B : Type} {f : A → B} {a : A} {xs : List A}
  → a ∈ xs → f a ∈ mapList f xs
∈mapList here = here
∈mapList (there ma) = there (∈mapList ma)

pre∈mapList : {A B : Type} {f : A → B} {b : B} {xs : List A}
  → b ∈ mapList f xs → Σ[ a ∈ A ] (a ∈ xs) × (f a ≡ b)
pre∈mapList {xs = x ∷ xs} here = _ , here , refl
pre∈mapList {xs = x ∷ xs} (there mb) with pre∈mapList mb
... | a , ma , eq = a , there ma , eq


-- setoids
record Setoid ℓ : Type (ℓ-suc ℓ) where
  constructor setoid
  field
    Carr : Type ℓ
    Rel : Carr → Carr → hProp ℓ
    reflRel : ∀ x → ⟨ Rel x x ⟩
    symRel : ∀{x y} → ⟨ Rel x y ⟩ → ⟨ Rel y x ⟩
    transRel : ∀{x y z} → ⟨ Rel x y ⟩ → ⟨ Rel y z ⟩ → ⟨ Rel x z ⟩
open Setoid public

Setoid₀ = Setoid ℓ-zero

record _→S_ {ℓ} (S₁ S₂ : Setoid ℓ) : Type ℓ where
  constructor _,_
  field
    mor : S₁ .Carr → S₂ .Carr
    morRel : ∀{x y} → ⟨ S₁ .Rel x y ⟩ → ⟨ S₂ .Rel (mor x) (mor y) ⟩ 
open _→S_ public

_≡S_ : ∀{ℓ} {S₁ S₂ : Setoid ℓ} (f g : S₁ →S S₂) → Type ℓ
_≡S_ {S₂ = S₂} f g = ∀ x → ⟨ S₂ .Rel (f .mor x) (g .mor x) ⟩

infix 21 _∘S_
_∘S_ : ∀{ℓ} {S₁ S₂ S₃ : Setoid ℓ}
  → (g : S₂ →S S₃) (f : S₁ →S S₂)
  → S₁ →S S₃
(g , gr) ∘S (f , fr) = g ∘ f , gr ∘ fr
