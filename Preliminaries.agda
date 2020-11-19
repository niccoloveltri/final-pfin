{-# OPTIONS --cubical --no-import-sorts #-}

module Preliminaries where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List

hProp₀ = hProp ℓ-zero

-- list membership
data _∈_ {ℓ}{X : Type ℓ} (x : X) : List X → Type ℓ where
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- setoids
record Setoid ℓ : Type (ℓ-suc ℓ) where
  constructor _,_
  field
    Carr : Type ℓ
    Rel : Carr → Carr → hProp ℓ
open Setoid public

Setoid₀ = Setoid ℓ-zero

record SetoidMor {ℓ} (S₁ S₂ : Setoid ℓ) : Type (ℓ-suc ℓ) where
  constructor _,_
  field
    mor : S₁ .Carr → S₂ .Carr
    morRel : ∀{x y} → ⟨ S₁ .Rel x y ⟩ → ⟨ S₂ .Rel (mor x) (mor y) ⟩ 
open SetoidMor public

