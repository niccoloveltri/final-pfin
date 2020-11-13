{-# OPTIONS --cubical --no-import-sorts #-}

module Trees where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Relation.Binary

Cont : ∀ ℓ → Type (ℓ-suc ℓ)
Cont ℓ = Σ (Type ℓ) λ S → S → Type ℓ

⟦_⟧ : ∀{ℓ} → Cont ℓ → Type ℓ → Type ℓ
⟦ S , P ⟧ X = Σ S λ s → P s → X

data ν {ℓ} (C : Cont ℓ) (X : Type ℓ) : Type ℓ
record ν' {ℓ} (C : Cont ℓ) (X : Type ℓ) : Type ℓ

data ν C X where
  leaf : X → ν C X
  node : ν' C X → ν C X 

record ν' C X where
  coinductive
  field
    cont : ⟦ C ⟧ (ν C X)

open ν'

head : ∀{ℓ} {C : Cont ℓ} {X : Type ℓ} (x : ν' C X) → C .fst
head x = cont x .fst

tails : ∀{ℓ} {C : Cont ℓ} {X : Type ℓ} (x : ν' C X)
  → C .snd (cont x .fst) → ν C X
tails x p = cont x .snd p

νmap : ∀{ℓ X Y} (C : Cont ℓ) (f : X → Y) → ν C X → ν C Y
νmap' : ∀{ℓ X Y} (C : Cont ℓ) (f : X → Y) → ν' C X → ν' C Y

νmap C f (leaf x) = leaf (f x)
νmap C f (node xs) = node (νmap' C f xs)

cont (νmap' C f xs) = head xs , λ p → νmap C f (tails xs p)

νbind : ∀{ℓ X Y} (C : Cont ℓ) (f : X → ν C Y) → ν C X → ν C Y
νbind' : ∀{ℓ X Y} (C : Cont ℓ) (f : X → ν C Y) → ν' C X → ν' C Y

νbind C f (leaf x) = f x
νbind C f (node xs) = node (νbind' C f xs)

cont (νbind' C f xs) = head xs , λ p → νbind C f (tails xs p)

relLift : ∀{ℓ X Y} {C : Cont ℓ} (R : X → Y → Type ℓ)
  → ⟦ C ⟧ X → ⟦ C ⟧ Y → Type ℓ 
relLift {C = S , P} R (s₁ , v₁) (s₂ , v₂) =
  (p₁ : P s₁) → Σ (P s₂) λ p₂ → R (v₁ p₁) (v₂ p₂)

{- Define a version relLiftₚ targeting hProp where R targets hProp -}

-- relLift : ∀{ℓ X Y} {C : Cont ℓ} (R : X → Y → hProp ℓ) → ⟦ C ⟧ X → ⟦ C ⟧ Y → hProp ℓ 
-- relLift {C = S , P} R (s₁ , v₁) (s₂ , v₂) =
--   ∀[ p₁ ∶ P s₁ ] ∃[ p₂ ∶ P s₂ ] R (v₁ p₁) (v₂ p₂)


data νRel {ℓ} (C : Cont ℓ) {X Y} (R : X → Y → Type ℓ)
  : Rel (ν C X) (ν C Y) ℓ
record νRel' {ℓ} (C : Cont ℓ) {X Y} (R : X → Y → Type ℓ)
  (xs : ν' C X) (ys : ν' C Y) : Type ℓ

data νRel C R where
  leafR : ∀{x y} → R x y → νRel C R (leaf x) (leaf y)
  nodeR : ∀{xs ys} →  νRel' C R xs ys → νRel C R (node xs) (node ys)

record νRel' C R xs ys where
  coinductive
  field
    contR : relLift (νRel C R) (cont xs) (cont ys)

open νRel'

{- Define a version νRelₚ targeting hProp where R targets hProp. For
this one surely needs the coinduction principle of νC -}

νSim : ∀ {ℓ} (C : Cont ℓ) {X} →  Rel (ν C X) (ν C X) ℓ
νSim C = νRel C _≡_

{- Define a version νSimₚ targeting hProp (so νRelₚ instantiated to ≡ₚ) -}




-- νRelProp : ∀ {ℓ} (C : Cont ℓ) {X Y} (R : X → Y → hProp ℓ) {t₁ t₂}
--   → isProp (νRel C R t₁ t₂)
-- νRelProp' : ∀ {ℓ} (C : Cont ℓ) {X Y} (R : X → Y → hProp ℓ) {t₁ t₂}
--   → isProp (νRel' C R t₁ t₂)
-- νRelₚ : ∀ {ℓ} (C : Cont ℓ) {X Y} (R : X → Y → hProp ℓ) → ν C X → ν C Y → hProp ℓ

-- data νRel C R where
--   leafR : ∀{x y} → ⟨ R x y ⟩ → νRel C R (leaf x) (leaf y)
--   nodeR : ∀{xs ys} →  νRel' C R xs ys → νRel C R (node xs) (node ys)

-- record νRel' C R xs ys where
--   coinductive
--   field
--     contR : ⟨ relLift (νRelₚ C R) (cont xs) (cont ys) ⟩ 

-- νRelProp C R (leafR x) (leafR x₁) = cong leafR (R _ _ .snd x x₁)
-- νRelProp C R (nodeR x) (nodeR x₁) = cong nodeR (νRelProp' C R x x₁)

-- νRelProp' C R {t₁}{t₂} r s = {!!}

-- νRelₚ C R t₁ t₂ = νRel C R t₁ t₂ , νRelProp C R

-- -- -- mem : ∀{ℓ X} {C : Cont ℓ} (R : X → X → hProp ℓ) → X → ⟦ C ⟧ X → hProp ℓ 
-- -- -- mem {C = S , P} R x (s , v) = ∃[ p ∶ P s ] R x (v p)




-- -- --mem : ∀{ℓ X} {C : Cont ℓ} → PropRel X (⟦ C ⟧ X) ℓ 
-- -- --fst mem x c = ⟨ x ∈ c ⟩
-- -- --snd mem x c = isProp⟨⟩ (x ∈ c)

-- -- _∼_ : ∀{ℓ X} {C : Cont ℓ} → Rel (ν C X) (ν C X) ℓ
-- -- t₁ ∼ t₂ = νRel {!!} {!mem!} t₁ t₂


-- -- {-
-- -- open import Cubical.Data.Nat

-- -- data Test : Type where
-- --   leaf : Test
-- --   node : (ℕ → Test) → Test 

-- -- r : ℕ → Test
-- -- r zero = leaf
-- -- r (suc n) = node (λ _ → r n)

-- -- t0 : Test
-- -- t0 = node r
-- -- -}
