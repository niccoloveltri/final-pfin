{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module Worrell.Finality where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as Pr
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients renaming (rec to recQ)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Data.Nat renaming (elim to elimNat)
open import Cubical.Data.Nat.Order hiding (eq) renaming (_≤_ to _≤N_; _≟_ to _≟N_)
open import Cubical.Data.Bool 
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂; rec to rec⊎; elim to elim⊎)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Basics
open import ListRelations
open import ListStuff
open import Pfin.AsSetQuot
open import Pfin.AsFreeJoinSemilattice
open import Pfin.PreservesCountableIntersections
open BinaryRelation

open import Worrell.Limits

-- Worrell's proof: Vω2 is the final Pfin-coalgebra.  This works
-- classically, and constructively requires countable choice and the
-- injectivity of (m : Pfin Vω → Vω) (or analogously LLPO)
module Finality (minj : ∀ s t → m s ≡ m t → s ≡ t)
                (cc : (P : ℕ → Type) → (∀ n → ∥ P n ∥) → ∥ (∀ n → P n) ∥) where

-- since m is injective, so are all the restriction maps iMapPfin2 n
  iMapPfin2inj : ∀ n (x y : iPfin2 (suc n))
    → iMapPfin2 n x ≡ iMapPfin2 n y → x ≡ y
  iMapPfin2inj zero x y eq = minj x y eq
  iMapPfin2inj (suc n) x y eq =
    mapPfinInj (iMapPfin2 n) (iMapPfin2inj n) x y eq

-- injective maps projecting an element in (iPin2 n) to Vω
  u : ∀ n → iPfin2 n → Vω
  u zero x = x
  u (suc n) x = u n (iMapPfin2 n x)
  
  uinj : ∀ n (x y : iPfin2 n)
    → u n x ≡ u n y → x ≡ y
  uinj zero x y eq = eq
  uinj (suc n) x y eq =
    iMapPfin2inj n _ _ (uinj n _ _ eq)
  
  uLem : ∀ (x : Vω2) n
    → u n (iMapPfin2 n (x .fst (suc n))) ≡ m (x .fst 1)
  uLem x zero = refl
  uLem x (suc n) = cong (λ z → u n (iMapPfin2 n z)) (x .snd (suc n)) ∙ uLem x n
  
  uLem2 : ∀ (x : ×pℕ u) n
    → u (suc n) (x .fst (suc n)) ≡ u n (x .fst n)
  uLem2 x zero = x .snd 0
  uLem2 (x , p) (suc n) = uLem2 ((λ n → iMapPfin2 n (x (suc n))) , λ n → p (suc n) ∙ sym (p 0)) n

-- Vω2 is equivalent to the intersection of the family of maps u
  Vω2-iso-×pℕ : Iso Vω2 (×pℕ u)
  Vω2-iso-×pℕ = Σ-cong-iso-snd
    λ x → iso (λ p n → uLem (x , p) n ∙ p 0)
               (λ q n → uinj n _ _ (uLem2 (x , q) n))
               (λ _ → isPropΠ (λ _ → isSetVω _ _) _ _)
               λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _) _ _
  
  Vω2≃×pℕ : Vω2 ≃ ×pℕ u
  Vω2≃×pℕ = isoToEquiv Vω2-iso-×pℕ
      
-- The limit of the shifted chain Vω2Sh is equivalent to the
-- intersection of the family of maps (mapPfin ∘ u)
  ×pℕSh-iso-Vω2Sh : Iso (×pℕ (mapPfin ∘ u)) Vω2Sh
  ×pℕSh-iso-Vω2Sh = Σ-cong-iso-snd
    λ x → iso (λ p n → mapPfinInj (u n) (uinj n) _ _ (mapPfinComp (x (suc n)) ∙ lem x p n))
               (λ p n → lem2 x (λ n → sym (mapPfinComp (x (suc n))) ∙ cong (mapPfin (u n)) (p n)) n)
               (λ _ → isPropΠ (λ _ → trunc _ _) _ _)
               λ _ → isPropΠ (λ _ → trunc _ _) _ _
    where
      lem : (x : ∀ n → Pfin (iPfin2 n))
        → (∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u 0) (x 0))
        → ∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u n) (x n)
      lem x p zero = p 0
      lem x p (suc n) = p (suc n) ∙ sym (p n) 
  
      lem2 : (x : ∀ n → Pfin (iPfin2 n))
        → (∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u n) (x n))
        → ∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u 0) (x 0)
      lem2 x p zero = p 0
      lem2 x p (suc n) = p (suc n) ∙ lem2 x p n
  
  
  ×pℕSh≃Vω2Sh : ×pℕ (mapPfin ∘ u) ≃ Vω2Sh
  ×pℕSh≃Vω2Sh = isoToEquiv ×pℕSh-iso-Vω2Sh

-- The shifted chain has equivalent limit
  Vω22Sh≃Vω2 : Vω2Sh ≃ Vω2
  Vω22Sh≃Vω2 = invEquiv (shift≃ iPfin2-ch isSetiPfin2)

-- Composing the above equivalence shows that Vω2 is a fixpoint of
-- Pfin
  τ-equiv : Pfin Vω2 ≃ Vω2
  τ-equiv =
    compEquiv (Pfin≃ Vω2≃×pℕ)
      (compEquiv (Pfin×pℕ cc (λ _ → trunc) isSetVω u (λ n → uinj (suc n)))
        (compEquiv ×pℕSh≃Vω2Sh Vω22Sh≃Vω2))


-- In particular, Vω is a Pfin-coalgebra
  τ : Vω2 → Pfin Vω2
  τ = invEq τ-equiv

  τ-1≡ : τ-1 ≡ equivFun τ-equiv
  τ-1≡ = funExt (λ x → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
    (funExt (λ n → cong (iMapPfin2 n) (sym (mapPfinComp x)))))

-- Proof that Vω is the final Pfin-coalgebra
  module _ (A : Type) (α : A → Pfin A)
                  (αsim : A → Vω2) 
                  (αsim-mor : ∀ a → τ (αsim a) ≡ mapPfin αsim (α a)) where

    pα : ∀ n (a : A) → iPfin n
    pα zero a = tt
    pα (suc n) a = mapPfin (pα n) (α a)

    pα-res : ∀ n (a : A) → iMapPfin n (mapPfin (pα n) (α a)) ≡ pα n a
    pα-res zero a = refl
    pα-res (suc n) a = mapPfinComp (α a) ∙ cong (λ f → mapPfin f (α a)) (funExt (pα-res n))
  
    pα2 : ∀ n (a : A) → iPfin2 n
    pα2 zero a = (λ n → pα n a) , λ n → pα-res n a 
    pα2 (suc n) a = mapPfin (pα2 n) (α a)
  
    pα2-res : ∀ n (a : A) → iMapPfin2 n (mapPfin (pα2 n) (α a)) ≡ pα2 n a
    pα2-res zero a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin  _ _ _))
      (funExt (λ n → cong (iMapPfin n) (mapPfinComp (α a)) ∙ pα-res n a))
    pα2-res (suc n) a = mapPfinComp (α a) ∙ cong (λ f → mapPfin f (α a)) (funExt (pα2-res n))
  
    coneA : Cone iPfin2-ch A
    coneA = pα2 , pα2-res
  
    αbar : A → Vω2
    αbar = Iso.inv (AdjLim iPfin2-ch _) coneA
  
    αbar-mor' : ∀ a → αbar a ≡ τ-1 (mapPfin αbar (α a))
    αbar-mor' a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
      (funExt (λ n → sym (cong (iMapPfin2 n) (mapPfinComp (α a)) ∙ pα2-res n a)))
  
    αbar-mor : ∀ a → τ (αbar a) ≡ mapPfin αbar (α a)
    αbar-mor a =
        τ (αbar a)
      ≡⟨ (λ i → τ (αbar-mor' a i)) ⟩
        τ (τ-1 (mapPfin αbar (α a)))
      ≡⟨ (λ i → τ (τ-1≡ i (mapPfin αbar (α a)))) ⟩
        τ (equivFun τ-equiv (mapPfin αbar (α a)))
      ≡⟨ (λ i → Iso.leftInv (equivToIso τ-equiv) (mapPfin αbar (α a)) i) ⟩
        mapPfin αbar (α a)
      ∎
  
    αsim-mor' : ∀ a → αsim a ≡ τ-1 (mapPfin αsim (α a))
    αsim-mor' a =
        αsim a
      ≡⟨ sym (Iso.rightInv (equivToIso τ-equiv) (αsim a)) ⟩
        equivFun τ-equiv (τ (αsim a))
      ≡⟨ (λ i → equivFun τ-equiv (αsim-mor a i) ) ⟩
        equivFun τ-equiv (mapPfin αsim (α a))
      ≡⟨ (λ i → τ-1≡ (~ i) (mapPfin αsim (α a))) ⟩
        τ-1 (mapPfin αsim (α a))
      ∎
  
    αbar-eq : ∀ a n → αsim a .fst 0 .fst n ≡ pα n a
    αbar-eq a zero = refl
    αbar-eq a (suc n) = 
      funExt⁻ (cong fst (funExt⁻ (cong fst (αsim-mor' a)) 0)) (suc n)
      ∙ mapPfinComp ((mapPfin (proj iPfin2-ch 0) (mapPfin αsim (α a))))
      ∙ mapPfinComp (mapPfin αsim (α a))
      ∙ mapPfinComp (α a)
      ∙ cong (λ f → mapPfin f (α a)) (funExt (λ x → αsim x .fst 0 .snd n ∙ αbar-eq x n))
  
    αbar-eq2 : ∀ a n → αsim a .fst n ≡ pα2 n a
    αbar-eq2 a zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
      (funExt (αbar-eq a))
    αbar-eq2 a (suc n) =
      funExt⁻ (cong fst (αsim-mor' a)) (suc n)
      ∙ mapPfinComp (mapPfin αsim (α a))
      ∙ mapPfinComp (α a)
      ∙ cong (λ f → mapPfin f (α a)) (funExt (λ x → αsim x .snd n ∙ αbar-eq2 x n))
  
    αbar-uniq : ∀ a → αsim a ≡ αbar a
    αbar-uniq a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
      (funExt (αbar-eq2 a))



