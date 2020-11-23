{-# OPTIONS --cubical --no-import-sorts #-}

module PfinAsQuot where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2)
open import Cubical.Data.Sigma
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Preliminaries
open import Trees
open import PfinAsHIT

SameEls : {A : Type} → List A → List A → Type
SameEls = Relator _≡_

DRelatorEq++₁ : {A : Type}{xs ys zs : List A}
  → DRelator _≡_ xs ys → DRelator _≡_ (xs ++ zs) (ys ++ zs)
DRelatorEq++₁ {xs = xs}{ys} p x mx with ++∈ {xs = xs} mx
... | inj₁ mx' = ∥map∥ (λ { (y , my , eq) → y , ∈++₁ my , eq}) (p x mx')
... | inj₂ mx' = ∣ x , ∈++₂ {xs = ys} mx' , refl ∣

DRelatorEq++₂ : {A : Type}{xs ys zs : List A}
  → DRelator _≡_ ys zs → DRelator _≡_ (xs ++ ys) (xs ++ zs)
DRelatorEq++₂ {xs = xs} p x mx with ++∈ {xs = xs} mx
... | inj₁ mx' = ∣ x , ∈++₁ mx' , refl ∣
... | inj₂ mx' =
  ∥map∥ (λ { (y , my , eq) → y , ∈++₂ {xs = xs} my , eq }) (p x mx')

DRelatorEqCom : {A : Type}(xs ys : List A)
  → DRelator _≡_ (xs ++ ys) (ys ++ xs)
DRelatorEqCom xs ys x mx with ++∈ {xs = xs} mx
... | inj₁ mx' = ∣ x , ∈++₂ {xs = ys} mx' , refl ∣
... | inj₂ mx' = ∣ x , ∈++₁ mx' , refl ∣

DRelatorEqAss₁ : {A : Type}(xs ys zs : List A)
  → DRelator _≡_ (xs ++ ys ++ zs) ((xs ++ ys) ++ zs)
DRelatorEqAss₁ xs ys zs x mx with ++∈ {xs = xs} mx
... | inj₁ mx' = ∣ x , ∈++₁ (∈++₁ mx') , refl ∣
... | inj₂ mx' with ++∈ {xs = ys} mx'
... | inj₁ mx'' = ∣ x , ∈++₁ (∈++₂ {xs = xs} mx'') , refl ∣
... | inj₂ mx'' = ∣ x , ∈++₂ {xs = xs ++ ys} mx'' , refl ∣

DRelatorEqAss₂ : {A : Type}(xs ys zs : List A)
  → DRelator _≡_ ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)
DRelatorEqAss₂ xs ys zs x mx with ++∈ {xs = xs ++ ys} mx
... | inj₂ mx' = ∣ x , ∈++₂ {xs = xs} (∈++₂ {xs = ys} mx') , refl ∣
... | inj₁ mx' with ++∈ {xs = xs} mx'
... | inj₁ mx'' = ∣ x , ∈++₁ mx'' , refl ∣
... | inj₂ mx'' = ∣ x , ∈++₂ {xs = xs} (∈++₁ mx'') , refl ∣

DRelatorEqIdem : {A : Type}(xs : List A)
  → DRelator _≡_ (xs ++ xs) xs
DRelatorEqIdem xs x mx with ++∈ {xs = xs} mx
... | inj₁ mx' = ∣ x , mx' , refl ∣
... | inj₂ mx' = ∣ x , mx' , refl ∣

DRelatorEqNr : {A : Type}(xs : List A)
  → DRelator _≡_ (xs ++ []) xs
DRelatorEqNr xs x mx with ++∈ {xs = xs} mx
... | inj₁ mx' = ∣ x , mx' , refl ∣
... | inj₂ ()

PfinQ : Type → Type
PfinQ A = List A / SameEls

List→PfinRel : ∀{A}{xs ys : List A}
  → DRelator _≡_ xs ys → PfinDRel _≡_ (List→Pfin xs) (List→Pfin ys)
List→PfinRel p x mx =
  ∥rec∥ propTruncIsProp
    (λ mx' →
      ∥map∥ (λ { (y , my , eq) → (y , List→Pfin∈ _ my , eq) }) (p x mx'))
    (∈ₛList→Pfin _ mx)

PfinQ→Pfin : ∀{A} → PfinQ A → Pfin A
PfinQ→Pfin = recQ trunc List→Pfin
    λ xs ys p → PfinEq→Eq (List→PfinRel (p .fst) , List→PfinRel (p .snd))

Pfin→PfinQ : ∀{A} → Pfin A → PfinQ A
Pfin→PfinQ =
  recPfin squash/
    [ [] ]
    (λ a → [ a ∷ [] ])
    (recQ2 squash/ (λ xs ys → [ xs ++ ys ])
      (λ xs ys zs p → eq/ _ _ (DRelatorEq++₁ (p .fst) , DRelatorEq++₁ (p .snd)))
      (λ xs ys zs p → eq/ _ _ (DRelatorEq++₂ (p .fst) , DRelatorEq++₂ (p .snd))))
    (elimProp2 (λ _ _ → squash/ _ _)
      λ xs ys → eq/ _ _ (DRelatorEqCom xs ys , DRelatorEqCom ys xs))
    (elimProp3 (λ _ _ _ → squash/ _ _)
      λ xs ys zs → eq/ _ _ (DRelatorEqAss₁ xs ys zs , DRelatorEqAss₂ xs ys zs))
    (elimProp (λ _ → squash/ _ _)
      λ xs → eq/ _ _ (DRelatorEqIdem xs , λ x mx → ∣ x , ∈++₁ mx , refl ∣))
    (elimProp (λ _ → squash/ _ _)
      λ xs → eq/ _ _ (DRelatorEqNr xs , λ x mx → ∣ x , ∈++₁ mx , refl ∣))

PfinQ→Pfin→PfinQ' : ∀{A} (xs : List A)
  → Pfin→PfinQ (List→Pfin xs) ≡ [ xs ]
PfinQ→Pfin→PfinQ' [] = refl
PfinQ→Pfin→PfinQ' (x ∷ xs) =
  cong (recQ squash/ (λ ys → [ x ∷ ys ]) _) (PfinQ→Pfin→PfinQ' xs)

PfinQ→Pfin→PfinQ : ∀{A} (s : PfinQ A) → Pfin→PfinQ (PfinQ→Pfin s) ≡ s
PfinQ→Pfin→PfinQ = elimProp (λ _ → squash/ _ _) PfinQ→Pfin→PfinQ'

Pfin→PfinQ→Pfin : ∀{A} (s : Pfin A) → PfinQ→Pfin (Pfin→PfinQ s) ≡ s
Pfin→PfinQ→Pfin =
  elimPfinProp (λ _ → _ , trunc _ _) refl (λ _ → nr _)
    λ p q → {!!} ∙ cong₂ _∪_ p q
