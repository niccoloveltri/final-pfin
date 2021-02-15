{-# OPTIONS --cubical --no-import-sorts #-}

module AxiomChoice where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List renaming (map to mapList; [_] to sing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Nat
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂; map to map⊎)
open import Cubical.Functions.Logic hiding (⊥)
open import Cubical.HITs.SetQuotients renaming (rec to recQ)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.Relation.Binary hiding (Rel)
open BinaryRelation

open import Basics

-- pointwise lifting of a relation to a function space
PW : {X A B : Type} (R : A → B → Type) → (X → A) → (X → B) → Type
PW R f g = ∀ x → R (f x) (g x)

-- the quotient a function space by the pointwise lifted relation
[_⇒_]/_ : (A B : Type) (R : B → B → Type) → Type
[ A ⇒ B ]/ R = (A → B) / PW R

-- a function sending equivalence classes of function wrt. pointwise
-- lifted relation and functions into equivalence classes
θ : ∀ A {B} (R : B → B → Type) → [ A ⇒ B ]/ R → A → B / R
θ A R = recQ (isSetΠ (λ _ → squash/)) (λ c x → [ c x ])
  λ c c' r → funExt (λ x → eq/ _ _ (r x))


-- equivalence between two formulation of full axiom of choice; the
-- formulation stating the surjectivity of the map λ g → [_] ∘ g is
-- proved equivalent to the usual presentation of axiom of choice

-- NB: in the first formulation we do not need to 0-truncate the
-- existence of a section, since the type of sections of θ is a
-- proposition; this follows directly from the lemma SectionIsProp
-- below

module _ (θInv : ∀ A {B} (R : B → B → Type) → (A → B / R) → [ A ⇒ B ]/ R)
         (sectionθ : ∀ A {B} (R : B → B → Type) → section (θ A R) (θInv A R)) where

  ac' : ∀ (A : Type) {B : Type} (R : B → B → Type)
    → (f : (A → B) / PW R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ θ A R f
  ac' A R = elimProp (λ _ → propTruncIsProp) (λ g → ∣ g , refl ∣)

  ac : ∀ (A : Type) {B : Type} (R : B → B → Type)
    → (f : A → B / R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ f
  ac A R f =
    ∥map∥ (λ { (g , eq) → g , eq ∙ sectionθ A R f }) (ac' A R (θInv A R f))

module _ (ac : ∀ (A : Type) {B : Type} (R : B → B → Type)
             → isPropValued R → isEquivRel R
             → (f : A → B / R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ f) where

  SectionIsProp' : ∀ A {B} (R : B → B → Type)
    → isPropValued R → isEquivRel R
    → (f : A → B / R)
    → (g g' : [ A ⇒ B ]/ R) (eq : θ A R g ≡ f) (eq' : θ A R g' ≡ f)
    → g ≡ g'
  SectionIsProp' A R Rprop Reqr f = elimProp2 (λ _ _ → isPropΠ (λ _ → isPropΠ λ _ → squash/ _ _))
    λ g g' eq eq' → eq/ _ _ (λ x → effective Rprop Reqr _ _ (λ i → (eq ∙ sym eq') i x))

  SectionIsProp : ∀ A {B} (R : B → B → Type)
    → isPropValued R → isEquivRel R
    → (f : A → B / R)
    → isProp (Σ ([ A ⇒ B ]/ R) (λ g → θ A R g ≡ f))
  SectionIsProp A R Rprop Reqr f (g , eq) (g' , eq') =
    Σ≡Prop (λ _ → isPropFunEq _ _ λ _ → squash/ _ _)
      (SectionIsProp' A R Rprop Reqr f g g' eq eq')

  θInvSec : ∀ A {B} (R : B → B → Type)
    → isPropValued R → isEquivRel R
    → (f : A → B / R) → Σ ([ A ⇒ B ]/ R) (λ g → θ A R g ≡ f)
  θInvSec A R Rprop Reqr f =
    ∥rec∥ (SectionIsProp A R Rprop Reqr f)
         (λ {(g , eq) → [ g ] , eq})
         (ac A R Rprop Reqr f)
    
