{-# OPTIONS --cubical --no-import-sorts #-}

module Preliminaries where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂; map to map⊎)
open import Cubical.Functions.Logic 
open import Cubical.HITs.SetQuotients renaming (rec to recQ)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.Relation.Binary hiding (Rel)
open BinaryRelation

hProp₀ = hProp ℓ-zero

mapListComp : ∀{ℓ}{X Y Z : Type ℓ}{g : Y → Z}{f : X → Y} (xs : List X)
  → mapList g (mapList f xs) ≡ mapList (g ∘ f) xs
mapListComp [] = refl
mapListComp (x ∷ xs) = cong (_ ∷_) (mapListComp xs)


-- list membership
infix 21 _∈_
data _∈_ {ℓ}{X : Type ℓ} (x : X) : List X → Type ℓ where
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

++∈ : ∀{ℓ}{X : Type ℓ}{x : X}{xs ys} → x ∈ (xs ++ ys) → x ∈ xs ⊎ x ∈ ys
++∈ {xs = []} m = inj₂ m
++∈ {xs = x ∷ xs} here = inj₁ here
++∈ {xs = x ∷ xs} (there m) = map⊎ there (λ z → z) (++∈ {xs = xs} m)

∈++₁ : ∀{ℓ}{X : Type ℓ}{x : X}{xs ys} → x ∈ xs → x ∈ (xs ++ ys)
∈++₁ here = here
∈++₁ (there p) = there (∈++₁ p)

∈++₂ : ∀{ℓ}{X : Type ℓ}{x : X}{xs ys} → x ∈ ys → x ∈ (xs ++ ys)
∈++₂ {xs = []} m = m
∈++₂ {xs = x ∷ xs} m = there (∈++₂ m)


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

Set→Setoid : ∀{ℓ} → hSet ℓ → Setoid ℓ
Set→Setoid (X , Xset) =
  setoid X (λ x y → (x ≡ y) , Xset _ _) (λ _ → refl) sym _∙_

isPropFunEq : ∀{ℓ}{A B : Type ℓ} (f g : A → B)
  → (∀ x → isProp (f x ≡ g x))
  → isProp (f ≡ g)
isPropFunEq f g p eq1 eq2 i j x =
  p x (λ k → eq1 k x) (λ k → eq2 k x) i j 

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
-- proved equivalent to the usual presentation of axiom of choice in
-- many places, e.g. in my PhD thesis.

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
    
