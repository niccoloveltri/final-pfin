{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module ListRelations where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as Pr
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming ([_] to eqCl)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq) renaming (_≤_ to _≤N_; _≟_ to _≟N_)
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open BinaryRelation

open import ListStuff

-- canonical relation lifting on lists
data ListRel {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : List X → List Y → Type ℓ where
  [] : ListRel R [] []
  _∷_ : ∀{x y xs ys} → R x y → ListRel R xs ys
    → ListRel R (x ∷ xs) (y ∷ ys)

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
  isProp× (isPropΠ (λ _ → isPropΠ (λ _ → Pr.isPropPropTrunc)))
          (isPropΠ (λ _ → isPropΠ (λ _ → Pr.isPropPropTrunc)))

Relatorₚ : ∀{ℓ}{X : Type ℓ} (R : X → X → hProp ℓ)
  → List X → List X → hProp ℓ 
Relatorₚ R xs ys =
  Relator (λ x y → ⟨ R x y ⟩) xs ys ,
  isPropRelator _ xs ys

-- reflexivity, symmetry and transitivity of the relator
reflDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → DRelator R xs xs
reflDRelator reflR xs x mx = ∣ x , mx , reflR x ∣

reflRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → Relator R xs xs
reflRelator reflR xs = (reflDRelator reflR xs) , (reflDRelator reflR xs)  

symRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → ∀ {xs ys} → Relator R xs ys → Relator R ys xs
symRelator (p , q) = q , p

transDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y z} → R x y → R y z → R x z)
  → ∀ {xs ys zs} → DRelator R xs ys → DRelator R ys zs → DRelator R xs zs
transDRelator transR p q x mx =
  ∥rec∥ Pr.isPropPropTrunc
    (λ { (y , my , ry) → ∥map∥ (λ { (z , mz , rz) → z , mz , transR ry rz }) (q y my)})
    (p x mx)

transRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y z} → R x y → R y z → R x z)
  → ∀ {xs ys zs} → Relator R xs ys → Relator R ys zs → Relator R xs zs
transRelator transR (p , q) (p' , q') =
  transDRelator transR p p' , transDRelator transR q' q

isEquivRelRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → isEquivRel R → isEquivRel (Relator R)
isEquivRelRelator (equivRel reflR _ transR) =
  equivRel (reflRelator reflR)
           (λ _ _ r → r .snd , r .fst)
           λ _ _ _ → transRelator (transR _ _ _)

-- the relation Relator R is decidable if the relation R is decidable
decDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ} 
  → (∀ x y → Dec (R x y)) → ∀ xs ys → Dec (DRelator R xs ys)
decDRelator decR [] ys = yes (λ _ ())
decDRelator decR (x ∷ xs) ys with decDRelator decR xs ys
... | no ¬p = no (λ q → ¬p (λ y my → q y (there my)))
... | yes p with decMem decR x ys
... | yes q = yes (λ { ._ here → ∣ q ∣
                     ; y (there m) → p y m })
... | no ¬q = no (λ q → ∥rec∥ isProp⊥ ¬q (q  _ here))

decRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x y → Dec (R x y)) → ∀ xs ys → Dec (Relator R xs ys)
decRelator decR xs ys with decDRelator decR xs ys
... | no ¬p = no (λ x → ¬p (fst x))
... | yes p with decDRelator decR ys xs
... | yes q = yes (p , q)
... | no ¬q = no (λ z → ¬q (snd z))

-- interaction between relator and mapList
DRelatorFunMapList : {X Y : Type}(f g : X → Y)
  → {R : Y → Y → Type} → (∀ x → R (f x) (g x))
  → ∀ xs → DRelator R (mapList f xs) (mapList g xs)
DRelatorFunMapList f g {R = R} r xs x mx with pre∈mapList mx
... | (y , my , eq) = ∣ g y , ∈mapList my , subst (λ z → R z (g y)) eq (r y) ∣ 

RelatorFunMapList : {X Y : Type}(f g : X → Y)
  → {R : Y → Y → Type} → (∀ x → R (f x) (g x))
  → (∀ {x x'} → R x x' → R x' x)
  → ∀ xs → Relator R (mapList f xs) (mapList g xs)
RelatorFunMapList f g r Rsym xs =
  DRelatorFunMapList f g r xs , DRelatorFunMapList g f (λ x → Rsym (r x)) xs

-- properties of DRelator _≡_
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

-- given two duplicate-free lists xs and ys such that each element of
-- xs is also ys, then xs is shorter than ys
lengthDupFree : {A : Type} 
  → (xs ys : List A) → dupFree xs → dupFree ys
  → DRelator _≡_ xs ys → length xs ≤N length ys
lengthDupFree [] ys dxs dys r = zero-≤
lengthDupFree (x ∷ xs) ys (p , dxs) dys r =
  ∥rec∥ m≤n-isProp
    (λ { (y , m , eq) →
      ≤-trans (suc-≤-suc (lengthDupFree xs (remove ys m) dxs
                                        (dupFreeRemove m dys)
                                        λ z m' → ∥map∥ (λ { (a , ma , eqa) →
                                                         a ,
                                                         ∈removeRel {R = _≡_} (λ _ → refl) m ma
                                                           (λ eq' → p (subst (_∈ xs) (eqa ∙ eq' ∙ sym eq) m')) ,
                                                         eqa })
                                                       (r z (there m'))))
              (subst (suc (length (remove ys m)) ≤N_) (sym (lengthRemove m)) ≤-refl) })
    (r _ here)
