{-# OPTIONS --cubical --no-import-sorts #-}

module ListStuff where

open import Cubical.Foundations.Everything
open import Cubical.Data.List renaming (map to mapList; [_] to sing)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂; map to map⊎)
open import Cubical.Relation.Nullary


--open import Cubical.Core.Everything
--open import Cubical.Data.Unit
--open import Cubical.Functions.Logic hiding (⊥)
--open import Cubical.HITs.SetQuotients renaming (rec to recQ)
--open import Cubical.HITs.PropositionalTruncation as Pr
--  renaming (map to ∥map∥; rec to ∥rec∥)
--open import Cubical.Relation.Binary hiding (Rel)
--open BinaryRelation

-- mapList preserves composition
mapListComp : ∀{ℓ}{X Y Z : Type ℓ}{g : Y → Z}{f : X → Y} (xs : List X)
  → mapList g (mapList f xs) ≡ mapList (g ∘ f) xs
mapListComp [] = refl
mapListComp (x ∷ xs) = cong (_ ∷_) (mapListComp xs)


-- list membership
infix 21 _∈_
data _∈_ {ℓ}{X : Type ℓ} (x : X) : List X → Type ℓ where
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- properties of list membership
∈sing : ∀{ℓ}{X : Type ℓ}{x y : X} → x ∈ sing y → x ≡ y
∈sing here = refl

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

-- length of a mapList
lengthMapList : ∀{ℓ}{A B : Type ℓ}{f : A → B}(xs : List A)
  → length (mapList f xs) ≡ length xs
lengthMapList [] = refl
lengthMapList (x ∷ xs) = cong suc (lengthMapList xs)

-- mapList is a monoid homomorphism (commutes with ++)
mapList++ : ∀{ℓ}{A B : Type ℓ}{f : A → B}(xs ys : List A)
  → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList++ [] ys = refl
mapList++ (x ∷ xs) ys = cong (_ ∷_) (mapList++ xs ys)

-- removing an element from a list
remove : ∀{ℓ}{A : Type ℓ} {x : A} xs → x ∈ xs → List A
remove (x ∷ xs) here = xs
remove (y ∷ xs) (there m) = y ∷ remove xs m

-- interaction between ∈ and remove
remove∈ : ∀{ℓ}{A : Type ℓ} {x y : A} {xs} (m : x ∈ xs)
  → y ∈ remove xs m → y ∈ xs
remove∈ here m' = there m'
remove∈ (there m) here = here
remove∈ (there m) (there m') = there (remove∈ m m')

∈removeRel : ∀{ℓ}{A : Type ℓ}
  → {R : A → A → Type ℓ} → (∀ x → R x x)
  → {xs : List A} {x w : A} (m : x ∈ xs) 
  → w ∈ xs → (R w x → ⊥)
  → w ∈ remove xs m
∈removeRel reflR here here ¬r = ⊥-rec (¬r (reflR _))
∈removeRel reflR here (there mw) ¬r = mw
∈removeRel reflR (there mx) here ¬r = here
∈removeRel reflR (there mx) (there mw) ¬r = there (∈removeRel reflR mx mw ¬r)

-- length of remove
lengthRemove : ∀{ℓ}{A : Type ℓ} {x : A} {xs} (m : x ∈ xs)
  → length xs ≡ suc (length (remove xs m))
lengthRemove here = refl
lengthRemove (there m) = cong suc (lengthRemove m)

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

-- list membership is decidable if equality on the carrier is
-- decidable
decMem : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ} 
  → (∀ x y → Dec (R x y)) → ∀ x ys
  → Dec (Σ[ y ∈ _ ] (y ∈ ys) × R x y)
decMem decR x [] = no (λ { () })
decMem decR x (y ∷ ys) with decR x y
... | yes p = yes (y , here , p)
... | no ¬p with decMem decR x ys
... | yes (z , m , r) = yes (z , there m , r)
... | no ¬q = no (λ { (._ , here , r') → ¬p r'
                    ; (w , there m' , r') → ¬q (w , m' , r') })

-- removing all duplicates from a list (assuming decidable equality)
removeDups : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (xs : List A) → List A
removeDups decA [] = []
removeDups decA (x ∷ xs) with decMem decA x xs
... | yes p = removeDups decA xs
... | no ¬p = x ∷ removeDups decA xs

-- by removing all duplicates we obtain a generally shorter list
lengthRemoveDups : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (xs : List A) → length (removeDups decA xs) ≤ length xs
lengthRemoveDups decA [] = ≤-refl
lengthRemoveDups decA (x ∷ xs) with decMem decA x xs
... | yes p = ≤-trans (lengthRemoveDups decA xs) (≤-suc ≤-refl)
... | no ¬p = suc-≤-suc (lengthRemoveDups decA xs)

-- lemmata about membership in removeDups
removeDups∈ : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (xs : List A) {x : A}
  → x ∈ removeDups decA xs → x ∈ xs
removeDups∈ decA (x ∷ xs) m with decMem decA x xs
... | yes p = there (removeDups∈ decA xs m)
removeDups∈ decA (x ∷ xs) here | no ¬p = here
removeDups∈ decA (x ∷ xs) (there m) | no ¬p =
  there (removeDups∈ decA xs m)

∈removeDups : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (xs : List A) {x : A}
  → x ∈ xs → x ∈ removeDups decA xs
∈removeDups decA (x ∷ xs) m with decMem decA x xs
∈removeDups decA (x ∷ xs) here | yes (y , m , eq) = subst (_∈ removeDups decA xs) (sym eq) (∈removeDups decA xs m)
∈removeDups decA (x ∷ xs) (there m) | yes p = ∈removeDups decA xs m
∈removeDups decA (x ∷ xs) here | no ¬p = here
∈removeDups decA (x ∷ xs) (there m) | no ¬p = there (∈removeDups decA xs m)

-- interaction between mapList and removeDups
removeDupMapList : {A B : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (decB : (x y : B) → Dec (x ≡ y))
  → {f : A → B} (injf : ∀ x y → f x ≡ f y → x ≡ y) (xs : List A)
  → removeDups decB (mapList f xs) ≡ mapList f (removeDups decA xs)
removeDupMapList decA decB injf [] = refl
removeDupMapList decA decB {f} injf (x ∷ xs) with decMem decA x xs | decMem decB (f x) (mapList f xs)
... | yes p | yes q = removeDupMapList decA decB injf xs
... | yes (y , m , eq) | no ¬q = ⊥-rec (¬q (f y , ∈mapList m , cong f eq))
... | no ¬p | no ¬q = cong (f x ∷_) (removeDupMapList decA decB injf xs)
... | no ¬p | yes (y , m , eq) with pre∈mapList m
... | (x' , m' , eq') = ⊥-rec (¬p (x' , m' , injf _ _ (eq ∙ sym eq')))

-- duplicate-free lists
dupFree : {A : Type} → List A → Type
dupFree [] = Unit
dupFree (x ∷ xs) = (x ∈ xs → ⊥) × dupFree xs

-- duplicate-freeness is preserved under removal of elements
dupFreeRemove : {A : Type}
  → {xs : List A} {x : A} (m : x ∈ xs)
  → dupFree xs
  → dupFree (remove xs m)
dupFreeRemove here (p , dxs) = dxs
dupFreeRemove (there m) (p , dxs) =
  (λ m' → p (remove∈ m m')) , dupFreeRemove m dxs

dupFreeRemoveDups : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (xs : List A) → dupFree (removeDups decA xs)
dupFreeRemoveDups decA [] = tt
dupFreeRemoveDups decA (x ∷ xs) with decMem decA x xs
... | yes p = dupFreeRemoveDups decA xs
... | no ¬p = (λ q → ¬p (x , removeDups∈ decA xs q , refl)) , (dupFreeRemoveDups decA xs)
