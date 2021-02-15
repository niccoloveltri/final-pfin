{-# OPTIONS --cubical --no-import-sorts #-}

module Pfin.AsSetQuot where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2; elim to elimQ)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 
open import Cubical.Data.Bool
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Basics
open import ListStuff
open import ListRelations
open import Trees
open import Pfin.AsFreeJoinSemilattice
open import Cubical.Data.Nat.Order hiding (eq) renaming (_≤_ to _≤N_)

-- the relation relating lists with the same elements
SameEls : {A : Type} → List A → List A → Type
SameEls = Relator _≡_

isPropSameEls : ∀{A} (xs ys : List A) → isProp (SameEls xs ys)
isPropSameEls = isPropRelator _ 

isEquivRelSameEls : ∀{A} → BinaryRelation.isEquivRel (SameEls {A})
isEquivRelSameEls =
  BinaryRelation.equivRel (reflRelator (λ _ → refl))
                          (λ _ _ r → r .snd , r .fst)
                          (λ _ _ _ → transRelator _∙_)
                          
-- finite powerset as a quotient of lists
PfinQ : Type → Type
PfinQ A = List A / SameEls

-- adding an element to a finite subset
_∷Q_ : ∀ {A} → A → PfinQ A → PfinQ A
_∷Q_ a = recQ squash/ (λ xs → [ a ∷ xs ])
  λ { xs ys (p , q) → eq/ _ _
    ((λ { x here → ∣ x , here , refl ∣ ; x (there m) → ∥map∥ (λ { (y , m' , eq) → y , there m' , eq }) (p x m) }) ,
     λ { x here → ∣ x , here , refl ∣ ; x (there m) → ∥map∥ (λ { (y , m' , eq) → y , there m' , eq }) (q x m) }) }

-- membership relation
_∈Q_ : ∀{A} → A → PfinQ A → hProp₀
_∈Q_ a = elimQ (λ _ → isSetHProp)
  (λ xs → ∥ a ∈ xs ∥ , propTruncIsProp)
  λ xs ys r → Σ≡Prop (λ _ → isPropIsProp)
    (hPropExt propTruncIsProp propTruncIsProp
      (∥rec∥ propTruncIsProp (λ m → ∥map∥ (λ { (x , m , eq) → subst (_∈ ys) (sym eq) m }) (r .fst _ m)))
      (∥rec∥ propTruncIsProp (λ m → ∥map∥ (λ { (x , m , eq) → subst (_∈ xs) (sym eq) m }) (r .snd _ m))))


-- turning a list into a finite subset
List→Pfin : ∀{A : Type} → List A → Pfin A
List→Pfin [] = ø
List→Pfin (x ∷ xs) = η x ∪ List→Pfin xs

-- this functions is a monoid morphism (turns ++ into ∪)
List→Pfin++ : {A : Type}(xs ys : List A)
  → List→Pfin (xs ++ ys) ≡ List→Pfin xs ∪ List→Pfin ys
List→Pfin++ [] ys = sym (com _ _ ∙ nr _)
List→Pfin++ (x ∷ xs) ys = cong (η x ∪_) (List→Pfin++ xs ys) ∙ ass _ _ _


-- properties of membership in the finite subset associated to a list
∈ₛList→Pfin : ∀{A : Type} (xs : List A){a : A}
  → ⟨ a ∈ₛ List→Pfin xs ⟩ → ∥ a ∈ xs ∥
∈ₛList→Pfin (x ∷ xs) = ∥rec∥ propTruncIsProp
  λ { (inj₁ p) → ∥map∥ (λ eq → subst (_∈ _) (sym eq) here) p
    ; (inj₂ p) → ∥map∥ there (∈ₛList→Pfin xs p)} 

List→Pfin∈ : ∀{A : Type} (xs : List A){a : A}
  → a ∈ xs → ⟨ a ∈ₛ List→Pfin xs ⟩
List→Pfin∈ (x ∷ xs) here = inl ∣ refl ∣
List→Pfin∈ (x ∷ xs) (there p) = inr (List→Pfin∈ xs p)


-- the two presentation of finite powerset (as a quotient and as the
-- free join semilattice) are equivalent
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
Pfin→PfinQ→Pfin {A} =
  elimPfinProp (λ _ → _ , trunc _ _) refl (λ _ → nr _)
    λ {s₁}{s₂} p q →
      lem (Pfin→PfinQ s₁) (Pfin→PfinQ s₂) ∙ cong₂ _∪_ p q
  where
    lem : (s₁ s₂ : PfinQ A)
      → PfinQ→Pfin (recQ2 squash/ (λ xs ys → [ xs ++ ys ]) _ _ s₁ s₂) ≡
         PfinQ→Pfin s₁ ∪ PfinQ→Pfin s₂
    lem = elimProp2 (λ _ _ → trunc _ _) List→Pfin++

Pfin≡PfinQ : ∀{A} → Pfin A ≡ PfinQ A
Pfin≡PfinQ =
  isoToPath (iso Pfin→PfinQ PfinQ→Pfin PfinQ→Pfin→PfinQ Pfin→PfinQ→Pfin)

-- PfinQ action on functions 
DRelatorMapList : {A B : Type} (f : A → B) {xs ys : List A}
  → DRelator _≡_ xs ys → DRelator _≡_ (mapList f xs) (mapList f ys)
DRelatorMapList f p x mx with pre∈mapList mx
... | y , my , eq =
  ∥map∥ (λ { (z , mz , eq') → _ , ∈mapList mz , sym eq ∙ cong f eq'}) (p y my)

mapPfinQ : ∀{A B} (f : A → B) → PfinQ A → PfinQ B
mapPfinQ f = recQ squash/ (λ xs → [ mapList f xs ])
  λ xs ys p → eq/ _ _ (DRelatorMapList f (p .fst) , DRelatorMapList f (p .snd))

mapPfinQComp : ∀{A B C} {g : B → C} {f : A → B} (x : PfinQ A)
  → mapPfinQ g (mapPfinQ f x) ≡ mapPfinQ (g ∘ f) x
mapPfinQComp = elimProp (λ _ → squash/ _ _)
  (λ xs → cong [_] (mapListComp xs))

pre∈mapPfinQ : {A B : Type} {f : A → B} {b : B} (s : PfinQ A)
  → ⟨ b ∈Q mapPfinQ f s ⟩ → ∃[ a ∈ A ] ⟨ a ∈Q s ⟩ × (f a ≡ b)
pre∈mapPfinQ = elimProp (λ _ → isPropΠ (λ _ → propTruncIsProp))
  λ xs → ∥map∥ (λ m → _ , ∣ pre∈mapList m .snd .fst ∣ , pre∈mapList m .snd .snd) 

-- the size of a finite subset, which we can define if the carrier
-- type has decidable equality
size : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → PfinQ A → ℕ
size decA = recQ isSetℕ
  (λ xs → length (removeDups decA xs))
  λ xs ys r → ≤-antisym (lengthDupFree (removeDups decA xs) (removeDups decA ys)
                                        (dupFreeRemoveDups decA xs) (dupFreeRemoveDups decA ys)
                                        λ x m → ∥map∥ (λ { (y , m , eq) → y , ∈removeDups decA ys m , eq}) (r .fst _ (removeDups∈ decA xs m)))
                         (lengthDupFree (removeDups decA ys) (removeDups decA xs)
                                        (dupFreeRemoveDups decA ys) (dupFreeRemoveDups decA xs)
                                        λ x m → ∥map∥ (λ { (y , m , eq) → y , ∈removeDups decA xs m , eq}) (r .snd _ (removeDups∈ decA ys m)))

-- the size of (x ∷Q s)
size∷Q' : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → {x : A} (xs : List A) → (∥ x ∈ xs ∥ → ⊥)
  → size decA (x ∷Q [ xs ]) ≡ suc (size decA [ xs ])
size∷Q' decA {x} xs m with decMem decA x xs
... | yes (x' , m' , eq) = ⊥-rec (m ∣ subst (_∈ xs) (sym eq) m' ∣)
... | no ¬p = refl

size∷Q : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
  → {x : A} (s : PfinQ A) → (⟨ x ∈Q s ⟩ → ⊥)
  → size decA (x ∷Q s) ≡ suc (size decA s)
size∷Q decA = elimProp (λ _ → isPropΠ (λ _ → isSetℕ _ _)) (size∷Q' decA)

-- the size of (mapPfinQ f s)
sizeMapPfinQ : {A B : Type} (decA : (x y : A) → Dec (x ≡ y))
  → (decB : (x y : B) → Dec (x ≡ y))
  → {f : A → B} (injf : ∀ x y → f x ≡ f y → x ≡ y) (s : PfinQ A)
  → size decB (mapPfinQ f s) ≡ size decA s
sizeMapPfinQ decA decB injf = elimProp (λ _ → isSetℕ _ _)
  (λ xs → cong length (removeDupMapList decA decB injf xs)
          ∙ lengthMapList (removeDups decA xs))



-- if path equality on A is decidable, then also path equality on PfinQ A
-- is decidable
PfinQDecEq' : {A : Type}
  → ((x y : A) → Dec (x ≡ y))
  → (xs ys : List A) → Dec (_≡_ {A = PfinQ A} [ xs ] [ ys ])
PfinQDecEq'  decA xs ys with decRelator decA xs ys
... | yes p = yes (eq/ _ _ p)
... | no ¬p = no (λ p → ¬p (effective isPropSameEls isEquivRelSameEls _ _ p))

PfinQDecEq : {A : Type}
  → ((x y : A) → Dec (x ≡ y))
  → (x y : PfinQ A) → Dec (x ≡ y)
PfinQDecEq decA =
  elimProp2 (λ _ _ → isPropDec (squash/ _ _))
             (PfinQDecEq' decA)




