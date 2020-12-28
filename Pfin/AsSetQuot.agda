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
  renaming (rec to recQ; rec2 to recQ2)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 
open import Cubical.Data.Bool
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Preliminaries
open import ListRelations
open import Trees
open import Pfin.AsFreeJoinSemilattice
open import Relation.Nullary
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

-- many lemmata, mostly about about DRelator _≡_
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

List→Pfin++ : {A : Type}(xs ys : List A)
  → List→Pfin (xs ++ ys) ≡ List→Pfin xs ∪ List→Pfin ys
List→Pfin++ [] ys = sym (com _ _ ∙ nr _)
List→Pfin++ (x ∷ xs) ys = cong (η x ∪_) (List→Pfin++ xs ys) ∙ ass _ _ _

List→PfinRel : ∀{A}{xs ys : List A}
  → DRelator _≡_ xs ys → PfinDRel _≡_ (List→Pfin xs) (List→Pfin ys)
List→PfinRel p x mx =
  ∥rec∥ propTruncIsProp
    (λ mx' →
      ∥map∥ (λ { (y , my , eq) → (y , List→Pfin∈ _ my , eq) }) (p x mx'))
    (∈ₛList→Pfin _ mx)

-- the two presentation of finite powerset (as a quotient and as the
-- free join semilattice) are equal
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

-- action on functions of PfinQ
DRelatorMapList : {A B : Type} (f : A → B) {xs ys : List A}
  → DRelator _≡_ xs ys → DRelator _≡_ (mapList f xs) (mapList f ys)
DRelatorMapList f p x mx with pre∈mapList mx
... | y , my , eq =
  ∥map∥ (λ { (z , mz , eq') → _ , ∈mapList mz , sym eq ∙ cong f eq'}) (p y my)

mapPfinQ : ∀{A B} (f : A → B) → PfinQ A → PfinQ B
mapPfinQ f = recQ squash/ (λ xs → [ mapList f xs ])
  λ xs ys p → eq/ _ _ (DRelatorMapList f (p .fst) , DRelatorMapList f (p .snd))

{-
-- size

module _ {A : Type} (decEq : (x y : A) → Dec (x ≡ y)) where

  dec∈ : ∀ (x : A) xs → Dec (x ∈ xs)
  dec∈ x [] = no (λ ())
  dec∈ x (y ∷ xs) with decEq x y
  ... | yes p = yes (hereEq p)
  ... | no ¬p with dec∈ x xs
  ... | no ¬q = no (λ { here → ¬p refl ; (there m) → ¬q m })
  ... | yes p = yes (there p)

  lengthNoDup' : (n : ℕ) (xs : List A) → length xs ≤N n → ℕ
  lengthNoDup' zero [] eq = zero
  lengthNoDup' zero (x ∷ xs) eq = ⊥-elim {A = λ _ → ℕ} (snotz (≤-antisym {m = suc (length xs)} eq zero-≤))
  lengthNoDup' (suc n) [] eq = zero
  lengthNoDup' (suc n) (x ∷ xs) eq with dec∈ x xs
  ... | no ¬p = suc (lengthNoDup' n xs (pred-≤-pred eq))
  ... | yes p = lengthNoDup' n (remove xs p) (≤-trans (subst (length (remove xs p) ≤N_) (sym (lengthRemove p)) (≤-suc ≤-refl)) (pred-≤-pred eq))

  lengthNoDup : List A → ℕ
  lengthNoDup xs = lengthNoDup' (length xs) xs ≤-refl

  lengthNoDupEq' : (n : ℕ) (xs ys : List A)
    → (px : length xs ≤N n) (py : length ys ≤N n)
    → SameEls xs ys
    → lengthNoDup' n xs px ≡ lengthNoDup' n ys py
  lengthNoDupEq' zero [] [] px py s = refl
  lengthNoDupEq' zero [] (x ∷ ys) px py s = ⊥-elim {A = λ _ → zero ≡ ⊥-elim {A = λ _ → ℕ} (snotz (≤-antisym py zero-≤))} (snotz (≤-antisym {m = suc (length ys)} py zero-≤))
  lengthNoDupEq' zero (x ∷ xs) ys px py s = ⊥-elim {A = λ _ → ⊥-elim {A = λ _ → ℕ} (snotz (≤-antisym px zero-≤)) ≡ lengthNoDup' zero ys py} (snotz (≤-antisym {m = suc (length xs)} px zero-≤))
  lengthNoDupEq' (suc n) [] ys px py s = {!!}
  lengthNoDupEq' (suc n) (x ∷ xs) ys px py s with dec∈ x xs
  ... | no ¬m = {!!}
  ... | yes m = {!!}


  size : PfinQ A → ℕ
  size = recQ isSetℕ lengthNoDup {!!}
 

-}
