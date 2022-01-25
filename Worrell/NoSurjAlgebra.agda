{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module Worrell.NoSurjAlgebra where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as Pr
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients renaming (rec to recQ; elimProp to elimQProp; elim to elimQ; elimProp2 to elimQProp2)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Data.Unit
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
open BinaryRelation
open import Worrell.Limits

-- A counterexample to the surjectivity of the PfinQ-algebra function
-- mQ : PfinQ VωQ → VωQ. This also shows that m : Pfin Vω → Vω is not
-- surjective.

-- a sequence of finite trees in which top-level branching is strictly
-- increasing
growing : ∀ n → iPfinQ n
growing zero = tt
growing (suc zero) = [ tt ∷ [] ]
growing (suc (suc n)) = [ [] ] ∷Q mapPfinQ (λ x → [ x ∷ [] ]) (growing (suc n))

-- an alternative but equivalent definition growing', for which is
-- easier to prove that it is in fact an element of VωQ
growing'-aux : ∀ n → iPfinQ (suc n) →  iPfinQ (suc (suc n))
growing'-aux n = 
  recQ squash/
       (λ xs → [ [ [] ] ∷ mapList (λ x → [ x ∷ [] ]) xs ])
       (λ xs ys r → eq/ _ _
         ((λ { .([ [] ]) here → ∣ _ , here , refl ∣ ;
                 x (there m) → ∥map∥ (λ { (y , m' , eq) → _ , there (∈mapList m') , sym (pre∈mapList m .snd .snd) ∙ cong (λ z →  [ z ∷ [] ]) eq }) (r .fst _ (pre∈mapList m .snd .fst)) }) ,
          λ { .([ [] ]) here → ∣ _ , here , refl ∣ ;
                x (there m) → ∥map∥ (λ { (y , m' , eq) → _ , there (∈mapList m') , sym (pre∈mapList m .snd .snd) ∙ cong (λ z →  [ z ∷ [] ]) eq }) (r .snd _ (pre∈mapList m .snd .fst)) }))


growing' : ∀ n → iPfinQ n
growing' zero = tt
growing' (suc zero) = [ tt ∷ [] ]
growing' (suc (suc n)) = growing'-aux n (growing' (suc n))

growing≡growing' : ∀ n → growing n ≡ growing' n
growing≡growing' zero = refl
growing≡growing' (suc zero) = refl
growing≡growing' (suc (suc n)) =
  elimQProp {P = λ x → ([ [] ] ∷Q mapPfinQ (λ x → [ x ∷ [] ]) x) ≡ growing'-aux n x}
            (λ _ → squash/ _ _)
            (λ _ → refl)
            (growing (suc n)) 
  ∙ cong (growing'-aux n) (growing≡growing' (suc n))

growingEq' : ∀ n → iMapPfinQ n (growing' (suc n)) ≡ growing' n
growingEq' zero = refl
growingEq' (suc zero) = eq/ _ _
  ((λ { _ here → ∣ tt , here , refl ∣ ; _ (there m) → ∣ tt , m , refl ∣ }) ,
   λ { _ here → ∣ tt , here , refl ∣ })
growingEq' (suc (suc n)) =
  elimQProp {P = λ x → mapPfinQ (mapPfinQ (iMapPfinQ n)) ((growing'-aux (suc n) (growing'-aux n x))) ≡ growing'-aux n (mapPfinQ (iMapPfinQ n) (growing'-aux n x))}
            (λ _ → squash/ _ _)
            (λ xs →
              cong [_] (cong (λ z → [ [] ] ∷ [ iMapPfinQ n [ [] ] ∷ [] ] ∷ z) (mapListComp (mapList (λ x → [ x ∷ [] ]) xs)))
              ∙ cong [_] (cong (λ z → [ [] ] ∷ [ iMapPfinQ n [ [] ] ∷ [] ] ∷ z) (mapListComp xs))
              ∙ cong [_] (cong (λ z → [ [] ] ∷ [ iMapPfinQ n [ [] ] ∷ [] ] ∷ z) (sym (mapListComp xs)))
              ∙ cong [_] (cong (λ z → [ [] ] ∷ [ iMapPfinQ n [ [] ] ∷ [] ] ∷ z) (sym (mapListComp (mapList (λ x → [ x ∷ [] ]) xs)))))
            (growing' (suc n))
  ∙ cong (growing'-aux n) (growingEq' (suc n))            

growingEq : ∀ n → iMapPfinQ n (growing (suc n)) ≡ growing n
growingEq n =
  cong (iMapPfinQ n) (growing≡growing' (suc n))
  ∙ growingEq' n
  ∙ sym (growing≡growing' n)

-- growing is an element of VωQ
growing-ch : VωQ
growing-ch = growing , growingEq

-- the growing sequence is in fact growing:
-- the size of (growing (suc n)) is (suc n)
sizeGrowing : ∀ n → size (iPfinQDecEq _) (growing (suc n)) ≡ suc n
sizeGrowing zero = refl
sizeGrowing (suc n) =
  size∷Q (iPfinQDecEq _) (mapPfinQ (λ x → [ x ∷ [] ]) (growing (suc n)))
         (λ p → ∥rec∥ isProp⊥
                      (λ { (s , m , eq) → ∥rec∥ isProp⊥
                                                (λ { (_ , () , _) })
                                                (effective isPropSameEls isEquivRelSameEls _ _ eq .fst _ here) })
                      (pre∈mapPfinQ (growing (suc n)) p))
  ∙ cong suc (sizeMapPfinQ (iPfinQDecEq _) (iPfinQDecEq _) (inj[x∷[]] n) (growing (suc n)))
  ∙ cong suc (sizeGrowing n)
  where
    inj[x∷[]] : ∀ n (x y : iPfinQ n) → _≡_ {A = PfinQ (iPfinQ n)} [ x ∷ [] ] [ y ∷ [] ] → x ≡ y 
    inj[x∷[]] zero _ _ _ = refl
    inj[x∷[]] (suc n) = elimQProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
      λ xs ys r → eq/ _ _
        (∥rec∥ (isPropSameEls _ _)
               (λ { (.([ ys ]) , here , eq) → effective isPropSameEls isEquivRelSameEls _ _ eq })
               (effective isPropSameEls isEquivRelSameEls _ _ r .fst _ here)) 

-- growing is not in the image of mQ:
-- there is no element s : PfinQ VωQ such that (mQ s ≡ growing-ch).
-- Therefore mQ is not surjective
noSurjAlg' : (xs : List VωQ) → mQ [ xs ] ≡ growing-ch → ⊥
noSurjAlg' xs eq = ¬m<m absurd
  where
    N : ℕ
    N = length xs

    zs : PfinQ (iPfinQ N)
    zs = [ mapList (λ x → iMapPfinQ N (x .fst (suc N))) xs ]

    ys : PfinQ (iPfinQ N)
    ys = growing (suc N)

    szs≡sys : size (iPfinQDecEq _) zs ≡ size (iPfinQDecEq _) ys
    szs≡sys = cong (size (iPfinQDecEq _)) (sym (cong [_] (mapListComp xs)) ∙ funExt⁻ (cong fst eq) (suc N))

    szs≤N : size (iPfinQDecEq _) zs ≤N N
    szs≤N = ≤-trans (lengthRemoveDups (iPfinQDecEq _) (mapList (λ x → iMapPfinQ N (x .fst (suc N))) xs))
                    (subst (_≤N N) (sym (lengthMapList xs)) ≤-refl)

    sys≡sucN : size (iPfinQDecEq _) ys ≡ suc N
    sys≡sucN = sizeGrowing N

    absurd : N < N
    absurd = subst (_≤N N) (szs≡sys ∙ sys≡sucN) szs≤N

noSurjAlg : (s : PfinQ VωQ) → mQ s ≡ growing-ch → ⊥
noSurjAlg = elimQProp (λ _ → isPropΠ (λ _ → isProp⊥)) noSurjAlg'
