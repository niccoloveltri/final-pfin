{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalgPfin.AsLimitSetoid where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Functions.Surjection
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients renaming ([_] to eqCl; rec to recQ)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.List renaming (map to mapList; [_] to sing)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary hiding (Rel)
open import Cubical.Relation.Nullary
open BinaryRelation
open isEquivRel
open import Preliminaries
open import Trees
open import ListRelations
open import FinalCoalgPfin.AsSetoid
open import Pfin.AsSetQuot

-- ω-chains of setoids
record ωChainS ℓ : Type (ℓ-suc ℓ) where
  constructor _,_
  field
    Ch : ℕ → Setoid ℓ
    res : (n : ℕ) → Ch (suc n) →S Ch n
open ωChainS public

ωChainS₀ = ωChainS ℓ-zero

-- the limit of a ω-chain
ωLimitCarr : ∀{ℓ} → ωChainS ℓ → Type ℓ
ωLimitCarr (S , π) =
  Σ[ x ∈ ((n : ℕ) → S n .Carr) ] ∀ n → S n .Rel (π n .mor (x (suc n))) (x n)

ωLimitRel : ∀{ℓ} (c : ωChainS ℓ) (l l' : ωLimitCarr c) → Type ℓ
ωLimitRel (S , _) l l' = ∀ n → S n .Rel (l .fst n) (l' .fst n)

ωLimitS : ∀{ℓ} → ωChainS ℓ → Setoid ℓ
ωLimitS C@(S , π) =
  setoid (ωLimitCarr C) (ωLimitRel C)
         (λ l l' → isPropΠ (λ _ → S _ .propRel _ _))
         (equivRel (λ _ n → S n .eqrRel .reflexive _)
                   (λ _ _ r n → S n .eqrRel .symmetric _ _ (r n))
                   (λ _ _ _ r s n → S n .eqrRel .transitive _ _ _ (r n) (s n)))

-- definition of cone for a ω-chain
isConeS : ∀{ℓ} → ωChainS ℓ → Setoid ℓ → Type ℓ
isConeS c S =
  Σ[ f ∈ (∀ n → S →S c .Ch n) ]
    (∀ n x → c .Ch n .Rel (c .res n .mor (f (suc n) .mor x)) (f n .mor x))

-- the limit is a cone
projS : ∀{ℓ} (c : ωChainS ℓ) n → ωLimitS c →S c .Ch n
projS c n = (λ s → s .fst n) , λ sr → sr n

projRelS : ∀{ℓ} (c : ωChainS ℓ) n (x : ωLimitS c .Carr)
  → c .Ch n .Rel (c .res n .mor (projS c (suc n) .mor x)) (projS c n .mor x)
projRelS c n x = x .snd n

isConeωLimitS : ∀{ℓ} (c : ωChainS ℓ) → isConeS c (ωLimitS c)
isConeωLimitS c = projS c , projRelS c

-- existence-part of the universal property of the limit:
-- given a setoid L which is cone, then there exists a setoid morphism
-- from L to the limit
∃upωLimit : ∀{ℓ} (c : ωChainS ℓ) (L : Setoid ℓ)
  → isConeS c L
  → L →S ωLimitS c
∃upωLimit c L (f , p) =
  (λ x → (λ n → f n .mor x) , λ n → p n x) ,
  λ r n → f n .morRel r

-- shifted chain
ωChainShiftS : ∀{ℓ} → ωChainS ℓ → ωChainS ℓ
ωChainShiftS (S , π) = (λ n → S (suc n)) , λ n → π (suc n)

-- the ω-chain of iterated applications of PfinS to the unit setoid
iPfinS : ℕ → Setoid₀ 
iPfinS zero = UnitS
iPfinS (suc n) = PfinS (iPfinS n)

iMapPfinS : ∀ n → iPfinS (suc n) →S iPfinS n
iMapPfinS zero = bangS
iMapPfinS (suc n) = mapPfinS (iMapPfinS n)

iPfinS-ch : ωChainS₀
iPfinS-ch = iPfinS , iMapPfinS

-- some convenient synonyms
iList : ℕ → Type
iList n = iPfinS n .Carr

iListRel : (n : ℕ) (xs ys : iList n) → Type
iListRel n = iPfinS n .Rel

reflIList : (n : ℕ) {xs : iList n} → iListRel n xs xs
reflIList n = iPfinS n .eqrRel .reflexive _

symIList : (n : ℕ) {xs ys : iList n}
  → iListRel n xs ys → iListRel n ys xs 
symIList n = iPfinS n .eqrRel .symmetric _ _

transIList : (n : ℕ) {xs ys zs : iList n}
  → iListRel n xs ys → iListRel n ys zs 
  → iListRel n xs zs
transIList n = iPfinS n .eqrRel .transitive _ _ _

iMapList : ∀ n → iList (suc n) → iList n
iMapList n = iMapPfinS n .mor

iMapListRel : ∀ n {xs ys : iList (suc n)}
  → Relator (iListRel n) xs ys → iListRel n (iMapList n xs) (iMapList n ys)
iMapListRel n = iMapPfinS n .morRel 

-- the limit of the ω-chain iPfinSeqS
ωPfinS : Setoid₀
ωPfinS = ωLimitS iPfinS-ch

-- this limit is an algebra for PfinS, which is given by the universal
-- property of the limit (i.e. PfinS ωPfinS is a cone)
isConePfinSωPfinS : isConeS iPfinS-ch (PfinS ωPfinS)
isConePfinSωPfinS =
  (λ n → (λ xs → iMapList n (mapPfinS (projS iPfinS-ch n) .mor xs)) ,
         (λ rs → iMapListRel n (mapPfinS (projS iPfinS-ch n) .morRel rs))) ,
  (λ n xs →
      subst (λ x →  iListRel n
                              (iMapList n x)
                              (iMapList n (mapList (λ s → s .fst n) xs)))
            (sym (mapListComp xs))
            (iMapListRel n (RelatorFunMapList _ _ (λ x → x .snd n) (symIList n) _)))


algωPfinS : PfinS ωPfinS →S ωPfinS
algωPfinS = ∃upωLimit iPfinS-ch _ isConePfinSωPfinS

-- the (n+1)-projections of the image of algωPfinS have fixed length,
-- given by the length of the input xs
lengthAlgωPfinS : ∀ xs n → length (algωPfinS .mor xs .fst (suc n)) ≡ length xs
lengthAlgωPfinS xs n =
  lengthMapList (mapList (λ s → s .fst (suc n)) xs) ∙ lengthMapList xs

-- Decidability of the relation iListRel 
decIListRel : ∀ n xs ys → Dec (iListRel n xs ys)
decIListRel zero _ _ = yes tt
decIListRel (suc n) = decRelator (decIListRel n)

-- We show that ωPfinS is not the final coalgebra of PfinS by proving
-- that the algebra algωPfinS is not surjective
module NoFinalCoalg where

-- given an iterated list xs, we construct a new list which is xs
-- containing at most one element in each equivalence class of
-- iListRel (this can be done since iListRel is decidable)
  removeDups : ∀ n (xs : iList (suc n)) → iList (suc n)
  removeDups n [] = []
  removeDups n (x ∷ xs) with decMem (decIListRel n) x xs
  ... | yes p = removeDups n xs
  ... | no ¬p = x ∷ removeDups n xs

-- some properties of removeDups
  removeDups∈ : ∀ n (xs : iList (suc n))
    → ∀{x} → x ∈ removeDups n xs → x ∈ xs
  removeDups∈ n (x ∷ xs) m with decMem (decIListRel n) x xs
  ... | yes p = there (removeDups∈ n xs m)
  removeDups∈ n (x ∷ xs) here | no ¬p = here
  removeDups∈ n (x ∷ xs) (there m) | no ¬p = there (removeDups∈ n xs m)
  
  lengthRemoveDups : ∀ n (xs : iList (suc n))
    → length (removeDups n xs) ≤ length xs
  lengthRemoveDups n [] = ≤-refl
  lengthRemoveDups n (x ∷ xs) with decMem (decIListRel n) x xs
  ... | yes p = ≤-suc (lengthRemoveDups n xs)
  ... | no ¬p = suc-≤-suc (lengthRemoveDups n xs)

  removeDupsRel : ∀ n (xs : iList (suc n))
    → iListRel (suc n) (removeDups n xs) xs
  removeDupsRel n [] = reflIList (suc n)
  removeDupsRel n (x ∷ xs) with decMem (decIListRel n) x xs
  removeDupsRel n (x ∷ xs) | yes (x' , mx' , rx') with removeDupsRel n xs
  ... | (q , r) =
    (λ x mx → ∥map∥ (λ { (y , my , ry) → y , there my , ry}) (q x mx)) ,
    (λ { ._ here →
            ∥map∥ (λ { (y , my , ry) → _ , my , transIList n rx' ry })
                  (r _ mx')
       ; y (there my) → r y my })
  removeDupsRel n (x ∷ xs) | no ¬p with removeDupsRel n xs
  ... | (q , r) =
    (λ { ._ here → ∣ _ , here , reflIList n ∣
        ; y (there my) → ∣ y , there (removeDups∈ n xs my) , reflIList n ∣ }) ,
    (λ { ._ here → ∣ _ , here , reflIList n ∣
       ; y (there my) → ∥map∥ (λ { (z , mz , rz) → _ , there mz , rz }) (r _ my) })

-- A predicate stating when an iterating list has at most one element
-- in each equivalence class of iListRel
  dupFree : ∀ n (xs : iList (suc n)) → Type
  dupFree n [] = Unit
  dupFree n (x ∷ xs) = (∀ y → y ∈ xs → iListRel n x y → ⊥) × dupFree n xs

-- removeDups is dupFree
  dupFreeRemoveDups : ∀ n (xs : iList (suc n))
    → dupFree n (removeDups n xs)
  dupFreeRemoveDups n [] = tt
  dupFreeRemoveDups n (x ∷ xs) with decMem (decIListRel n) x xs
  ... | yes p = dupFreeRemoveDups n xs
  ... | no ¬p = (λ y m r → ¬p (y , removeDups∈ n xs m , r)) , dupFreeRemoveDups n xs

-- the iterated list obtained by removing an element from a dupFree
-- iterated list is still dupFree
  dupFreeRemove : ∀ n {xs : iList (suc n)} {x}
    → (m : x ∈ xs) → dupFree n xs
    → dupFree n (remove xs m)
  dupFreeRemove n here (p , dxs) = dxs
  dupFreeRemove n (there m) (p , dxs) =
    (λ y my r → p _ (remove∈ m my) r) , dupFreeRemove n m dxs

-- given two dupFree iterated lists xs and ys, if for each x ∈ xs
-- there exists y ∈ ys which is iListRel-related to x, then the length
-- of xs is smaller or equal than the length of ys
  ≤lengthDupFree : ∀ n (xs ys : iList (suc n))
    → DRelator (iListRel n) xs ys
    → dupFree n xs → dupFree n ys
    → length xs ≤ length ys
  ≤lengthDupFree n [] ys r tt dys = zero-≤
  ≤lengthDupFree n (x ∷ xs) ys r (p , dxs) dys =
    ∥rec∥ m≤n-isProp
      (λ { (y , my , ry) →
        ≤-trans (suc-≤-suc (≤lengthDupFree n xs (remove ys my)
                                            (λ z mz →
                                              ∥map∥ (λ { (w , mw , rw) →
                                                       w ,
                                                       ∈removeRel (λ x → reflIList n {x}) my mw
                                                         (λ q → p z mz (transIList n ry
                                                                                  (transIList n (symIList n q)
                                                                                             (symIList n rw)))) ,
                                                       rw })
                                                    (r z (there mz)))
                                            dxs (dupFreeRemove n my dys)))
                (subst (suc (length (remove ys my)) ≤_) (sym (lengthRemove my)) ≤-refl) })
      (r _ here)

-- given two dupFree iterated lists xs and ys, if for each x ∈ xs
-- there exists y ∈ ys which is iListRel-related to x, and viceversa
-- starting from ys, then the xs and ys have the same length
  ≡lengthDupFree : ∀ n (xs ys : iList (suc n))
    → Relator (iListRel n) xs ys
    → dupFree n xs → dupFree n ys
    → length xs ≡ length ys
  ≡lengthDupFree n xs ys r dxs dys =
    ≤-antisym (≤lengthDupFree n _ _ (r .fst) dxs dys)
              (≤lengthDupFree n _ _ (r .snd) dys dxs)
    
  dupFreeMapSing : ∀ n (xs : iList (suc n))
    → dupFree n xs → dupFree (suc n) (mapList sing xs)
  dupFreeMapSing n [] dxs = tt
  dupFreeMapSing n (x ∷ xs) (p , dxs) =
    (λ y m r →
      ∥rec∥ isProp⊥
        (λ { (z , here , r') → p _ (pre∈mapList m .snd .fst) (symIList n r') })
        (r .snd _  (subst (pre∈mapList m .fst ∈_) (pre∈mapList m .snd .snd) here))) ,
    dupFreeMapSing n xs dxs

-- We show that the algebra algωPfinS is not surjective by giving an
-- element of ωPFinS which is not in the image of algωPfinS (This is a
-- classic counterexample, taken e.g. from the book "Initial Algebras,
-- Terminal Coalgebras, and the Theory of Fixed Points of Functors" by
-- Adámek, Milius and Moss.
  growing : ∀ n → iList n
  growing zero = tt
  growing (suc zero) = tt ∷ []
  growing (suc (suc n)) = [] ∷ mapList sing (growing (suc n))
  
  growingRel : ∀ n → iListRel n (iMapList n (growing (suc n))) (growing n)
  growingRel zero = tt
  growingRel (suc zero) = 
    (λ { _ here → ∣ tt , here , tt ∣ ; _ (there m) → ∣ tt , m , tt ∣ }) ,
    (λ { _ here → ∣ tt , here , tt ∣ })
  growingRel (suc (suc n)) with growingRel (suc n)
  ... | ih1 , ih2 =
    (λ { .[] here → ∣ _ , here , (λ { _ () }) , (λ { _ () }) ∣ ;
         ._ (there here) →
           ∥map∥ (λ { (ys , mys , r) → _ , there (∈mapList mys) ,
                    (λ { ._ here → ∣ _ , here , r ∣ }) ,
                    (λ { ._ here → ∣ _ , here , symIList n r ∣ }) })
                (ih1 _ here) ;
         xs (there (there mxs)) → 
           let zs = pre∈mapList mxs .fst in
           let mzs = pre∈mapList mxs .snd .fst in
           let eq = pre∈mapList mxs .snd .snd in
           let ys = pre∈mapList mzs .fst in
           let mys = pre∈mapList mzs .snd .fst in
           let eq' = pre∈mapList mzs .snd .snd in
           ∥map∥ (λ { (ws , mws , r) → _ , there (∈mapList mws) ,
                    (λ xs' mxs' → ∣ _ , here , 
                                    transIList n
                                      (subst (iListRel n xs')
                                             (∈sing (subst (xs' ∈_)
                                                    (sym (cong (mapList (iMapList n)) eq' ∙ eq))
                                                    mxs'))
                                             (reflIList n))
                                      r ∣) ,
                    (λ { ._ here → ∣ _ , 
                                     subst (iMapList n ys ∈_)
                                           (cong (mapList (iMapList n)) eq' ∙ eq)
                                           here ,
                                     symIList n r ∣ }) })
                (ih1 _ (there (∈mapList mys))) }),
    (λ { .[] here → ∣ _ , here , (λ { _ () }) , (λ _ ()) ∣
       ; xs (there mxs) →
           let zs = pre∈mapList mxs .fst in
           let mzs = pre∈mapList mxs .snd .fst in
           let eq = pre∈mapList mxs .snd .snd in
           ∥map∥ (λ { (._ , here , r) → _ , there here ,
                      (λ ys mys → ∣ _ , here ,
                                    transIList n
                                      (subst (iListRel n ys)
                                             (∈sing (subst (ys ∈_) (sym eq) mys))
                                             (reflIList n))
                                      r ∣) ,
                      (λ { ._ here → ∣ _ , subst (zs ∈_) eq here ,
                                       symIList n r ∣ })
                   ; (ys , there mys , r) →
                       let ws = pre∈mapList mys .fst in
                       let mws = pre∈mapList mys .snd .fst in
                       let eq' = pre∈mapList mys .snd .snd in
                       _ , there (there (∈mapList (∈mapList mws))) ,
                       (λ xs' mxs' → ∣ _ , here ,
                                       transIList n
                                         (subst (λ x → iListRel n x ys) (sym (∈sing (subst (xs' ∈_) (sym eq) mxs'))) r)
                                         (subst (iListRel n ys) (sym eq') (reflIList n)) ∣) ,
                       (λ { ._ here → ∣ _ , subst (zs ∈_) eq here ,
                                        transIList n
                                          (subst (λ x → iListRel n x ys) (sym eq') (reflIList n))
                                          (symIList n r) ∣ }) })
                 (ih2 _ mzs) })
  
  
  growingS : ωPfinS .Carr
  growingS = growing ,  growingRel

-- the "growing" sequence is indeed growing in size, moreover it does
-- not contain redundant elements wrt. iListRel
  lengthGrowingCh : ∀ n → length (growing (suc n)) ≡ suc n
  lengthGrowingCh zero = refl
  lengthGrowingCh (suc n) = cong suc (lengthMapList (growing (suc n)) ∙ lengthGrowingCh n)
  
  dupFreeGrowing : ∀ n → dupFree n (growing (suc n))
  dupFreeGrowing zero = (λ { _ () _ }) , tt
  dupFreeGrowing (suc n) =
    (λ { y m r →
      ∥rec∥ isProp⊥
        (λ { (z , () , r') })
        (r .snd _ (subst (pre∈mapList m .fst ∈_) (pre∈mapList m .snd .snd) here)) }) ,
    dupFreeMapSing n _ (dupFreeGrowing n)

  noSurjAlgωPfinS' : (xs : PfinS ωPfinS .Carr) → ωPfinS .Rel (algωPfinS .mor xs) growingS → ⊥
  noSurjAlgωPfinS' xs p = ¬m<m absurd
    where
      N : ℕ
      N = length xs
  
      zs = algωPfinS .mor xs .fst (suc N)
      ys = growing (suc N)
  
      ≡-lem : length ys ≡ length (removeDups N zs)
      ≡-lem =
        sym (≡lengthDupFree N _ _
                            (transIList (suc N) (removeDupsRel N zs) (p (suc N)))
                            (dupFreeRemoveDups N zs)
                            (dupFreeGrowing N))
  
  
      ≤-lem : length (removeDups N zs) ≤ length zs
      ≤-lem = lengthRemoveDups N zs
  
      <-lem : length zs < length ys
      <-lem = 
        subst (length zs <_) (sym (lengthGrowingCh N))
          (subst (_< suc N) (sym (lengthAlgωPfinS xs _)) ≤-refl)
  
      absurd : length ys < length ys
      absurd = ≤<-trans (≤-trans (subst (length ys ≤_) ≡-lem ≤-refl) ≤-lem) <-lem

  noSurjAlgωPfinS : isSurjectionS algωPfinS → ⊥
  noSurjAlgωPfinS surj = ∥rec∥ isProp⊥ (uncurry noSurjAlgωPfinS') (surj growingS)


