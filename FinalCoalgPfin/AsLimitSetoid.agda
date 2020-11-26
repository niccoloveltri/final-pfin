{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalgPfin.AsLimitSetoid where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
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
open import FinalCoalgPfin.AsSetoid
open import Pfin.AsSetQuot

record ωChainS ℓ : Type (ℓ-suc ℓ) where
  constructor _,_
  field
    Ch : ℕ → Setoid ℓ
    pr : (n : ℕ) → Ch (suc n) →S Ch n
open ωChainS public

ωChainS₀ = ωChainS ℓ-zero

ωLimitS : ∀{ℓ} → ωChainS ℓ → Setoid ℓ
ωLimitS (S , π) =
  setoid (Σ[ x ∈ ((n : ℕ) → S n .Carr) ] (∀ n → S n .Rel (π n .mor (x (suc n))) (x n)))
         (λ l l' → ∀ n → S n .Rel (l .fst n) (l' .fst n))
         (λ l l' → isPropΠ (λ _ → S _ .propRel _ _))
         (equivRel (λ _ n → S n .eqrRel .reflexive _)
                   (λ _ _ r n → S n .eqrRel .symmetric _ _ (r n))
                   (λ _ _ _ r s n → S n .eqrRel .transitive _ _ _ (r n) (s n)))

projS : ∀{ℓ} (c : ωChainS ℓ) n → ωLimitS c →S c .Ch n
projS c n = (λ s → s .fst n) , λ sr → sr n

projRelS : ∀{ℓ} (c : ωChainS ℓ) n (x : ωLimitS c .Carr)
  → c .Ch n .Rel (c .pr n .mor (projS c (suc n) .mor x)) (projS c n .mor x)
projRelS c n x = x .snd n

∃upωLimit : ∀{ℓ} (c : ωChainS ℓ) (L : Setoid ℓ)
  → (f : ∀ n → L →S c .Ch n)
  → (∀ n (x : L .Carr) → c .Ch n .Rel (c .pr n .mor (f (suc n) .mor x)) (f n .mor x))
  → L →S ωLimitS c
∃upωLimit c L f p =
  (λ x → (λ n → f n .mor x) , λ n → p n x) ,
  λ r n → f n .morRel r

ωChainShiftS : ∀{ℓ} → ωChainS ℓ → ωChainS ℓ
ωChainShiftS (S , π) = (λ n → S (suc n)) , λ n → π (suc n)

iterPfinS : ℕ → Setoid₀ 
iterPfinS zero = UnitS
iterPfinS (suc n) = PfinS (iterPfinS n)

iterMapPfinS : ∀ n → iterPfinS (suc n) →S iterPfinS n
iterMapPfinS zero = bangS
iterMapPfinS (suc n) = mapPfinS (iterMapPfinS n)

iterPfinSeqS : ωChainS₀
iterPfinSeqS = iterPfinS , iterMapPfinS

ωPfinS : Setoid₀
ωPfinS = ωLimitS iterPfinSeqS

algωPfinS : PfinS ωPfinS →S ωPfinS
algωPfinS =
  ∃upωLimit iterPfinSeqS _
    (λ n → (λ xs → iterMapPfinS n .mor (mapPfinS (projS iterPfinSeqS n) .mor xs)) ,
            (λ rs → iterMapPfinS n .morRel (mapPfinS (projS iterPfinSeqS n) .morRel rs)))
    λ n xs →
      subst (λ x →  iterPfinS n .Rel
                              (iterMapPfinS n .mor x)
                              (iterMapPfinS n .mor (mapList (λ s → s .fst n) xs)))
            (sym (mapListComp xs))
            {!isPropDec!}
            --(iterPfinS n .eqrRel .reflexive _)

lengthAlgωPfinS : ∀ xs n → length (algωPfinS .mor xs .fst (suc n)) ≡ length xs
lengthAlgωPfinS xs n =
  lengthMapList (mapList (λ s → s .fst (suc n)) xs) ∙ lengthMapList xs


decIterPfinS : ∀ n xs ys → Dec (iterPfinS n .Rel xs ys)
decIterPfinS zero _ _ = yes tt
decIterPfinS (suc n) = decRelator (decIterPfinS n)

growingCh : ∀ n → iterPfinS n .Carr
growingCh zero = tt
growingCh (suc zero) = tt ∷ []
growingCh (suc (suc n)) = [] ∷ mapList sing (growingCh (suc n))

growingPr : ∀ n → iterPfinS n .Rel (iterMapPfinS n .mor (growingCh (suc n))) (growingCh n)
growingPr zero = tt
growingPr (suc zero) = 
  (λ { _ here → ∣ tt , here , tt ∣ ; _ (there m) → ∣ tt , m , tt ∣ }) ,
  (λ { _ here → ∣ tt , here , tt ∣ })
growingPr (suc (suc n)) with growingPr (suc n)
... | ih1 , ih2 =
  (λ { .[] here → ∣ _ , here , (λ { _ () }) , (λ { _ () }) ∣ ;
       ._ (there here) →
         ∥map∥ (λ { (ys , mys , r) → _ , there (∈mapList mys) ,
                  (λ { ._ here → ∣ _ , here , r ∣ }) ,
                  (λ { ._ here → ∣ _ , here , iterPfinS n .eqrRel .symmetric _ _ r ∣ }) })
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
                                  iterPfinS n .eqrRel .transitive _ _ _
                                    (subst (iterPfinS n .Rel xs')
                                           (∈sing (subst (xs' ∈_)
                                                  (sym (cong (mapList (iterMapPfinS n .mor)) eq' ∙ eq))
                                                  mxs'))
                                           (iterPfinS n .eqrRel .reflexive _))
                                    r ∣) ,
                  (λ { ._ here → ∣ _ , 
                                   subst (iterMapPfinS n .mor ys ∈_)
                                         (cong (mapList (iterMapPfinS n .mor)) eq' ∙ eq)
                                         here ,
                                   iterPfinS n .eqrRel .symmetric _ _ r ∣ }) })
              (ih1 _ (there (∈mapList mys))) }),
  (λ { .[] here → ∣ _ , here , (λ { _ () }) , (λ _ ()) ∣
     ; xs (there mxs) →
         let zs = pre∈mapList mxs .fst in
         let mzs = pre∈mapList mxs .snd .fst in
         let eq = pre∈mapList mxs .snd .snd in
         ∥map∥ (λ { (._ , here , r) → _ , there here ,
                    (λ ys mys → ∣ _ , here ,
                                  iterPfinS n .eqrRel .transitive _ _ _
                                    (subst (Rel (iterPfinS n) ys)
                                           (∈sing (subst (ys ∈_) (sym eq) mys))
                                           (iterPfinS n .eqrRel .reflexive _))
                                    r ∣) ,
                    (λ { ._ here → ∣ _ , subst (zs ∈_) eq here ,
                                     iterPfinS n .eqrRel .symmetric _ _ r ∣ })
                 ; (ys , there mys , r) →
                     let ws = pre∈mapList mys .fst in
                     let mws = pre∈mapList mys .snd .fst in
                     let eq' = pre∈mapList mys .snd .snd in
                     _ , there (there (∈mapList (∈mapList mws))) ,
                     (λ xs' mxs' → ∣ _ , here ,
                                     iterPfinS n .eqrRel .transitive _ _ _
                                       (subst (λ x → Rel (iterPfinS n) x ys) (sym (∈sing (subst (xs' ∈_) (sym eq) mxs'))) r)
                                       (subst (Rel (iterPfinS n) ys) (sym eq') (iterPfinS n .eqrRel .reflexive _)) ∣) ,
                     (λ { ._ here → ∣ _ , subst (zs ∈_) eq here ,
                                      iterPfinS n .eqrRel .transitive _ _ _
                                        (subst (λ x → Rel (iterPfinS n) x ys) (sym eq') (iterPfinS n .eqrRel .reflexive _))
                                        (iterPfinS n .eqrRel .symmetric _ _ r) ∣ }) })
               (ih2 _ mzs) })


growing : ωPfinS .Carr
growing = growingCh ,  growingPr

lengthGrowingCh : ∀ n → length (growingCh (suc n)) ≡ suc n
lengthGrowingCh zero = refl
lengthGrowingCh (suc n) = cong suc (lengthMapList (growingCh (suc n)) ∙ lengthGrowingCh n)

data Dup {A : Type} : List A → Type where
  here : ∀{x xs} → x ∈ xs → Dup (x ∷ xs)
  there : ∀{x xs} → Dup xs → Dup (x ∷ xs)

∈cons : {A : Type} {x y : A} {xs : List A}
  → x ∈ (y ∷ xs) → (x ≡ y) ⊎ x ∈ xs
∈cons here = _⊎_.inl refl
∈cons (there m) = _⊎_.inr m

{-
pre∈mapListInj : {A B : Type} {f : A → B} {x : A} {xs : List A}
  → f x ∈ mapList f xs → (∀ {x y} → f x ≡ f y → x ≡ y) → x ∈ xs
pre∈mapListInj {xs = x ∷ xs} m injf with ∈cons m
... | _⊎_.inl eq = subst (_∈ _) (sym (injf eq)) here
... | _⊎_.inr m' = there (pre∈mapListInj m' injf)

mapListDupInj : ∀{A B}{f : A → B}(xs : List A) → Dup (mapList f xs)
  → (∀ {x y} → f x ≡ f y → x ≡ y) → Dup xs
mapListDupInj (x ∷ xs) (here m) injf = here (pre∈mapListInj m injf)
mapListDupInj (x ∷ xs) (there d) injf = there (mapListDupInj xs d injf)

noDupGrowingCh : ∀ n → Dup (growingCh (suc n)) → ⊥
noDupGrowingCh zero (here ())
noDupGrowingCh zero (there ())
noDupGrowingCh (suc n) (here m) = ¬cons≡nil (pre∈mapList m .snd .snd)
noDupGrowingCh (suc n) (there d) =
  noDupGrowingCh n (mapListDupInj (growingCh (suc n)) d cons-inj₁)
-}

growingDistinct : ∀ n {x y} → x ∈ growingCh (suc n) → y ∈ growingCh (suc n)
  → iterPfinS n .Rel x y → x ≡ y
growingDistinct zero here here r = refl
growingDistinct (suc n) here here r = refl
growingDistinct (suc n) here (there q) r =
  ⊥-elim (∥rec∥ isProp⊥ (λ { (_ , () , _)} ) (r .snd _ (subst (pre∈mapList q .fst ∈_) (pre∈mapList q .snd .snd) here))) 
growingDistinct (suc n) (there p) here r =
  ⊥-elim (∥rec∥ isProp⊥ (λ { (_ , () , _)} ) (r .fst _ (subst (pre∈mapList p .fst ∈_) (pre∈mapList p .snd .snd) here))) 
growingDistinct (suc n) (there p) (there q) r with pre∈mapList p | pre∈mapList q
... | x , mx , eqx | y , my , eqy =
  sym eqx
  ∙ cong sing (growingDistinct n mx my
      (∥rec∥ (iterPfinS n .propRel _ _)
             (λ { (y' , my' , r') → iterPfinS n .eqrRel .transitive _ _ _ r'
                                              (subst (iterPfinS n .Rel y') (∈sing (subst (y' ∈_) (sym eqy) my'))
                                                     (iterPfinS n .eqrRel .reflexive _)) })
             (r .fst x (subst (x ∈_) eqx here))))
  ∙ eqy

lengthDistinct : ∀ n → iterPfinS (suc n) .Carr → ℕ
lengthDistinct n [] = zero
lengthDistinct n (x ∷ xs) with decMem (decIterPfinS n) x xs
... | yes p = lengthDistinct n xs
... | no ¬p = suc (lengthDistinct n xs)

remove : ∀{ℓ}{A : Type ℓ} {x : A} xs → x ∈ xs → List A
remove (x ∷ xs) here = xs
remove (y ∷ xs) (there m) = y ∷ remove xs m

remove∈ : ∀{ℓ}{A : Type ℓ} {x y : A} {xs} (m : x ∈ xs)
  → y ∈ remove xs m → y ∈ xs
remove∈ here m' = there m'
remove∈ (there m) here = here
remove∈ (there m) (there m') = there (remove∈ m m')

removeAll : ∀ n (x : iterPfinS n .Carr) (xs : iterPfinS (suc n) .Carr)
  → iterPfinS (suc n) .Carr
removeAll n x [] = []
removeAll n x (y ∷ xs) with decIterPfinS n x y
... | yes p = removeAll n x xs
... | no ¬p = y ∷ removeAll n x xs

∈removeAll : ∀ {n x y} (xs : iterPfinS (suc n) .Carr)
  → x ∈ xs → (iterPfinS n .Rel x y → ⊥)
  → x ∈ removeAll n y xs
∈removeAll {n} {y = y} (x ∷ xs) here r with decIterPfinS n y x
... | yes p = ⊥-elim (r (iterPfinS n .eqrRel .symmetric _ _ p))
... | no ¬p = here
∈removeAll {n} {y = y} (x ∷ xs) (there p) r with decIterPfinS n y x
... | yes q = ∈removeAll xs p r
... | no ¬q = there (∈removeAll xs p r)

lengthRemove : ∀{ℓ}{A : Type ℓ} {x : A} {xs} (m : x ∈ xs)
  → length xs ≡ suc (length (remove xs m))
lengthRemove here = refl
lengthRemove (there m) = cong suc (lengthRemove m)

{-
lengthDistinctRemove : ∀ n x (xs : iterPfinS (suc n) .Carr) (m : x ∈ xs)
  → (∀ y → y ∈ remove xs m → iterPfinS n .Rel x y → ⊥) 
  → lengthDistinct n xs ≡ suc (lengthDistinct n (remove xs m))
lengthDistinctRemove n x (x' ∷ xs) m p with decMem (decIterPfinS n) x' xs
lengthDistinctRemove n .x' (x' ∷ xs) here p | no ¬q = refl
lengthDistinctRemove n x (x' ∷ xs) (there m) p | no ¬q with decMem (decIterPfinS n) x' (remove xs m)
... | yes (y , my , r) = ⊥-elim (¬q (_ , remove∈ m my , r))
... | no ¬q' = cong suc (lengthDistinctRemove n x xs m (λ y my r → p _ (there my) r))
lengthDistinctRemove n .x' (x' ∷ xs) here p | yes (y , my , r) = ⊥-elim (p _ my r)
lengthDistinctRemove n x (x' ∷ xs) (there m) p | yes (y , my , r) with decMem (decIterPfinS n) x' (remove xs m)
... | yes (y' , my' , r') = lengthDistinctRemove n x xs m (λ _ mz rz → p _ (there mz) rz)
... | no ¬q = {!!}

lengthDistinct≤ : ∀ n (xs ys : iterPfinS (suc n) .Carr)
  → DRelator (iterPfinS n .Rel) xs ys 
  → lengthDistinct n xs ≤ lengthDistinct n ys
lengthDistinct≤ n [] ys r = zero-≤
lengthDistinct≤ n (x ∷ xs) ys r with decMem (decIterPfinS n) x xs
... | yes p = lengthDistinct≤ n xs ys (λ y m → r _ (there m))
lengthDistinct≤ n (x ∷ xs) ys r | no ¬p =
  ∥rec∥ m≤n-isProp
    (λ { (y , my , ry) → lem y my ry })
    (r _ here)
  where
    lem : ∀ y → y ∈ ys → iterPfinS n .Rel x y → suc (lengthDistinct n xs) ≤ lengthDistinct n ys
    lem y my ry with decMem (decIterPfinS n) y (removeAll n y ys)
    ... | yes (y' , my' , ry') =
      ≤-trans (suc-≤-suc (lengthDistinct≤ n xs (removeAll n y ys)
                                          (λ z mz → ∥map∥ (λ { (y' , my' , ry') →
                                                             y' ,
                                                             ∈removeAll ys my' (\ rz → ¬p (_ , mz , iterPfinS n .eqrRel .transitive _ _ _ ry
                                                                                                             (iterPfinS n .eqrRel .symmetric _ _
                                                                                                                        (iterPfinS n .eqrRel .transitive _ _ _ ry' rz)))) ,
                                                             ry'})
                                                          (r z (there mz))) ))
              {!!}
    ... | no ¬q = {!!}

lengthDistinct≤' : ∀ n (xs ys : iterPfinS (suc n) .Carr)
  → DRelator (iterPfinS n .Rel) xs ys
  → lengthDistinct n ys ≤ lengthDistinct n xs
lengthDistinct≤' n xs [] r = zero-≤
lengthDistinct≤' n xs (y ∷ ys) r with decMem (decIterPfinS n) y ys
... | yes p = {!!}
... | no ¬p = {!!}

sameLengthDistinct : ∀ n (xs ys : iterPfinS (suc n) .Carr)
  → Relator (iterPfinS n .Rel) xs ys
  → lengthDistinct n xs ≡ lengthDistinct n ys
sameLengthDistinct n xs ys r = {!!}
-}

dupFree : ∀ n (xs : iterPfinS (suc n) .Carr) → Type
dupFree n [] = Unit
dupFree n (x ∷ xs) = (∀ y → y ∈ xs → iterPfinS n .Rel x y → ⊥) × dupFree n xs

∈removeRel : ∀ n {xs : iterPfinS (suc n) .Carr} {x w}
  → (m : x ∈ xs) 
  → w ∈ xs → (iterPfinS n .Rel w x → ⊥)
  → w ∈ remove xs m
∈removeRel n here here ¬r = ⊥-elim (¬r (iterPfinS n .eqrRel .reflexive _))
∈removeRel n here (there mw) ¬r = mw
∈removeRel n (there mx) here ¬r = here
∈removeRel n (there mx) (there mw) ¬r = there (∈removeRel n mx mw ¬r)

dupFreeRemove : ∀ n {xs : iterPfinS (suc n) .Carr} {x}
  → (m : x ∈ xs) → dupFree n xs
  → dupFree n (remove xs m)
dupFreeRemove n here (p , dxs) = dxs
dupFreeRemove n (there m) (p , dxs) =
  (λ y my r → p {!!} {!∈remove!} {!!}) , dupFreeRemove n m dxs

≤LengthDistinct : ∀ n (xs ys : iterPfinS (suc n) .Carr)
  → DRelator (iterPfinS n .Rel) xs ys
  → dupFree n xs → dupFree n ys
  → length xs ≤ length ys
≤LengthDistinct n [] ys r tt dys = zero-≤
≤LengthDistinct n (x ∷ xs) ys r (p , dxs) dys =
  ∥rec∥ m≤n-isProp
    (λ { (y , my , ry) →
      ≤-trans (suc-≤-suc (≤LengthDistinct n xs (remove ys my)
                                          (λ z mz →
                                            ∥map∥ (λ { (w , mw , rw) →
                                                     w ,
                                                     ∈removeRel n my mw
                                                       (λ q → p z mz (iterPfinS n .eqrRel .transitive _ _ _ ry
                                                                                (iterPfinS n .eqrRel .transitive _ _ _ (iterPfinS n .eqrRel .symmetric _ _ q)
                                                                                           (iterPfinS n .eqrRel .symmetric _ _ rw)))) ,
                                                     rw })
                                                  (r z (there mz)))
                                          dxs {!!}))
              (subst (suc (length (remove ys my)) ≤_) (sym (lengthRemove my)) ≤-refl) })
    (r _ here)

sameLengthDistinct : ∀ n (xs ys : iterPfinS (suc n) .Carr)
  → Relator (iterPfinS n .Rel) xs ys
  → dupFree n xs → dupFree n ys
  → length xs ≡ length ys
sameLengthDistinct n xs ys r dxs dys = {!!}


noSurjAlgωPfinS : (xs : PfinS ωPfinS .Carr) → ωPfinS .Rel (algωPfinS .mor xs) growing → ⊥
noSurjAlgωPfinS xs p = {!p (suc (theN .fst)) !}
  where
    theN : Σ[ n ∈ ℕ ] length (algωPfinS .mor xs .fst (suc n)) < length (growingCh (suc n))
    theN = length xs ,
      subst (length (algωPfinS .mor xs .fst (suc (length xs))) <_) (sym (lengthGrowingCh (length xs)))
        (subst (_< suc (length xs)) (sym (lengthAlgωPfinS xs _)) ≤-refl)

-- proof:

-- 1) there must exists n : ℕ such that length (growingCh (suc n)) >
-- length (algωPfinS .mor xs .fst (suc n)) = length xs

-- 2) all elements of growingCh (suc n) are unrelated to each other,
-- so there must exists one which is not related to anything in
-- algωPfinS .mor xs .fst (suc n)

-- 3) absurd

-- []Ch : ∀ n → iterPfinS n .Carr
-- []Ch zero = tt
-- []Ch (suc n) = []

-- []Pr : ∀ n → iterPfinS n .Rel (iterMapPfinS n .mor []) ([]Ch n)
-- []Pr zero = tt
-- []Pr (suc n) = (λ { _ () }) , (λ { _ () })

-- ω[] : ωPfinS .Carr
-- ω[] = []Ch , []Pr

-- _ω++Ch_ :  (s s' : ∀ n → iterPfinS n .Carr) → ∀ n → iterPfinS n .Carr
-- (s ω++Ch s') zero = tt
-- (s ω++Ch s') (suc n) = s (suc n) ++ s' (suc n)

-- ω++Pr :  ∀ (s s' : ωPfinS .Carr) n
--   → iterPfinS n .Rel (iterMapPfinS n .mor (s .fst (suc n) ++ s' .fst (suc n))) ((s .fst ω++Ch s' .fst) n)
-- ω++Pr s s' zero = tt
-- ω++Pr (s , sr) (s' , sr') (suc n) = lem1 , lem2
--   where
--     lem1 : _
--     lem1 x mx with ++∈ {xs = s (suc (suc n))} (pre∈mapList mx .snd .fst)
--     ... | _⊎_.inl m =
--       ∥map∥ (λ { (y , my , r) → _ , ∈++₁ {xs = s (suc n)} my ,
--                                 iterPfinS n .eqrRel .transitive _ _ _
--                                           (subst (Rel (iterPfinS n) x) (sym (pre∈mapList mx .snd .snd))
--                                                  (iterPfinS n .eqrRel .reflexive _))
--                                           r })
--             (sr (suc n) .fst _ (∈mapList m)) 
--     ... | _⊎_.inr m = 
--       ∥map∥ (λ { (y , my , r) → _ , ∈++₂ {xs = s (suc n)} my ,
--                                 iterPfinS n .eqrRel .transitive _ _ _
--                                           (subst (Rel (iterPfinS n) x) (sym (pre∈mapList mx .snd .snd))
--                                                  (iterPfinS n .eqrRel .reflexive _))
--                                           r })
--             (sr' (suc n) .fst _ (∈mapList m)) 

--     lem2 : _
--     lem2 x mx with ++∈ {xs = s (suc n)} mx
--     ... | _⊎_.inl m =
--       ∥map∥ (λ { (y , my , r) → _ , subst (y ∈_) (sym (mapList++ (s (suc (suc n))) _)) (∈++₁ my) , r })
--             (sr (suc n) .snd _ m)
--     ... | _⊎_.inr m = 
--       ∥map∥ (λ { (y , my , r) → _ , subst (y ∈_) (sym (mapList++ (s (suc (suc n))) _)) (∈++₂ my) , r })
--             (sr' (suc n) .snd _ m)


-- _ω++_ :  ωPfinS .Carr → ωPfinS .Carr → ωPfinS .Carr
-- s ω++ s' = (s .fst ω++Ch s' .fst) , ω++Pr s s'

-- algωPfinMor : List (ωPfinS .Carr) → ωPfinS .Carr
-- algωPfinMor [] = ω[]
-- algωPfinMor (x ∷ xs) = x ω++ (algωPfinMor xs)

-- ∈algωPfinMor : ∀ {s} {y : ωPfinS .Carr} {n z} → y ∈ s
--   → z ∈ y .fst (suc n) → z ∈ algωPfinMor s .fst (suc n)
-- ∈algωPfinMor here mz = ∈++₁ mz
-- ∈algωPfinMor (there my) mz = ∈++₂ (∈algωPfinMor my mz)

-- algωPfinMor∈ : ∀ s {n} {x : iterPfinS n .Carr} 
--   → x ∈ algωPfinMor s .fst (suc n) → Σ[ y ∈ _ ] y ∈ s × x ∈ y .fst (suc n) 
-- algωPfinMor∈ ((t , tr) ∷ s) {n} mx with ++∈ {xs = t (suc n)} mx
-- ... | _⊎_.inl m = (t , tr) , here , m
-- ... | _⊎_.inr m with algωPfinMor∈ s m
-- ... | (y , my , mx') = y , there my , mx'

-- algωPfinMorRel' : ∀ s s' → DRelator (Rel ωPfinS) s s'
--   → ∀ n → DRelator (iterPfinS n .Rel) (algωPfinMor s .fst (suc n)) (algωPfinMor s' .fst (suc n))
-- algωPfinMorRel' (t ∷ s) [] p n x mx = ∥map∥ (λ { (_ , () , _) }) (p _ here)
-- algωPfinMorRel' ((t , tr) ∷ s) ((t' , tr') ∷ s') p n x mx with ++∈ {xs = t (suc n)} mx
-- ... | _⊎_.inl m =
--   ∥rec∥ propTruncIsProp
--     (λ { (._ , here , r) →
--          ∥map∥ (λ { (z , mz , r') → z , ∈++₁ mz , r' })
--               (r (suc n) .fst _ m)
--        ; (y , there my , r) →
--          ∥map∥ (λ { (z , mz , r') → z , ∈++₂ (∈algωPfinMor my mz) , r' })
--                (r (suc n) .fst _ m) })
--         (p _ here)
-- ... | _⊎_.inr m =
--   ∥rec∥ propTruncIsProp
--     (λ { (._ , here , r) →
--          ∥map∥ (λ { (z , mz , r') → z , ∈++₁ mz , r'})
--                (r (suc n) .fst _ (algωPfinMor∈ s m .snd .snd))
--        ; (y , there my , r) → 
--          ∥map∥ (λ { (z , mz , r') → z , ∈++₂ (∈algωPfinMor my mz) , r' })
--                (r (suc n) .fst _ (algωPfinMor∈ s m .snd .snd)) })
--     (p _ (there (algωPfinMor∈ s m .snd .fst)))



-- algωPfinMorRel : (s s' : List (ωPfinS .Carr))
--   → Relator (ωPfinS .Rel) s s'
--   → ∀ n → iterPfinS n .Rel (algωPfinMor s .fst n) (algωPfinMor s' .fst n)
-- algωPfinMorRel s s' r zero = tt
-- algωPfinMorRel s s' (p , q) (suc n) =
--   algωPfinMorRel' s s' p n , algωPfinMorRel' s' s q n

-- algωPfinS : PfinS ωPfinS →S ωPfinS
-- algωPfinS = algωPfinMor , algωPfinMorRel _ _


-- algωPfinMor-sing : ∀ s n →  (s ω++Ch []Ch) n ≡ s n
-- algωPfinMor-sing s zero = refl
-- algωPfinMor-sing s (suc n) = {!!}



-- PTrunc' : Type → Type
-- PTrunc' A = A / λ _ _ → Unit

-- →PTrunc' : ∀{A} → ∥ A ∥ → PTrunc' A
-- →PTrunc' = ∥rec∥ (elimProp2 (λ _ _ → squash/ _ _) (λ _ _ → eq/ _ _ _)) _/_.[_]

-- canon[]∈ : {A : Type}(xs : List (List A)) → [] ∈ xs → [] ∈ xs
-- canon[]∈ ([] ∷ xss) _ = here
-- canon[]∈ ((x ∷ xs) ∷ xss) (there m) = there (canon[]∈ xss m)

-- canon[]∈IsConst : {A : Type}(xs : List (List A))
--   → (p q : [] ∈ xs) → canon[]∈ xs p ≡ canon[]∈ xs q
-- canon[]∈IsConst ([] ∷ xss) p q = refl
-- canon[]∈IsConst ((x ∷ xs) ∷ xss) (there p) (there q) =
--   cong there (canon[]∈IsConst xss p q)

-- hStable[]∈' : {A : Type}(xs : List (List A)) → PTrunc' ([] ∈ xs) → [] ∈ xs
-- hStable[]∈' xs = recQ {!!} (canon[]∈ xs) (λ p q _ → canon[]∈IsConst xs p q)

-- hStable[]∈ : {A : Type}(xs : List (List A)) → ∥ [] ∈ xs ∥ → [] ∈ xs
-- hStable[]∈ xs m = hStable[]∈' xs (→PTrunc' m)

-- check : ∀ (y : ωPfinS .Carr) n → [] ∈ y .fst (suc (suc (suc n))) → [] ∈ y .fst (suc (suc n))
-- check y n m = hStable[]∈ _
--   (∥map∥ (λ { ([] , mx , r) → mx
--            ; (x ∷ x₁ , mx , r) → {!r .snd _ here --imp!} }) (y .snd (suc (suc n)) .fst [] (∈mapList m)))

-- noSurjAlgωPfinS : (t : PfinS ωPfinS .Carr) → ωPfinS .Rel (algωPfinS .mor t) growing → ⊥
-- --noSurjAlgωPfinS [] r = ∥rec∥ isProp⊥ (λ { (_ , () , _) }) (r 1 .snd tt here)
-- noSurjAlgωPfinS s r = {!!}
--   where
--     lem : ∀ n → [] ∈ algωPfinS .mor s .fst (suc (suc n))
--     lem n =
--       hStable[]∈ _ (∥rec∥ propTruncIsProp
--         (λ { ([] , mx , rx) → ∣ mx ∣
--           ; (x ∷ xs , mx , rx) → ∥map∥ (λ { (_ , () , _) }) (rx .snd _ here) })
--         (r (suc (suc n)) .snd _ here))

--     lem' : ∀ n → Σ[ y ∈ ωPfinS .Carr ] (y ∈ s) × [] ∈ y .fst (suc (suc n))
--     lem' n = algωPfinMor∈ s (lem n)

-- {-
-- noSurjAlgωPfinS [] r = ∥rec∥ isProp⊥ (λ { (_ , () , _) }) (r 1 .snd tt here)
-- noSurjAlgωPfinS ((t , tr) ∷ ts) r = {!!}
--   where
--     r' : ∀ n → DRelator (Relator (iterPfinS n .Rel)) ([] ∷ mapList sing (growingCh (suc n))) (t (suc (suc n)) ++ algωPfinMor ts .fst (suc (suc n)))
--     r' n = r (suc (suc n)) .snd

--     r'' : ∀ n → {!r' n _ here !}
--     r'' n = {!!}
-- -}
