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
open import Cubical.Data.Sum
open import Cubical.Data.List renaming (map to mapList; [_] to sing)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary hiding (Rel)
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

[]Ch : ∀ n → iterPfinS n .Carr
[]Ch zero = tt
[]Ch (suc n) = []

[]Pr : ∀ n → iterPfinS n .Rel (iterMapPfinS n .mor []) ([]Ch n)
[]Pr zero = tt
[]Pr (suc n) = (λ { _ () }) , (λ { _ () })

ω[] : ωPfinS .Carr
ω[] = []Ch , []Pr

_ω++Ch_ :  (s s' : ∀ n → iterPfinS n .Carr) → ∀ n → iterPfinS n .Carr
(s ω++Ch s') zero = tt
(s ω++Ch s') (suc n) = s (suc n) ++ s' (suc n)

ω++Pr :  ∀ (s s' : ωPfinS .Carr) n
  → iterPfinS n .Rel (iterMapPfinS n .mor (s .fst (suc n) ++ s' .fst (suc n))) ((s .fst ω++Ch s' .fst) n)
ω++Pr s s' zero = tt
ω++Pr (s , sr) (s' , sr') (suc n) = lem1 , lem2
  where
    lem1 : _
    lem1 x mx with ++∈ {xs = s (suc (suc n))} (pre∈mapList mx .snd .fst)
    ... | _⊎_.inl m =
      ∥map∥ (λ { (y , my , r) → _ , ∈++₁ {xs = s (suc n)} my ,
                                iterPfinS n .eqrRel .transitive _ _ _
                                          (subst (Rel (iterPfinS n) x) (sym (pre∈mapList mx .snd .snd))
                                                 (iterPfinS n .eqrRel .reflexive _))
                                          r })
            (sr (suc n) .fst _ (∈mapList m)) 
    ... | _⊎_.inr m = 
      ∥map∥ (λ { (y , my , r) → _ , ∈++₂ {xs = s (suc n)} my ,
                                iterPfinS n .eqrRel .transitive _ _ _
                                          (subst (Rel (iterPfinS n) x) (sym (pre∈mapList mx .snd .snd))
                                                 (iterPfinS n .eqrRel .reflexive _))
                                          r })
            (sr' (suc n) .fst _ (∈mapList m)) 

    lem2 : _
    lem2 x mx with ++∈ {xs = s (suc n)} mx
    ... | _⊎_.inl m =
      ∥map∥ (λ { (y , my , r) → _ , subst (y ∈_) (sym (mapList++ (s (suc (suc n))) _)) (∈++₁ my) , r })
            (sr (suc n) .snd _ m)
    ... | _⊎_.inr m = 
      ∥map∥ (λ { (y , my , r) → _ , subst (y ∈_) (sym (mapList++ (s (suc (suc n))) _)) (∈++₂ my) , r })
            (sr' (suc n) .snd _ m)


_ω++_ :  ωPfinS .Carr → ωPfinS .Carr → ωPfinS .Carr
s ω++ s' = (s .fst ω++Ch s' .fst) , ω++Pr s s'

algωPfinMor : List (ωPfinS .Carr) → ωPfinS .Carr
algωPfinMor [] = ω[]
algωPfinMor (x ∷ xs) = x ω++ (algωPfinMor xs)

∈algωPfinMor : ∀ {s} {y : ωPfinS .Carr} {n z} → y ∈ s
  → z ∈ y .fst (suc n) → z ∈ algωPfinMor s .fst (suc n)
∈algωPfinMor here mz = ∈++₁ mz
∈algωPfinMor (there my) mz = ∈++₂ (∈algωPfinMor my mz)

algωPfinMor∈ : ∀ s {n} {x : iterPfinS n .Carr} 
  → x ∈ algωPfinMor s .fst (suc n) → Σ[ y ∈ _ ] y ∈ s × x ∈ y .fst (suc n) 
algωPfinMor∈ ((t , tr) ∷ s) {n} mx with ++∈ {xs = t (suc n)} mx
... | _⊎_.inl m = (t , tr) , here , m
... | _⊎_.inr m with algωPfinMor∈ s m
... | (y , my , mx') = y , there my , mx'

algωPfinMorRel' : ∀ s s' → DRelator (Rel ωPfinS) s s'
  → ∀ n → DRelator (iterPfinS n .Rel) (algωPfinMor s .fst (suc n)) (algωPfinMor s' .fst (suc n))
algωPfinMorRel' (t ∷ s) [] p n x mx = ∥map∥ (λ { (_ , () , _) }) (p _ here)
algωPfinMorRel' ((t , tr) ∷ s) ((t' , tr') ∷ s') p n x mx with ++∈ {xs = t (suc n)} mx
... | _⊎_.inl m =
  ∥rec∥ propTruncIsProp
    (λ { (._ , here , r) →
         ∥map∥ (λ { (z , mz , r') → z , ∈++₁ mz , r' })
              (r (suc n) .fst _ m)
       ; (y , there my , r) →
         ∥map∥ (λ { (z , mz , r') → z , ∈++₂ (∈algωPfinMor my mz) , r' })
               (r (suc n) .fst _ m) })
        (p _ here)
... | _⊎_.inr m =
  ∥rec∥ propTruncIsProp
    (λ { (._ , here , r) →
         ∥map∥ (λ { (z , mz , r') → z , ∈++₁ mz , r'})
               (r (suc n) .fst _ (algωPfinMor∈ s m .snd .snd))
       ; (y , there my , r) → 
         ∥map∥ (λ { (z , mz , r') → z , ∈++₂ (∈algωPfinMor my mz) , r' })
               (r (suc n) .fst _ (algωPfinMor∈ s m .snd .snd)) })
    (p _ (there (algωPfinMor∈ s m .snd .fst)))



algωPfinMorRel : (s s' : List (ωPfinS .Carr))
  → Relator (ωPfinS .Rel) s s'
  → ∀ n → iterPfinS n .Rel (algωPfinMor s .fst n) (algωPfinMor s' .fst n)
algωPfinMorRel s s' r zero = tt
algωPfinMorRel s s' (p , q) (suc n) =
  algωPfinMorRel' s s' p n , algωPfinMorRel' s' s q n

algωPfinS : PfinS ωPfinS →S ωPfinS
algωPfinS = algωPfinMor , algωPfinMorRel _ _


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

{-
lengthGrowingCh : ∀ n → length (growingCh (suc n)) ≡ suc n
lengthGrowingCh zero = refl
lengthGrowingCh (suc n) = cong suc (lengthMapList (growingCh (suc n)) ∙ lengthGrowingCh n)
-}

PTrunc' : Type → Type
PTrunc' A = A / λ _ _ → Unit

→PTrunc' : ∀{A} → ∥ A ∥ → PTrunc' A
→PTrunc' = ∥rec∥ (elimProp2 (λ _ _ → squash/ _ _) (λ _ _ → eq/ _ _ _)) _/_.[_]

canon[]∈ : {A : Type}(xs : List (List A)) → [] ∈ xs → [] ∈ xs
canon[]∈ ([] ∷ xss) _ = here
canon[]∈ ((x ∷ xs) ∷ xss) (there m) = there (canon[]∈ xss m)

canon[]∈IsConst : {A : Type}(xs : List (List A))
  → (p q : [] ∈ xs) → canon[]∈ xs p ≡ canon[]∈ xs q
canon[]∈IsConst ([] ∷ xss) p q = refl
canon[]∈IsConst ((x ∷ xs) ∷ xss) (there p) (there q) =
  cong there (canon[]∈IsConst xss p q)

hStable[]∈' : {A : Type}(xs : List (List A)) → PTrunc' ([] ∈ xs) → [] ∈ xs
hStable[]∈' xs = recQ {!!} (canon[]∈ xs) (λ p q _ → canon[]∈IsConst xs p q)

hStable[]∈ : {A : Type}(xs : List (List A)) → ∥ [] ∈ xs ∥ → [] ∈ xs
hStable[]∈ xs m = hStable[]∈' xs (→PTrunc' m)

check : ∀ (y : ωPfinS .Carr) n → [] ∈ y .fst (suc (suc (suc n))) → [] ∈ y .fst (suc (suc n))
check y n m = hStable[]∈ _
  (∥map∥ (λ { ([] , mx , r) → mx
           ; (x ∷ x₁ , mx , r) → {!r .snd _ here --imp!} }) (y .snd (suc (suc n)) .fst [] (∈mapList m)))

noSurjAlgωPfinS : (t : PfinS ωPfinS .Carr) → ωPfinS .Rel (algωPfinS .mor t) growing → ⊥
--noSurjAlgωPfinS [] r = ∥rec∥ isProp⊥ (λ { (_ , () , _) }) (r 1 .snd tt here)
noSurjAlgωPfinS s r = {!!}
  where
    lem : ∀ n → [] ∈ algωPfinS .mor s .fst (suc (suc n))
    lem n =
      hStable[]∈ _ (∥rec∥ propTruncIsProp
        (λ { ([] , mx , rx) → ∣ mx ∣
          ; (x ∷ xs , mx , rx) → ∥map∥ (λ { (_ , () , _) }) (rx .snd _ here) })
        (r (suc (suc n)) .snd _ here))

    lem' : ∀ n → Σ[ y ∈ ωPfinS .Carr ] (y ∈ s) × [] ∈ y .fst (suc (suc n))
    lem' n = algωPfinMor∈ s (lem n)

{-
noSurjAlgωPfinS [] r = ∥rec∥ isProp⊥ (λ { (_ , () , _) }) (r 1 .snd tt here)
noSurjAlgωPfinS ((t , tr) ∷ ts) r = {!!}
  where
    r' : ∀ n → DRelator (Relator (iterPfinS n .Rel)) ([] ∷ mapList sing (growingCh (suc n))) (t (suc (suc n)) ++ algωPfinMor ts .fst (suc (suc n)))
    r' n = r (suc (suc n)) .snd

    r'' : ∀ n → {!r' n _ here !}
    r'' n = {!!}
-}
