{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalgPfin.Set.AsLimit where

open import Size
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients renaming (rec to recQ)
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to mapList) hiding ([_])
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Data.Nat renaming (elim to elimNat)
open import Cubical.Data.Nat.Order hiding (eq) renaming (_≤_ to _≤N_; _≟_ to _≟N_)
open import Cubical.Data.Bool 
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂; rec to rec⊎; elim to elim⊎)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Preliminaries
open import ListRelations
open import Pfin.AsFreeJoinSemilattice
open BinaryRelation

-- ω-chains
record ωChain ℓ : Type (ℓ-suc ℓ) where
  constructor _,_
  field
    Ch : ℕ → Type ℓ
    res : (n : ℕ) → Ch (suc n) → Ch n
open ωChain public

ωChain₀ = ωChain ℓ-zero

-- the limit of a ω-chain
ωLimit : ∀{ℓ} → ωChain ℓ → Type ℓ
ωLimit (A , r) =
  Σ[ x ∈ ((n : ℕ) → A n) ] ∀ n → r n (x (suc n)) ≡ x n

-- definition of cone for a ω-chain
Cone : ∀{ℓ} → ωChain ℓ → Type ℓ → Type ℓ
Cone (A , r) C =
  Σ[ f ∈ (∀ n → C → A n) ] ∀ n x → r n (f (suc n) x) ≡ f n x

-- Cone : ∀{ℓ} → ωChain ℓ → Type (ℓ-suc ℓ)
-- Cone c = Σ[ C ∈ Type _ ] isCone c C

-- -- cone morphisms
-- 
-- ConeMap : ∀{ℓ} (c : ωChain ℓ) (C1 C2 : Cone c) → Type ℓ
-- ConeMap c (C1 , f1 , eq1) (C2 , f2 , eq2) =
--   Σ[ g ∈ (C1 → C2) ] ∀ n x → f2 n (g x) ≡ f1 n x

-- the limit is a cone
proj : ∀{ℓ} (c@(A , r) : ωChain ℓ) n → ωLimit c → A n
proj (A , r) n (x , eq) = x n

ConeωLimit : ∀{ℓ} (c : ωChain ℓ) → Cone c (ωLimit c)
ConeωLimit c@(A , r) = proj c , λ n x → x .snd n


AdjLim : ∀{ℓ} (c : ωChain ℓ) (C : Type ℓ)
  → Iso (C → ωLimit c) (Cone c C)
AdjLim (A , r) C = iso
  (λ g → (λ n x → g x .fst n) , λ n x → g x .snd n)
  (λ h@(f , eq) x → (λ n → f n x) , (λ n → eq n x))
  (λ _ → refl)
  (λ g → funExt (λ _ → refl))

{-
lem-injective-lim2 : ∀{ℓ} (c : ωChain ℓ) (C : Type ℓ)
  → (g : C → ωLimit c)
  → ∀ x y → (∀ n → Iso.fun (AdjLim c C) g .fst n x ≡ Iso.fun (AdjLim c C) g .fst n y)
  → g x ≡ g y
lem-injective-lim2 c C g x y p =
  Σ≡Prop (λ _ → isPropΠ λ _ → {!!}) (funExt p)
-}

lem-injective-lim : ∀{ℓ} (c : ωChain ℓ) (C : Type ℓ)
  → (g : C → ωLimit c)
  → (∀ x y → (∀ n → Iso.fun (AdjLim c C) g .fst n x ≡ Iso.fun (AdjLim c C) g .fst n y) → x ≡ y)
  → ∀ x y → g x ≡ g y → x ≡ y
lem-injective-lim c C g p x y eq = p x y (funExt⁻ (cong fst eq))

-- existence-part of the universal property of the limit: given a type
-- L which is a cone, then there exists a map from L to the limit
∃upωLimit : ∀{ℓ} (c : ωChain ℓ) (L : Type ℓ)
  → Cone c L
  → L → ωLimit c
∃upωLimit c L = Iso.inv (AdjLim c L)

-- shifted chain
shift : ∀{ℓ} → ωChain ℓ → ωChain ℓ
shift (A , r) = (λ n → A (suc n)) , λ n → r (suc n)

shift-iso : ∀{ℓ} (c : ωChain ℓ)
  → (∀ n → isSet (c .Ch n))
  → Iso (ωLimit c) (ωLimit (shift c))
shift-iso c@(A , r) cS =
  iso (Iso.inv (AdjLim (shift c) _) cone-sh)
      (Iso.inv (AdjLim c _) cone)
      (λ { (x , p) → Σ≡Prop (λ _ → isPropΠ (λ n → cS (suc n) _ _)) (λ i n → p n i) })
      λ { (x , p) → Σ≡Prop (λ _ → isPropΠ (λ n → cS n _ _)) (λ i n → p n i) }
  where
    cone-sh : Cone (shift c) (ωLimit c)
    cone-sh = (λ n x → x .fst (suc n)) , λ n x → x .snd (suc n)

    cone : Cone c (ωLimit (shift c))
    cone = (λ n x → r n (x .fst n)) , λ n x → cong (r n) (x .snd n)


shift≃ : ∀{ℓ} (c : ωChain ℓ) 
  → (∀ n → isSet (c .Ch n))
  → ωLimit c ≃ ωLimit (shift c)
shift≃ c cS = isoToEquiv (shift-iso c cS)

≤-suc-cases : ∀ k n → k ≤N suc n
  → (k ≤N n) ⊎ (k ≡ suc n)
≤-suc-cases zero n le = inj₁ zero-≤
≤-suc-cases (suc k) zero le = inj₂ (cong suc (≤0→≡0 (pred-≤-pred le)))
≤-suc-cases (suc k) (suc n) le with ≤-suc-cases k n (pred-≤-pred le)
... | inj₁ p = inj₁ (suc-≤-suc p)
... | inj₂ p = inj₂ (cong suc p)

ires : ∀{ℓ} (c : ωChain ℓ)
  → ∀ n k → k ≤N n
  → c .Ch n → c .Ch k
ires c zero k le y = J (λ k _ → c .Ch k) y (sym (≤0→≡0 le))
ires c (suc n) k le y with ≤-suc-cases k n le
... | inj₁ p = ires c n k p (c .res n y)
... | inj₂ p = J (λ k _ → c .Ch k) y (sym p)

ires-eq : ∀{ℓ} (c : ωChain ℓ) (x : ωLimit c)
  → ∀ n k (le : k ≤N n)
  → ires c n k le (x .fst n) ≡ x .fst k
ires-eq c x zero k le =
  J (λ k eq → J (λ k _ → c .Ch k) (x .fst 0) eq ≡ x .fst k) (JRefl (λ k _ → c .Ch k) (x .fst 0)) (sym (≤0→≡0 le))
ires-eq c x (suc n) k le with ≤-suc-cases k n le
... | inj₁ p = cong (ires c n k p) (x .snd n) ∙ ires-eq c x n k p
... | inj₂ p = J (λ k eq → J (λ k _ → c .Ch k) (x .fst (suc n)) eq ≡ x .fst k) (JRefl (λ k _ → c .Ch k) (x .fst (suc n))) (sym p)

-- the ω-chain of iterated applications of Pfin to the unit type
iPfin : ℕ → Type 
iPfin zero = Unit
iPfin (suc n) = Pfin (iPfin n)

isSetiPfin : ∀ n → isSet (iPfin n)
isSetiPfin zero = λ _ _ _ _ → refl
isSetiPfin (suc n) = trunc

iMapPfin : ∀ n → iPfin (suc n) → iPfin n
iMapPfin zero = λ _ → tt
iMapPfin (suc n) = mapPfin (iMapPfin n)

iPfin-ch : ωChain₀
iPfin-ch = iPfin , iMapPfin

-- the limit of the ω-chain iPfin-ch
ωPfin : Type
ωPfin = ωLimit iPfin-ch

isSetωPfin : isSet ωPfin
isSetωPfin =
  isSetΣ (isSetΠ (λ _ → isSetiPfin _))
         (λ _ → isProp→isSet (isPropΠ (λ _ → isSetiPfin _ _ _)))

-- the limit of the shifted ω-chain
ωPfinSh : Type
ωPfinSh = ωLimit (shift iPfin-ch)


-- this limit is an algebra for Pfin, which is given by the universal
-- property of the limit (i.e. Pfin ωPfin is a cone)
ConePfinωPfin : Cone iPfin-ch (Pfin ωPfin)
ConePfinωPfin =
  (λ n x → iMapPfin n (mapPfin (proj iPfin-ch n) x)) ,
  λ n x → cong (iMapPfin n)
    (mapPfinComp x ∙ cong (λ f → mapPfin f x)
      (funExt (λ y → y .snd n)))

m : Pfin ωPfin → ωPfin
m = Iso.inv (AdjLim iPfin-ch _) ConePfinωPfin

-- m is injective(??)

decIsProp : {A : Type}
  → isProp A
  → isProp (Dec A)
decIsProp propA (yes p) (yes q) = cong yes (propA _ _)
decIsProp propA (yes p) (no ¬p) = ⊥-elim {A = λ _ → yes p ≡ no ¬p} (¬p p)
decIsProp propA (no ¬p) (yes p) = ⊥-elim {A = λ _ → no ¬p ≡ yes p} (¬p p)
decIsProp propA (no ¬p) (no ¬q) = cong no (funExt (λ _ → isProp⊥ _ _))

decPropTrunc : {A : Type} → Dec A → Dec ∥ A ∥ 
decPropTrunc (yes a) = yes ∣ a ∣
decPropTrunc (no ¬a) = no (∥rec∥ isProp⊥ ¬a)

dec∈ₛ : {A : Type}
  → ((x y : A) → Dec (x ≡ y))
  → (x : A) (s : Pfin A) → Dec ⟨ x ∈ₛ s ⟩
dec∈ₛ decEq x = elimPfinProp
  (λ s → _ , decIsProp (snd (x ∈ₛ s)))
  (no λ x → x)
  (λ a → decPropTrunc (decEq x a)) 
  λ {s1}{s2} → lem {s1}{s2}
  where
    lem : ∀{s1 s2} → Dec ⟨ x ∈ₛ s1 ⟩ → Dec ⟨ x ∈ₛ s2 ⟩
      → Dec ⟨ x ∈ₛ (s1 ∪ s2) ⟩
    lem (yes p) d2 = yes (inl p)
    lem (no ¬p) (yes p) = yes (inr p)
    lem (no ¬p) (no ¬q) = no (∥rec∥ isProp⊥
      (λ { (inj₁ x) → ¬p x ; (inj₂ x) → ¬q x }))

dec⊆ : {A : Type}
  → ((x y : A) → Dec (x ≡ y))
  → (s t : Pfin A) → Dec (s ⊆ t)
dec⊆ {A} decEq =
  elimPfinProp (λ _ → _ , isPropΠ λ x → isPropDec (isPropΠ (λ y → isPropΠ (λ _ → snd (y ∈ₛ x)))))
    (λ t → yes (λ { _ () }))
    (λ a → lem' {a})
    λ {s1}{s2} d1 d2 t → lem {s1} {s2} t (d1 t) (d2 t)  
  where
    lem' : ∀ {a : A} t → Dec (η a ⊆ t)
    lem' {a} t with dec∈ₛ decEq a t
    ... | yes p = yes (λ y → ∥rec∥ (snd (y ∈ₛ t)) (λ eq → subst (λ z → ⟨ z ∈ₛ t ⟩) (sym eq) p))
    ... | no ¬p = no (λ q → ¬p (q _ ∣ refl ∣))

    lem : ∀ {s1 s2 : Pfin A} t
      → Dec (s1 ⊆ t) → Dec (s2 ⊆ t)
      → Dec ((s1 ∪ s2) ⊆ t)
    lem {s1}{s2} t (yes p) (yes q) = yes (∪⊆ s1 s2 t p q)
    lem t (yes p) (no ¬p) = no (λ q → ¬p λ x mx → q x (inr mx))
    lem t (no ¬p) d2 = no (λ q → ¬p (λ x mx → q x (inl mx)))

PfinDecEq : {A : Type}
  → ((x y : A) → Dec (x ≡ y))
  → (x y : Pfin A) → Dec (x ≡ y)
PfinDecEq decEq x y with dec⊆ decEq x y | dec⊆ decEq y x
... | yes p | yes q = yes (antisym⊆ p q)
... | yes p | no ¬q = no (λ eq → ¬q (λ a → subst (λ z → ⟨ a ∈ₛ z ⟩) (sym eq)))
... | no ¬p | _ = no (λ eq → ¬p (λ a → subst (λ z → ⟨ a ∈ₛ z ⟩) eq))

iPfinDecEq : ∀ n (x y : iPfin n) → Dec (x ≡ y)
iPfinDecEq zero x y = yes refl
iPfinDecEq (suc n) = PfinDecEq (iPfinDecEq n)

{-
ω+1Pfin : Type
ω+1Pfin = Σ[ x ∈ ωPfin ] (∀ n → {!!})

ω+1Pfin→PfinωPfin : ω+1Pfin → Pfin ωPfin
ω+1Pfin→PfinωPfin ((x , r) , eq) = {!!}
-}

growing : ∀ n → iPfin n
growing zero = tt
growing (suc zero) = η tt ∪ ø
growing (suc (suc n)) = η ø ∪ mapPfin η (growing (suc n))

growingEq : ∀ n → iMapPfin n (growing (suc n)) ≡ growing n
growingEq zero = refl
growingEq (suc zero) =
  ass _ _ _ ∙ cong (_∪ ø) (idem _)
growingEq (suc (suc n)) =
  cong (η ø ∪_)
    (cong (η (η (iMapPfin n ø)) ∪_)
      (mapPfinComp (mapPfin η (growing (suc n)))
       ∙ mapPfinComp (growing (suc n))
       ∙ sym (mapPfinComp (growing (suc n)))
       ∙ sym (mapPfinComp (mapPfin η (growing (suc n)))))
    ∙ cong (mapPfin η) (growingEq (suc n)))

growing-ch : ωPfin
growing-ch = growing , growingEq




{-
iPfinEmb : ∀ k n → k ≤N n → iPfin k → iPfin n
iPfinEmb k zero le x = tt
iPfinEmb k (suc zero) le x = η tt ∪ ø
iPfinEmb k (suc (suc n)) le x =
  rec⊎ (λ le' → mapPfin η (iPfinEmb k (suc n) le' x))
       (λ eq → subst iPfin eq x)
       (≤-suc-cases _ _ le)

iPfinEmbEq : ∀ k n (le : k ≤N n) (x : iPfin k)
  → iMapPfin n (iPfinEmb k (suc n) (≤-suc le) x) ≡ iPfinEmb k n le x
iPfinEmbEq k zero le x = refl
iPfinEmbEq k (suc n) le x = {!!}
-- iPfinEmbEq k (suc zero) le x with ≤-suc-cases k _ le
-- ... | inj₁ p =
--   subst
--     (λ k →
--        (le : k ≤N 1) (x : iPfin k) →
--        mapPfin _
--        (rec⊎ (λ le' → η (η tt) ∪ ø)
--         (λ eq → transp (λ i → iPfin (eq i)) i0 x)
--         (≤-suc-cases k 1 (suc (fst le) , (λ i → suc (snd le i)))))
--        ≡ (η tt ∪ ø))
--     (sym (≤0→≡0 p)) (λ _ _ → refl) le x
-- ... | inj₂ p =
--   subst
--     (λ k →
--        (le : k ≤N 1) (x : iPfin k) →
--        mapPfin _
--        (rec⊎ (λ le' → η (η tt) ∪ ø)
--         (λ eq → transp (λ i → iPfin (eq i)) i0 x)
--         (≤-suc-cases k 1 (suc (fst le) , (λ i → suc (snd le i)))))
--        ≡ (η tt ∪ ø))
--     (sym p) (λ _ _ → refl) le x
-- iPfinEmbEq k (suc (suc n)) le x = {!!}

iPfinEmbRefl : ∀ n (x : ωPfin)
  → iMapPfin n (iPfinEmb (suc n) (suc n) ≤-refl (x .fst (suc n)))
    ≡ x .fst n
iPfinEmbRefl zero x = refl
iPfinEmbRefl (suc n) x with ≤-suc-cases (suc n) n (pred-≤-pred ≤-refl)
... | inj₁ p = ⊥-rec (¬m<m p) 
... | inj₂ p =
  cong (λ q → mapPfin (iMapPfin n) (subst (Pfin ∘ iPfin) q (x .fst (suc (suc n))))) (isSetℕ (suc n) (suc n) p refl)
  ∙ cong (mapPfin (iMapPfin n)) (substRefl {B = Pfin ∘ iPfin} (x .fst (suc (suc n)))) 
  ∙ x .snd (suc n)
-}

{-
-- with ≤-suc-cases k (suc n) le
-- ... | inj₁ p =
--   {!!}
--   ∙ cong (mapPfin η) (iPfinEmbEq k (suc n) p x)
-- ... | inj₂ p = {!!}


module _
  (closed : 
    ∀ s (x : ωLimit iPfin-ch)
    → (y : ℕ → ωLimit iPfin-ch)
    → (my : ∀ n → ⟨ y n ∈ₛ s ⟩)
    → (yconv : ∀ n → y n .fst n ≡ x .fst n)
    → ⟨ x ∈ₛ s ⟩) where

  _≤B_ : Bool → Bool → Type
  false ≤B b = Unit
  true ≤B b = b ≡ true

  infix 5 _≤B_

  ℕ∞ : Type
  ℕ∞ = Σ[ x ∈ (ℕ → Bool) ] isProp (Σ[ n ∈ ℕ ] x n ≡ true)

  HP : Type
  HP = (x : ℕ∞) →
    ((n : ℕ) → x .fst n ≡ false) ⊎ (∃[ n ∈ ℕ ] x .fst n ≡ true)

  true-before? : (x : ℕ∞) (n : ℕ)
    → Dec (Σ[ k ∈ ℕ ] (k ≤N n) × (x .fst k ≡ true))
  true-before? x zero with x .fst zero ≟ true
  ... | yes p = yes (0 , ≤-refl , p)
  ... | no ¬p = no (λ { (k , k≤ , eq) →
    ¬p (cong (x .fst) (sym (≤0→≡0 k≤)) ∙ eq) })
  true-before? x (suc n) with true-before? x n
  ... | yes (k , k≤ , eq) = yes (k , ≤-suc k≤ , eq)
  ... | no ¬ih with x .fst (suc n) ≟ true
  ... | yes p = yes (suc n , ≤-refl , p)
  ... | no ¬p = no (λ { (k , k≤ , eq) → {!fine!} })


  halting : HP
  halting x = {!!}
    where
      growing? : ℕ∞ → ∀ n → iPfin n
      growing? x n with true-before? x n
      ... | yes (k , le , eq) = iPfinEmb k n le (growing k) 
      ... | no ¬p = growing n

      growing?Eq : (x : ℕ∞) → ∀ n
        → iMapPfin n (growing? x (suc n)) ≡ growing? x n
      growing?Eq x n with true-before? x n
      ... | yes (k , le , eq) = iPfinEmbEq k n le _
      ... | no ¬p with x .fst (suc n) ≟ true
      ... | yes q = iPfinEmbRefl n growing-ch
      ... | no ¬q = growingEq n

      growing?-ch : ℕ∞ → ωPfin
      growing?-ch x = growing? x , growing?Eq x

{-
      diag : ℕ∞ → ∀ n → iPfin n
      diag x n =
        if (x .fst n)
           then growing? x n
           else growing n

      diagEq : (x : ℕ∞) (n : ℕ)  → iMapPfin n (diag x (suc n)) ≡ diag x n
      diagEq x n = {!!}
-}
--       x zero = refl
--       diagEq x (suc zero) with x .fst 2
--       ... | false = growingEq 1
--       ... | true = refl
--       diagEq x (suc (suc n)) with x .snd (suc (suc n)) 
--       ... | p with x .fst (suc (suc n))
--       ... | true =
--         cong (λ z →
--                 mapPfin (mapPfin (iMapPfin n))
--                         (if z
--                          then η (η ø) ∪ mapPfin η (mapPfin η (growing (suc n)))
--                          else η ø ∪ (η (η ø)
--                               ∪ mapPfin η (mapPfin η (growing (suc n))))))
--              p
--        ∙ {!growingEq (suc (suc n))!}
--       ... | false with x .fst (suc (suc (suc n)))
--       ... | false = growingEq (suc (suc n))
--       ... | true = {!growingEq (suc (suc n))!}

--       diag-ch : ℕ∞ → ωPfin
--       diag-ch x = diag x , diagEq x

      seq : ℕ∞ → ℕ → ωPfin
      seq x n with x .fst n ≟ true
      ... | yes p = {!growing-ch!}
      ... | no ¬p = {!!}

      



misInjective-neg :
  (∀ s t
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → s ⊆ t)
  → ∀ s (x : ωLimit iPfin-ch)
  → (∀ n → Σ[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ s ⟩ × (z .fst n ≡ x .fst n))
  → ⟨ x ∈ₛ s ⟩
misInjective-neg inj s x@(u , equ) p =
  inj (η x) s lem _ ∣ refl ∣
  where
    lem : ∀ n → η (u n) ⊆ mapPfin (λ x → x .fst n) s
    lem n =
      let (w , mw , eqw) = p n
      in λ y → ∥rec∥ (snd (y ∈ₛ mapPfin (λ x → x .fst n) s))
           (λ eqy → subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) s ⟩) (eqw ∙ sym eqy)
             (∈ₛmapPfin (λ x → x .fst n) w s mw))

module _ where

  lem1 : ∀ s t
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                        ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → ∀ x → ⟨ x ∈ₛ s ⟩
    → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n)
  lem1 s t hyp x mx n  =
    pre∈ₛmapPfin (λ x → x .fst n) (x .fst n) t (hyp n _ (∈ₛmapPfin (λ x → x .fst n) x s mx))

  lem2 : ∀ s t
    → (∀ x → ⟨ x ∈ₛ s ⟩
         → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n))
    → ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                       ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
  lem2 s t hyp n x mx = ∥rec∥ (snd (x ∈ₛ mapPfin (λ x₁ → x₁ .fst n) t))
    (λ { (y , my , eq) → ∥rec∥ (snd (x ∈ₛ mapPfin (λ x₁ → x₁ .fst n) t))
       (λ { (z , mz , eq') → subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) t ⟩) (eq' ∙ eq) (∈ₛmapPfin (λ x → x .fst n) z t mz) })
       (hyp y my n) })
    (pre∈ₛmapPfin (λ x → x .fst n) x s mx)


  lem12 : (∀ s t
        → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                       ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
        → s ≡ t)
    → ∀ s t
    → (∀ x →  ⟨ x ∈ₛ s ⟩
      → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n))
    → (∀ x →  ⟨ x ∈ₛ t ⟩
      → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ s ⟩ × (z .fst n ≡ x .fst n))
    → s ≡ t
  lem12 hyp s t p1 p2 = hyp s t (λ n → antisym⊆ (lem2 s t p1 n) (lem2 t s p2 n))

  lem21 :  (∀ s t
        → (∀ x →  ⟨ x ∈ₛ s ⟩
          → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n))
        → (∀ x →  ⟨ x ∈ₛ t ⟩
          → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ s ⟩ × (z .fst n ≡ x .fst n))
        → s ≡ t)
    → ∀ s t
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                       ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → s ≡ t
  lem21 hyp s t p = hyp s t (lem1 s t (λ n → subst (mapPfin (λ x → x .fst n) s ⊆_) (p n) (λ _ z → z)))
                            (lem1 t s (λ n → subst (_⊆ mapPfin (λ x → x .fst n) s) (p n) (λ _ z → z)))


  lem3 : (∀ s t
        → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                       ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
        → s ≡ t)
    → ∀ t x (z : ℕ → ωLimit iPfin-ch)
    → (∀ n → ⟨ z n ∈ₛ t ⟩) → (∀ n → z n .fst n ≡ x .fst n) → ⟨ x ∈ₛ t ⟩
  lem3 hyp t x z p q = {!!}
    where
      lemma : η x ≡ t
      lemma = lem12 hyp (η x) t (λ y eq n → ∥map∥ (λ eq → z n , p n , q n ∙ sym (funExt⁻ (cong fst eq) n)) eq)
        λ y my n → {!!}
-}











{-
misInjective-neg' :
  (∀ s t
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → s ⊆ t)
  → ∀ s t 
  → (∀ x → ⟨ x ∈ₛ s ⟩ → (∀ n → Σ[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n)) → ⟨ x ∈ₛ t ⟩)
  → (∀ x → ⟨ x ∈ₛ t ⟩ → (∀ n → Σ[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ s ⟩ × (z .fst n ≡ x .fst n)) → ⟨ x ∈ₛ s ⟩)
  → s ⊆ t
misInjective-neg' inj s t ps pt =
  inj s t λ n → antisym⊆
    (λ y my → ∥rec∥ {!!}
      (λ { (y' , my' , eqy) →  subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) t ⟩) eqy (∈ₛmapPfin (λ x → x .fst n) y' t (ps y' my' {!!})) }) --subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) t ⟩) eqy (∈ₛmapPfin (λ x → x .fst n) y' t (ps y' my' {!my!}))})
      (pre∈ₛmapPfin (λ x → x .fst n) y s my))
    {!!}

misInjective-neg' : ∀ s t
  → (∀ x → ⟨ x ∈ₛ s ⟩ → (∀ n → Σ[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n)) → ⟨ x ∈ₛ t ⟩)
  → ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
misInjective-neg' s t p n y my = ∥rec∥ {!!}
  (λ { (y' , my' , eq') → subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) t ⟩) eq' (∈ₛmapPfin (λ x → x .fst n) y' t (p y' my' {!!})) })
  (pre∈ₛmapPfin (λ x → x .fst n) y s my)

misInjective-neg'' : ∀ s t
  → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
  → ∀ x → ⟨ x ∈ₛ s ⟩ → ∀ n → ∃[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n)
misInjective-neg'' s t p x mx n  = {!!}  

misInjective-neg' : ∀ s t
  → (∀ x → ⟨ x ∈ₛ s ⟩ → ∀ n → Σ[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n))
  → (∀ x → (∀ n → Σ[ z ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (z .fst n ≡ x .fst n)) → ⟨ x ∈ₛ t ⟩)
  → ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
misInjective-neg' s t p q n y my = ∥rec∥ {!!}
  (λ { (y' , my' , eq') → subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) t ⟩) eq' (∈ₛmapPfin (λ x → x .fst n) y' t (q y' (p y' my'))) })
  (pre∈ₛmapPfin (λ x → x .fst n) y s my)
-}


{-
misInjective' : ∀ s t
  → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
              ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
  → s ⊆ t
misInjective' s t p y@(u , eq) my =
  ∥rec∥ (snd (y ∈ₛ t))
    (λ q →
      let δ : ∀ n → iPfin n
          δ n = q n .fst .fst n
          eq? : ∀ n → δ n ≡ u n
          eq? n = q n .snd .snd

          w : ℕ → ∀ n → iPfin n
          w k = q k .fst .fst
          eqw : (k : ℕ) (n : ℕ) → iMapPfin n (w k (suc n)) ≡ w k n
          eqw k = q k .fst .snd
          mw : ∀ k → ⟨ (w k , eqw k) ∈ₛ t ⟩
          mw k = q k .snd .fst
          eqwu : ∀ k → w k k ≡ u k
          eqwu k = q k .snd .snd
          -- also true:
          -- ∀ n ≤ k → w k n ≡ u n
          -- therefore
          -- ∀ n ≤ k ≤ l → w l n ≡ w k n
      in {!q!})
    lem4
  where
    lem : ∀ n → ⟨ u n ∈ₛ mapPfin (λ x → x .fst n) s ⟩
    lem n = subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) s ⟩)
                  (eq n)
                  {! !}

    lem2 : ∀ n → ⟨ u n ∈ₛ mapPfin (λ x → x .fst n) t ⟩
    lem2 n = p n _ (lem n)

    lem3 : ∀ n → ∃[ z@(w , eqw) ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (w n ≡ u n)
    -- iMapPfin n (proj iPfin-ch (suc n) z
    lem3 n =  pre∈ₛmapPfin (λ x → x .fst n) (u n) t (lem2 n)

    lem4 : ∥ (∀ n → Σ[ z@(w , eqw) ∈ ωLimit iPfin-ch ] ⟨ z ∈ₛ t ⟩ × (w n ≡ u n)) ∥
    lem4 = {!!}
-}


path : ∀ n → iPfin n
path zero = tt
path (suc n) = η (path n)

path-res : ∀ n → iMapPfin n (path (suc n)) ≡ path n
path-res zero = refl
path-res (suc n) = cong η (path-res n)

path-ch : ωPfin
path-ch = path , path-res

path? : (a : ℕ → Bool) → ∀ n → iPfin n
path? a zero = tt
path? a (suc n) =
  if a 0 then ø else η (path? (a ∘ suc) n)

path?-res : (a : ℕ → Bool) 
  → ∀ n → iMapPfin n (path? a (suc n)) ≡ path? a n
path?-res a zero = refl
path?-res a (suc n) with a 0
... | false = cong η (path?-res (a ∘ suc) n)
... | true = refl

path?-ch : (a : ℕ → Bool) → ωPfin
path?-ch a = path? a , path?-res a

path?-res' : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → a (suc n) ≡ true → iMapPfin n (path? a (suc n)) ≡ path n
path?-res' a aP zero eq = refl
path?-res' a aP (suc n) eq with dichotomyBool (a 0)
... | inj₁ p = ⊥-rec (znots (cong fst (aP (_ , p) (_ , eq))))
... | inj₂ p =
  cong (λ z → mapPfin (iMapPfin n) (if z then ø else η (if a 1 then ø else η (path? (λ x → a (suc (suc x))) n)))) p
  ∙ cong η (path?-res' (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n eq)

path?≠path : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → path? a (suc n) ≡ path (suc n) → a n ≡ false
path?≠path a aP zero eq with a 0
... | false = refl
... | true = ⊥-rec (ødisjη (sym eq))
path?≠path a aP (suc n) eq with a 0
... | false = path?≠path (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n (ηisInjective trunc eq)
... | true = ⊥-rec (ødisjη (sym eq))

data isEven : ℕ → Type
data isOdd : ℕ → Type
data isEven where
  zero : isEven zero
  suc : ∀{n} → isOdd n → isEven (suc n)
data isOdd where
  suc : ∀{n} → isEven n → isOdd (suc n)

isEven? : Bool → ℕ → Type
isEven? false n = isOdd n
isEven? true n = isEven n

path?? : (a : ℕ → Bool) → Bool → ∀ n → iPfin n
path?? a b zero = tt
path?? a b (suc n) =
  if a 0 and b then ø else η (path?? (a ∘ suc) (not b) n)

path??-res : (a : ℕ → Bool) (b : Bool)
  → ∀ n → iMapPfin n (path?? a b (suc n)) ≡ path?? a b n
path??-res a b zero = refl
path??-res a b (suc n) with a 0 | b
... | false | false = cong η (path??-res (a ∘ suc) true n)
... | false | true = cong η (path??-res (a ∘ suc) false n)
... | true | false = cong η (path??-res (a ∘ suc) true n)
... | true | true = refl

path??-ch : (a : ℕ → Bool) → Bool → ωPfin
path??-ch a b = path?? a b , path??-res a b


path??-lem1 : (a : ℕ → Bool) (b : Bool) (n : ℕ)
  → (∀ k → k ≤N n → a k ≡ false) → path?? a b n ≡ path n
path??-lem1 a b zero p = refl
path??-lem1 a b (suc n) p with dichotomyBool (a 0)
... | inj₁ eq = ⊥-rec (true≢false (sym eq ∙ p 0 zero-≤))
path??-lem1 a true (suc n) p | inj₂ eq =
  cong (λ z → if z and true then ø else η (path?? (a ∘ suc) false n)) eq
  ∙ cong η (path??-lem1 (a ∘ suc) false n (λ k le → p (suc k) (suc-≤-suc le)))
path??-lem1 a false (suc n) p | inj₂ eq =
  cong (λ z → if z and false then ø else η (path?? (a ∘ suc) true n)) eq
  ∙ cong η (path??-lem1 (a ∘ suc) true n (λ k le → p (suc k) (suc-≤-suc le)))

path??-lem2 : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → path?? a b n ≡ path? a n
path??-lem2 a aP b zero k lek eqk evk = refl
path??-lem2 a aP true (suc n) zero lek eqk evk =
  cong (λ z → if z and true then ø else η (path?? (a ∘ suc) false n)) eqk
  ∙ cong (λ z → if z then ø else η (path? (a ∘ suc) n)) (sym eqk) 
path??-lem2 a aP b (suc n) (suc k) lek eqk evk with dichotomyBool (a 0)
path??-lem2 a aP b (suc n) (suc k) lek eqk evk | inj₁ eq0 =
  ⊥-rec (snotz (cong fst (aP (_ , eqk) (_ , eq0))))
path??-lem2 a aP false (suc n) (suc k) lek eqk (suc ev) | inj₂ eq0 =
  cong (λ z → if z and false then ø else η (path?? (a ∘ suc) true n)) eq0
  ∙ cong η (path??-lem2 (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) true n k (pred-≤-pred lek) eqk ev)
  ∙ cong (λ z → if z then ø else η (path? (a ∘ suc) n)) (sym eq0) 
path??-lem2 a aP true (suc n) (suc k) lek eqk (suc odd) | inj₂ eq0 =
  cong (λ z → if z and true then ø else η (path?? (a ∘ suc) false n)) eq0
  ∙ cong η (path??-lem2 (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) false n k (pred-≤-pred lek) eqk odd)
  ∙ cong (λ z → if z then ø else η (path? (a ∘ suc) n)) (sym eq0) 

path??-lem3 : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → path?? a (not b) n ≡ path n
path??-lem3 a aP b zero k le eqk evk = refl
path??-lem3 a aP true (suc n) zero le eq0 evk =
  cong (λ z → if z and false then ø else η (path?? (a ∘ suc) true n)) eq0
  ∙ cong η (path??-lem1 (a ∘ suc) true n
      (λ k le → rec⊎ (λ eqk → ⊥-rec (snotz (cong fst (aP (_ , eqk) (_ , eq0))))) (λ x → x) (dichotomyBool (a (suc k)))))
path??-lem3 a aP b (suc n) (suc k) le eqk evk with dichotomyBool (a 0)
... | inj₁ eq0 = ⊥-rec (snotz (cong fst (aP (_ , eqk) (_ , eq0))))
path??-lem3 a aP false (suc n) (suc k) le eqk (suc ev) | inj₂ eq0 =
  cong (λ z → if z and true then ø else η (path?? (a ∘ suc) false n)) eq0
  ∙ cong η (path??-lem3 (a ∘ suc) ((λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) })) true n k (pred-≤-pred le) eqk ev)
path??-lem3 a aP true (suc n) (suc k) le eqk (suc odd) | inj₂ eq0 = 
  cong (λ z → if z and false then ø else η (path?? (a ∘ suc) true n)) eq0
  ∙ cong η (path??-lem3 (a ∘ suc) ((λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) })) false n k (pred-≤-pred le) eqk odd)

--path?? : (a : ℕ → Bool) → Bool → ∀ n → iPfin n

seq-ch : {A : Type} (a : ℕ → Bool) (x y : A) → Bool → ℕ → A
seq-ch a x y b zero = if a 0 and b then y else x
seq-ch a x y b (suc n) = if a 0 and b then y else seq-ch (a ∘ suc) x y (not b) n

seq-ch-lem1 : {A : Type} (a : ℕ → Bool) (x y : A) (b : Bool) (n : ℕ)
  → (∀ k → k ≤N n → a k ≡ false) → seq-ch a x y b n ≡ x
seq-ch-lem1 a x y b zero p with p 0 zero-≤
... | r with a 0 | b
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = ⊥-rec (true≢false r)
seq-ch-lem1 a x y b (suc n) p with p 0 zero-≤
... | r with a 0 | b
... | false | false = seq-ch-lem1 (a ∘ suc) x y true n λ k le → p (suc k) (suc-≤-suc le)
... | false | true = seq-ch-lem1 (a ∘ suc) x y false n λ k le → p (suc k) (suc-≤-suc le)
... | true | false = seq-ch-lem1 (a ∘ suc) x y true n λ k le → p (suc k) (suc-≤-suc le)
... | true | true = ⊥-rec (true≢false r)


decEven : ∀ n → isEven n ⊎ isOdd n
decEven zero = inj₁ zero
decEven (suc n) =
  rec⊎ (λ z → inj₂ (suc z)) (λ z → inj₁ (suc z)) (decEven n)

even-not-odd : ∀ {n} → isEven n → isOdd n → ⊥
even-not-odd (suc x₁) (suc x) = even-not-odd x x₁

{-
decEven : ∀ n → Dec (isEven n)
decOdd : ∀ n → Dec (isOdd n)

decEven zero = yes zero
decEven (suc n) with decOdd n
... | yes p = yes (suc p)
... | no ¬p = no (λ { (suc q) → ¬p q })

decOdd zero = no (λ ())
decOdd (suc n) with decEven n
... | yes p = yes (suc p)
... | no ¬p = no (λ { (suc q) → ¬p q })
-}

seq-ch-lem2 : {A : Type} (a : ℕ → Bool) (x y : A) (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → seq-ch a x y b n ≡ y
seq-ch-lem2 a x y b zero zero le eq ev with a 0
... | false = ⊥-rec (false≢true eq)
seq-ch-lem2 a x y true zero zero le eq ev | true = refl
seq-ch-lem2 a x y b (suc n) zero le eq ev with a 0
... | false = ⊥-rec (false≢true eq)
seq-ch-lem2 a x y true (suc n) zero le eq ev | true = refl
seq-ch-lem2 a x y b zero (suc k) le eq ev = ⊥-rec (¬-<-zero le)
seq-ch-lem2 a x y b (suc n) (suc k) le eq ev with a 0
seq-ch-lem2 a x y false (suc n) (suc k) le eq (suc ev) | false = seq-ch-lem2 (a ∘ suc) x y true n k (pred-≤-pred le) eq ev
seq-ch-lem2 a x y true (suc n) (suc k) le eq (suc ev) | false = seq-ch-lem2 (a ∘ suc) x y false n k (pred-≤-pred le) eq ev
seq-ch-lem2 a x y false (suc n) (suc k) le eq (suc ev) | true = seq-ch-lem2 (a ∘ suc) x y true n k (pred-≤-pred le) eq ev
seq-ch-lem2 a x y true (suc n) (suc k) le eq ev | true = refl


seq-ch-lem3 : {A : Type} (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → (x y : A) (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → seq-ch a x y (not b) n ≡ x
seq-ch-lem3 a aP x y true zero zero le eq ev with a 0
... | false = ⊥-rec (false≢true eq)
... | true = refl
seq-ch-lem3 a aP x y true (suc n) zero le eq ev with dichotomyBool (a 0)
... | inj₂ q = ⊥-rec (false≢true (sym q ∙ eq)) 
... | inj₁ q =
  cong (λ z → if z and false then y else seq-ch (a ∘ suc) x y true n) q
  ∙ seq-ch-lem1 (a ∘ suc) x y true n
      (λ k le' → rec⊎ (λ p → ⊥-rec (snotz (cong fst (aP (_ , p) (_ , eq))) )) (λ p → p) (dichotomyBool (a (suc k)))) 
seq-ch-lem3 a aP x y b zero (suc k) le eq ev = ⊥-rec (¬-<-zero le)
seq-ch-lem3 a aP x y false (suc n) (suc k) le eq (suc ev) with dichotomyBool (a 0)
... | inj₂ p =
  cong (λ z → if z and true then y else seq-ch (a ∘ suc) x y false n) p
  ∙ seq-ch-lem3 (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) x y true n k (pred-≤-pred le) eq ev
... | inj₁ p = ⊥-rec (snotz (cong fst (aP (_ , eq) (_  , p))))
seq-ch-lem3 a aP x y true (suc n) (suc k) le eq (suc ev) with dichotomyBool (a 0)
... | inj₂ p = 
  cong (λ z → if z and false then y else seq-ch (a ∘ suc) x y true n) p
  ∙ seq-ch-lem3 (a ∘ suc) ((λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) })) x y false n k (pred-≤-pred le) eq ev
... | inj₁ p = ⊥-rec (snotz (cong fst (aP (_ , eq) (_  , p))))

true-before? : (a : ℕ → Bool) (n : ℕ)
  → Dec (Σ[ k ∈ ℕ ] (k ≤N n) × (a k ≡ true))
true-before? a zero with a zero ≟ true
... | yes p = yes (0 , ≤-refl , p)
... | no ¬p = no (λ { (k , k≤ , eq) →
  ¬p (cong a (sym (≤0→≡0 k≤)) ∙ eq) })
true-before? a (suc n) with true-before? a n
... | yes (k , k≤ , eq) = yes (k , ≤-suc k≤ , eq)
... | no ¬ih with a (suc n) ≟ true
... | yes p = yes (suc n , ≤-refl , p)
... | no ¬p = no (λ { (k , k≤ , eq) → rec⊎ (λ r → ¬ih (_ , r , eq)) (λ r → ¬p (cong a (sym r) ∙ eq)) (≤-suc-cases k n k≤) })

diag-seq-ch :  (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true)) (n : ℕ) →
  res iPfin-ch n (seq-ch a path-ch (path?-ch a) true (suc n) .fst (suc n)) ≡ seq-ch a path-ch (path?-ch a) true n .fst n
diag-seq-ch a aP n with true-before? a n
... | yes (k , le , eq) with decEven k
... | inj₁ p =
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem2 a path-ch (path?-ch a) true (suc n) k (≤-suc le) eq p)
  ∙ path?-res a n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem2 a path-ch (path?-ch a) true n k le eq p))
... | inj₂ p = 
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem3 a aP path-ch (path?-ch a) false (suc n) k (≤-suc le) eq p)
  ∙ path-res n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem3 a aP path-ch (path?-ch a) false n k le eq p))
diag-seq-ch a aP n | no ¬p with dichotomyBool (a (suc n))
... | inj₂ q =
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem1 a path-ch (path?-ch a) true (suc n)
    (λ k le → rec⊎ (λ r → ⊥-rec (rec⊎ (λ p → ¬p (k , p , r)) (λ p → false≢true (sym q ∙ cong a (sym p) ∙ r)) (≤-suc-cases _ _ le)))
                    (λ r → r)
                    (dichotomyBool (a k))))
  ∙ path-res n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem1 a path-ch (path?-ch a) true n
      λ k le → rec⊎ (λ r → ⊥-rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))
... | inj₁ q  with decEven (suc n)
... | inj₁ ev = 
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem2 a path-ch (path?-ch a) true (suc n) (suc n) ≤-refl q ev)
  ∙ path?-res' a aP n q
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem1 a path-ch (path?-ch a) true n
      λ k le → rec⊎ (λ r → ⊥-rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))
... | inj₂ odd =
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem3 a aP path-ch (path?-ch a) false (suc n) (suc n) ≤-refl q odd)
  ∙ path-res n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem1 a path-ch (path?-ch a) true n
      λ k le → rec⊎ (λ r → ⊥-rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))

seq-ch-path?? : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true)) (n : ℕ)
  → seq-ch a path-ch (path?-ch a) true n .fst n ≡ path??-ch a true .fst n
seq-ch-path?? a aP n with true-before? a n
... | yes (k , le , eq) with decEven k
... | inj₁ ev =
  cong (λ z → z .fst n) (seq-ch-lem2 a path-ch (path?-ch a) true n k le eq ev)
  ∙ sym (path??-lem2 a aP true n k le eq ev)
... | inj₂ odd = 
  cong (λ z → z .fst n) (seq-ch-lem3 a aP path-ch (path?-ch a) false n k le eq odd)
  ∙ sym (path??-lem3 a aP false n k le eq odd )
seq-ch-path?? a aP n | no ¬p =
  cong (λ z → z .fst n) (seq-ch-lem1 a path-ch (path?-ch a) true n
          (λ k le → rec⊎ (λ eq → ⊥-rec (¬p (k , le , eq))) (λ x → x) (dichotomyBool (a k))))
  ∙ sym (path??-lem1 a true n (λ k le → rec⊎ (λ eq → ⊥-rec (¬p (k , le , eq))) (λ x → x) (dichotomyBool (a k))))

seq-ch-cases : {A : Type} (a : ℕ → Bool)
  → (x y : A) (b : Bool) (n : ℕ)
  → (seq-ch a x y b n ≡ x) ⊎ (seq-ch a x y b n ≡ y)
seq-ch-cases a x y false zero with a 0
... | false = inj₁ refl
... | true = inj₁ refl
seq-ch-cases a x y true zero with a 0
... | false = inj₁ refl
... | true = inj₂ refl
seq-ch-cases a x y false (suc n) with a 0
... | false = seq-ch-cases (a ∘ suc) x y true n
... | true = seq-ch-cases (a ∘ suc) x y true n
seq-ch-cases a x y true (suc n) with a 0
... | false = seq-ch-cases (a ∘ suc) x y false n
... | true = inj₂ refl



{-
seq-ch-lem2-even : {A : Type} (a : ℕ → Bool) (x y : A) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven k → seq-ch a x y true n ≡ y
seq-ch-lem2-odd : {A : Type} (a : ℕ → Bool) (x y : A) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isOdd k → seq-ch a x y false n ≡ y

seq-ch-lem2-even a x y zero zero le eq ev with a 0
... | false = ⊥-rec (false≢true eq)
... | true = refl
seq-ch-lem2-even a x y (suc n) zero le eq ev with a 0
... | false = ⊥-rec (false≢true eq)
... | true = refl
seq-ch-lem2-even a x y zero (suc k) le eq ev with a 0
... | false = ⊥-rec (¬-<-zero le)
... | true = refl
seq-ch-lem2-even a x y (suc n) (suc k) le eq (suc ev) with a 0
... | false = seq-ch-lem2-odd (a ∘ suc) x y n k (pred-≤-pred le) eq ev
... | true = refl

seq-ch-lem2-odd a x y zero (suc k) le eq (suc ev) = ⊥-rec (¬-<-zero le)
seq-ch-lem2-odd a x y (suc n) (suc k) le eq (suc ev) with a 0
... | false = seq-ch-lem2-even (a ∘ suc) x y n k (pred-≤-pred le) eq ev
... | true = seq-ch-lem2-even (a ∘ suc) x y n k (pred-≤-pred le) eq ev
-}

{-
seq-ch-lem2 : {A : Type} (a : ℕ → Bool) (x y : A) (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → seq-ch a x y b n ≡ (if b then y else x)
seq-ch-lem2 a x y true zero zero le eq even? with a 0
... | false = ⊥-rec (false≢true eq)
... | true = refl
seq-ch-lem2 a x y true (suc n) zero le eq even? with a 0
... | false = ⊥-rec (false≢true eq)
... | true = refl
seq-ch-lem2 a x y b zero (suc k) le eq even? = {!imp!}
seq-ch-lem2 a x y b (suc n) (suc k) le eq even? with a 0
seq-ch-lem2 a x y false (suc n) (suc k) le eq (suc even?) | false = {!seq-ch-lem2 (a ∘ suc) x y true n k ? eq even?!}
seq-ch-lem2 a x y false (suc n) (suc k) le eq even? | true = {!!}
seq-ch-lem2 a x y true (suc n) (suc k) le eq even? | false = {!!}
seq-ch-lem2 a x y true (suc n) (suc k) le eq even? | true = {!!}
-}

-- seq-ch'' : {A : Type} (a : ℕ → Bool) (x y : A) → ℕ → A
-- seq-ch'' a x y zero = if a 0 then y else x
-- seq-ch'' a x y (suc zero) = if a 0 then y else x
-- seq-ch'' a x y (suc (suc n)) = if a 0 then y else (if a 1 then x else seq-ch'' (λ z → a (suc (suc z)))  x y n)

-- {-

-- seq-ch3-lem  :  (a : ℕ → Bool) (b : Bool) (n : ℕ)
--   → seq-ch a path (path? a) b n n ≡ path?? a b n
-- seq-ch3-lem a b zero = {!!}
-- seq-ch3-lem a b (suc n) with a 0 | b
-- ... | false | false = {!seq-ch3-lem (a ∘ suc) true n!}
-- ... | false | true = {!!}
-- ... | true | false = {!!}
-- ... | true | true = {!!}
-- -}

-- append : {A : Type} → List A → (ℕ → A) → ℕ → A
-- append [] a n = a n
-- append (x ∷ xs) a zero = x
-- append (x ∷ xs) a (suc n) = append xs a n

-- seq-ch : (xs : List Bool) (a : ℕ → Bool) → Bool → ℕ → ωPfin
-- seq-ch xs a b zero = if a 0 and b then path?-ch (append xs a) else path-ch
-- seq-ch xs a b (suc n) = if a 0 and b then path?-ch (append xs a) else seq-ch (xs ∷ʳ false) (a ∘ suc) (not b) n

-- seq-ch3-lem :  (xs : List Bool) (a : ℕ → Bool) (b : Bool) (n : ℕ)
--   → seq-ch xs a b n .fst n ≡ path?? a b n
-- seq-ch3-lem xs a b zero = {!!}
-- seq-ch3-lem xs a b (suc n) with a 0 | b
-- ... | false | false = {!seq-ch3-lem (xs ++ false ∷ []) (a ∘ suc) true n!}
-- ... | false | true = {!!}
-- ... | true | false = {!!}
-- ... | true | true = {!!}

-- module Prova where

--   a : ℕ → Bool
--   a 4 = true
--   a _ = false

--   x = 0
--   y = 1

--   check : {! seq-ch a x y true 100 !}

  




-- {-
-- seq-ch3 : (a : ℕ → Bool) → Bool → ℕ → ∀ n → iPfin n
-- seq-ch3 a b zero n = {!if a 0 and b then path? a else path!}
-- seq-ch3 a b (suc k) zero = tt
-- seq-ch3 a b (suc k) (suc n) = if a 0 and b then ø else seq-ch3 (a ∘ suc) (not b) k (suc n)

-- seq-ch3-lem2 :  (a : ℕ → Bool) (b : Bool) (n : ℕ)
--   → seq-ch3 (a ∘ suc) true n (suc n) ≡ η (seq-ch3 (a ∘ suc) true n n)
-- seq-ch3-lem2 a b zero = {!!}
-- seq-ch3-lem2 a b (suc n) = {!!}

-- seq-ch3-lem :  (a : ℕ → Bool) (b : Bool) (n : ℕ)
--   → seq-ch3 a b n n ≡ path?? a b n
-- seq-ch3-lem a b zero = refl
-- seq-ch3-lem a b (suc n) with a 0 | b
-- ... | false | false = {!!} ∙ cong η (seq-ch3-lem (a ∘ suc) true n)
-- ... | false | true = {!!}
-- ... | true | false = {!!}
-- ... | true | true = refl
-- -}

-- -- seq-ch' : {A : Type} (a : ℕ → Bool) (x y z : A) → ℕ → A
-- -- seq-ch' a x y z zero = if a 0 then y else z
-- -- seq-ch' a x y z (suc n) = if a 0 then y else seq-ch' (a ∘ suc) y x z n
-- -- --seq-ch a x y (suc (suc n)) = if a 0 then y else seq-ch (a ∘ suc) y x (suc n)

-- -- seq-ch : {A : Type} (a : ℕ → Bool) (x y : A) → ℕ → A
-- -- seq-ch a x y = seq-ch' a x y x


-- -- seq-ch'-lem1 : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → ∀ n k → iMapPfin k (seq-ch' a x y z n .fst (suc k)) ≡ seq-ch' a x y z n .fst k
-- -- seq-ch'-lem1 a x y z zero k with a 0
-- -- ... | false = z .snd k
-- -- ... | true = y .snd k
-- -- seq-ch'-lem1 a x y z (suc n) k with a 0
-- -- ... | false = seq-ch'-lem1 (a ∘ suc) y x z n k
-- -- ... | true = y .snd k

-- -- seq-ch'-lem21 : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → a 0 ≡ true
-- --   → ∀ n → y ≡ seq-ch' a x y z n
-- -- seq-ch'-lem21 a x y z eq zero with a 0
-- -- ... | false = ⊥-rec (false≢true eq)
-- -- ... | true = refl
-- -- seq-ch'-lem21 a x y z eq (suc n) with a 0
-- -- ... | false = ⊥-rec (false≢true eq)
-- -- ... | true = refl

-- -- seq-ch'-lem22 : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → a 0 ≡ false
-- --   → ∀ n → seq-ch' a y x z n ≡ seq-ch' (a ∘ suc) x y z n
-- -- seq-ch'-lem22 a x y z r zero with a 0
-- -- ... | false = {!!}
-- -- ... | true = {!!}
-- -- seq-ch'-lem22 a x y z r (suc n) with a 0
-- -- ... | false = {!!}
-- -- ... | true = {!!}

-- -- seq-ch'-lem2 : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → (∀ n → a n ≡ true → x .fst n ≡ z .fst n)
-- --   → (∀ {n} → isEven n → a n ≡ true → ∀{k} → k ≤N n → y .fst k ≡ z .fst k)
-- --   → ∀ n k → k ≤N n → (if a 0 then y else seq-ch' (a ∘ suc) y x z n) .fst k ≡ seq-ch' a x y z n .fst k
-- -- seq-ch'-lem2 a x y z p q zero k le with a 0
-- -- ... | true = refl
-- -- ... | false with dichotomyBool (a 1)
-- -- seq-ch'-lem2 a x y z p q zero zero le | false | inj₁ r = refl
-- -- seq-ch'-lem2 a x y z p q zero (suc k) le | false | inj₁ r = cong (λ b → (if b then x else z) .fst (suc k)) r ∙ p {!!} {!!}
-- -- ... | inj₂ r = cong (λ b → (if b then x else z) .fst k) r --cong (if_then x else z) r
-- -- seq-ch'-lem2 a x y z p q (suc n) k le with a 0
-- -- ... | false = seq-ch'-lem2 (a ∘ suc) y x z (λ nodd eq le → {!!}) {!!} n k {!!}
-- -- ... | true = refl

-- -- seq-ch'-lem : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → (∀ {n} → isOdd n → a n ≡ true → x ≡ z)
-- --   → (∀ {n} → isEven n → a n ≡ true → y ≡ z)
-- --   → ∀ n → iMapPfin n (seq-ch' a x y z (suc n) .fst (suc n)) ≡ seq-ch' a x y z n .fst n
-- -- seq-ch'-lem a x y z p q n =
-- --   seq-ch'-lem1 a x y z (suc n) n
-- --   ∙ {!!} --cong (λ w → w .fst n) (seq-ch'-lem2 a x y z p q n)

-- -- data Ord {A : Type} (x y z : A) : A → A → Type where
-- --   zlex : Ord x y z z x
-- --   zley : Ord x y z z y
-- --   yley : Ord x y z y y
-- --   xlex : Ord x y z x x
-- --   zlez : Ord x y z z z

-- -- Ord-swap : {A : Type} {x y z a b : A} → Ord x y z a b → Ord y x z a b
-- -- Ord-swap zlex = zley
-- -- Ord-swap zley = zlex
-- -- Ord-swap yley = xlex
-- -- Ord-swap xlex = yley
-- -- Ord-swap zlez = zlez

-- -- Ord-cases : {A : Type} {x y z a b : A} → Ord x y z a b
-- --   → ((a ≡ z) × (b ≡ x)) ⊎ (((a ≡ z) × (b ≡ y)) ⊎ (((a ≡ z) × (b ≡ z)) ⊎ (((a ≡ x) × (b ≡ x)) ⊎ ((a ≡ y) × (b ≡ y)))))
-- -- Ord-cases zlex = inj₁ (refl , refl)
-- -- Ord-cases zley = inj₂ (inj₁ (refl , refl))
-- -- Ord-cases zlez = inj₂ (inj₂ (inj₁ (refl , refl)))
-- -- Ord-cases xlex = inj₂ (inj₂ (inj₂ (inj₁ (refl , refl))))
-- -- Ord-cases yley = inj₂ (inj₂ (inj₂ (inj₂ (refl , refl))))

-- -- seq-ch-lem : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → ∀ n → ((a 0 ≡ false) × (a 1 ≡ false) × (seq-ch' a x y z (suc n) ≡ z) × (seq-ch' a x y z n ≡ z)) ⊎
-- --            (((a 0 ≡ false) × (a 1 ≡ true) × (seq-ch' a x y z (suc n) ≡ x) × (seq-ch' a x y z n ≡ z)) ⊎
-- --            ((a 0 ≡ true) × (seq-ch' a x y z (suc n) ≡ y) × (seq-ch' a x y z n ≡ y)))
-- -- seq-ch-lem a x y z zero with a 0
-- -- ... | true = inj₂ (inj₂ (refl , refl , refl))
-- -- ... | false with a 1
-- -- ... | false = inj₁ (refl , refl , refl , refl)
-- -- ... | true = inj₂ (inj₁ (refl , refl , refl , refl))
-- -- seq-ch-lem a x y z (suc n) with a 0
-- -- ... | true = inj₂ (inj₂ (refl , refl , refl))
-- -- ... | false with seq-ch-lem (a ∘ suc) y x z n
-- -- ... | inj₁ (r1 , r2 , eq1 , eq2) = inj₁ (refl , r1 , eq1 , eq2)
-- -- ... | inj₂ (inj₁ (r1 , r2 , eq1 , eq2)) = inj₁ (refl , r1 , eq1 ∙ {!!} , eq2)
-- -- ... | inj₂ (inj₂ x₁) = {!!}


-- -- --seq-ch-lem a x y z zero with a 0
-- -- --... | true = yley
-- -- --... | false with a 1
-- -- --... | false = zlez
-- -- --... | true = zlex
-- -- --seq-ch-lem a x y z (suc n) with a 0
-- -- --... | false = Ord-swap (seq-ch-lem (a ∘ suc) y x z n)
-- -- --... | true = yley
-- -- --
-- -- --seq-ch-lem-lem : (a : ℕ → Bool) (x y z : ωPfin)
-- -- --  → ∀ n → Ord x y z (seq-ch' a x y z n) (seq-ch' a x y z (suc n))

-- -- path?-eq : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
-- --   → ∀ n → a n ≡ true → path? a n ≡ path n
-- -- path?-eq a aP zero eq = refl
-- -- path?-eq a aP (suc n) eq with dichotomyBool (a 0)
-- -- ... | inj₁ p = ⊥-rec (znots (cong fst (aP (0 , p) (suc n , eq)))) 
-- -- ... | inj₂ p =
-- --   cong (if_then ø else η (path? (a ∘ suc) n)) p
-- --   ∙ cong η (path?-eq (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n eq)

-- -- {-
-- -- seq-ch'-lem2 : (a : ℕ → Bool) (x y z : ωPfin)
-- --   → (∀ n → a n ≡ true → iMapPfin n (x .fst (suc n)) ≡ z .fst n)
-- --   → (∀ n → a n ≡ true → iMapPfin n (y .fst (suc n)) ≡ z .fst n)
-- --   → ∀ n → iMapPfin n (seq-ch' a x y z (suc n) .fst (suc n)) ≡ seq-ch' a x y z n .fst n
-- -- seq-ch'-lem2 a x y z p q n = seq-ch'-lem1 a x y z (suc n) n ∙ {!!}
-- -- -}


-- -- {-
-- -- module Check where

-- --   a : ℕ → Bool
-- --   a 4 = true
-- --   a _ = false

-- --   x = 0
-- --   y = 1

-- --   check : {!seq-ch a x y 100 !}
-- -- -}

-- -- {-
-- -- x-res' :  (a : ℕ → Bool) (n : ℕ) →
-- --   res iPfin-ch n (seq-ch'' a path-ch (path?-ch a) (suc n) .fst (suc n)) ≡ seq-ch'' a path-ch (path?-ch a) n .fst n
-- -- x-res' a zero = refl
-- -- x-res' a (suc zero) = {!!}
-- -- x-res' a (suc (suc n)) = {!x-res' (λ z → a (suc (suc z))) n!}
-- -- -}

-- -- x-res' :  (a : ℕ → Bool) (n k : ℕ) →
-- --   {!mapPfin (iMapPfin k) (seq-ch' (a ∘ suc) path-ch (path?-ch (a ∘ suc)) path-ch n .fst k)!} ≡ seq-ch' (a ∘ suc) path-ch (path?-ch a) path-ch n .fst (suc k)

-- -- x-res :  (a : ℕ → Bool) (n : ℕ) →
-- --   res iPfin-ch n (seq-ch' a path-ch (path?-ch a) path-ch (suc n) .fst (suc n)) ≡ seq-ch' a path-ch (path?-ch a) path-ch n .fst n
-- -- x-res a zero = refl
-- -- x-res a (suc n) with dichotomyBool (a 0)
-- -- ... | inj₁ p =
-- --   cong (λ b → mapPfin (iMapPfin n) ((if b then path?-ch a else (if a 1 then path-ch else seq-ch' (λ x → a (suc (suc x))) path-ch (path?-ch a) path-ch n)) .fst (suc (suc n)))) p
-- --   ∙ cong (λ b → mapPfin (iMapPfin n) (if b then ø else η (if a 1 then ø else η (path? (λ x → a (suc (suc x))) n)))) p 
-- --   ∙ cong (if_then ø else η (path? (a ∘ suc) n)) (sym p)
-- --   ∙ cong (λ b → (if b then path?-ch a else seq-ch' (a ∘ suc) (path?-ch a) path-ch path-ch n) .fst (suc n)) (sym p)
-- -- ... | inj₂ p = 
-- --   cong (λ b → mapPfin (iMapPfin n) ((if b then path?-ch a else (if a 1 then path-ch else seq-ch' (λ x → a (suc (suc x))) path-ch (path?-ch a) path-ch n)) .fst (suc (suc n)))) p
-- --   ∙ {!!}
-- --   ∙ cong (λ b → (if b then path?-ch a else seq-ch' (a ∘ suc) (path?-ch a) path-ch path-ch n) .fst (suc n)) (sym p)






module FromInjectivity (minj : ∀ s t → m s ≡ m t → s ≡ t) where

  complete' : ∀ s t 
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → m s ≡ m t
  complete' s t p = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
    (funExt (λ { zero → refl ;
                 (suc n) → antisym⊆
                   (λ x mx → ∥rec∥ (snd ((x ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) t))))
                     (λ { (y , my , eq) → subst (λ z → ⟨ x ∈ₛ z ⟩)
                                                 (sym (mapPfinComp t
                                                   ∙ cong (λ f → mapPfin f t) (funExt (λ z → z .snd n))
                                                   ∙ sym (p n)
                                                   ∙ cong (λ f → mapPfin f s) (sym (funExt (λ z → z .snd n)))
                                                   ∙ sym (mapPfinComp s)))
                                                 (subst (λ z → ⟨ z ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) s) ⟩)
                                                        eq
                                                        (∈ₛmapPfin (iMapPfin n) y (mapPfin (proj iPfin-ch (suc n)) s) my)) })
                     (pre∈ₛmapPfin (iMapPfin n) x (mapPfin (proj iPfin-ch (suc n)) s) mx))
                   (λ x mx → ∥rec∥ (snd ((x ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) s))))
                     (λ { (y , my , eq) → subst (λ z → ⟨ x ∈ₛ z ⟩)
                                                 (sym (mapPfinComp s
                                                   ∙ cong (λ f → mapPfin f s) (funExt (λ z → z .snd n))
                                                   ∙ p n
                                                   ∙ cong (λ f → mapPfin f t) (sym (funExt (λ z → z .snd n)))
                                                   ∙ sym (mapPfinComp t)))
                                                 (subst (λ z → ⟨ z ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) t) ⟩)
                                                        eq
                                                        (∈ₛmapPfin (iMapPfin n) y (mapPfin (proj iPfin-ch (suc n)) t) my)) })
                     (pre∈ₛmapPfin (iMapPfin n) x (mapPfin (proj iPfin-ch (suc n)) t) mx))}))

  complete : (x y1 y2 : ωPfin) (z : ℕ → ωPfin)
    → (∀ n → (z n ≡ y1) ⊎ (z n ≡ y2))
    → (∀ n → z n .fst n ≡ x .fst n)
    → ⟨ x ∈ₛ (η y1 ∪ η y2) ⟩
  complete x y1 y2 z p q = subst (λ z → ⟨ x ∈ₛ z ⟩) (minj s t (complete' s t eq)) (inl ∣ refl ∣)
    where
      t : Pfin ωPfin
      t = η y1 ∪ η y2

      s : Pfin ωPfin
      s = η x ∪ t

      sub : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
      sub n a = ∥rec∥ propTruncIsProp
        (λ { (inj₁ r) →
                   ∥map∥ (λ eq → map⊎ (λ eq' → ∣ eq ∙ sym (q n) ∙ cong (λ w → w .fst n) eq' ∣)
                                      (λ eq' → ∣ eq ∙ sym (q n) ∙ cong (λ w → w .fst n) eq' ∣)
                                      (p n))
                         r ;
             (inj₂ r) → r })

      eq : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
      eq n = antisym⊆ (sub n) (λ a → inr)

  complete2 : ∀ x s1 s2 (z : ℕ → ωPfin)
    → (∀ n → ⟨ z n ∈ₛ (s1 ∪ s2) ⟩)
    → (∀ n → z n .fst n ≡ x .fst n)
    → ⟨ x ∈ₛ (s1 ∪ s2) ⟩
  complete2 x s1 s2 z p q = subst (λ z → ⟨ x ∈ₛ z ⟩) (minj s t (complete' s t eq)) (inl ∣ refl ∣)
    where
      t : Pfin ωPfin
      t = s1 ∪ s2

      s : Pfin ωPfin
      s = η x ∪ t

      sub : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
      sub n a = ∥rec∥ propTruncIsProp
        (λ { (inj₁ r) →
          ∥rec∥ propTruncIsProp
            (λ eq → ∥map∥ (map⊎ (λ r → subst (λ a → ⟨ a ∈ₛ mapPfin (λ z → z .fst n) s1 ⟩) (q n ∙ sym eq) (∈ₛmapPfin (λ z → z .fst n) (z n) s1 r))
                                (λ r → subst (λ a → ⟨ a ∈ₛ mapPfin (λ z → z .fst n) s2 ⟩) (q n ∙ sym eq) (∈ₛmapPfin (λ z → z .fst n) (z n) s2 r)))
                                (p n))
            r ;
             (inj₂ r) → r })

      eq : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
      eq n = antisym⊆ (sub n) (λ a → inr)

  llpo : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
    → ∥ (∀ n → isEven n → a n ≡ false) ⊎ (∀ n → isOdd n → a n ≡ false) ∥
  llpo a aP =
    ∥rec∥ propTruncIsProp
      (λ { (inj₁ p) →
             ∥map∥ (λ eq → inj₁ (λ n ev → rec⊎ (λ q → ⊥-rec (case1 eq n ev q)) (λ q → q) (dichotomyBool (a n))))
                   p
         ; (inj₂ p) → 
             ∥map∥ (λ eq → inj₂ (λ n odd → rec⊎ (λ q → ⊥-rec (case2 eq n odd q)) (λ q → q) (dichotomyBool (a n))))
                   p })
      (complete x y1 y2 z lem1 lem2)
    where
      y1 : ωPfin
      y1 = path-ch
      
      y2 : ωPfin
      y2 = path?-ch a

      z : ℕ → ωPfin
      z = seq-ch a y1 y2 true

      x : ωPfin
      x = (λ n → z n .fst n) ,
          diag-seq-ch a aP

      lem1 : ∀ n → (z n ≡ y1) ⊎ (z n ≡ y2)
      lem1 = seq-ch-cases a y1 y2 true

      lem2 : ∀ n → z n .fst n ≡ x .fst n
      lem2 n = refl

      case1 : x ≡ y1 → ∀ n → isEven n → a n ≡ true → ⊥
      case1 eqx n ev eq = false≢true (sym (path?≠path a aP n bad) ∙ eq) 
        where
          bad : path? a (suc n) ≡ path (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem2 a path-ch (path?-ch a) true (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ funExt⁻ (cong fst eqx) (suc n)

      case2 : x ≡ y2 → ∀ n → isOdd n → a n ≡ true → ⊥
      case2 eqx n ev eq = false≢true (sym (path?≠path a aP n (sym bad)) ∙ eq) 
        where
          bad : path (suc n) ≡ path? a (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem3 a aP path-ch (path?-ch a) false (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ funExt⁻ (cong fst eqx) (suc n)


parity : (a : ℕ → Bool) → Bool → ℕ → Bool
parity a b zero = (a 0 and b) or (not (a 0) and (not b))
parity a b (suc n) =
  if (a 0 and b) or (not (a 0) and (not b))
    then false
    else parity (a ∘ suc) (not b) n

parity-prop' : ∀ a b (n1 n2 : ℕ)
  → parity a b n1 ≡ true → parity a b n2 ≡ true
  → n1 ≡ n2
parity-prop' a b zero zero p q = refl
parity-prop' a b zero (suc n2) p q with a 0
parity-prop' a false zero (suc n2) p q | false = ⊥-rec (false≢true q) 
parity-prop' a true zero (suc n2) p q | false = ⊥-rec (false≢true p) 
parity-prop' a false zero (suc n2) p q | true = ⊥-rec (false≢true p) 
parity-prop' a true zero (suc n2) p q | true = ⊥-rec (false≢true q) 
parity-prop' a b (suc n1) zero p q with a 0
parity-prop' a false (suc n1) zero p q | false = ⊥-rec (false≢true p) 
parity-prop' a true (suc n1) zero p q | false = ⊥-rec (false≢true q) 
parity-prop' a false (suc n1) zero p q | true = ⊥-rec (false≢true q) 
parity-prop' a true (suc n1) zero p q | true = ⊥-rec (false≢true p) 
parity-prop' a b (suc n1) (suc n2) p q with a 0
parity-prop' a false (suc n1) (suc n2) p q | false = ⊥-rec (false≢true p) 
parity-prop' a true (suc n1) (suc n2) p q | false =
  cong suc (parity-prop' (a ∘ suc) false n1 n2 p q)
parity-prop' a false (suc n1) (suc n2) p q | true =
    cong suc (parity-prop' (a ∘ suc) true n1 n2 p q)
parity-prop' a true (suc n1) (suc n2) p q | true = ⊥-rec (false≢true p)

parity-prop : ∀ a b → isProp (Σ[ n ∈ ℕ ] parity a b n ≡ true)
parity-prop a b (n1 , eq1) (n2 , eq2) =
  Σ≡Prop (λ _ → isSetBool _ _) (parity-prop' a b n1 n2 eq1 eq2)

parity-even : (a : ℕ → Bool) 
  → ∀ n → isEven n
  → parity a true n ≡ false → a n ≡ true
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ b) × (parity a true k ≡ true)
parity-even' : (a : ℕ → Bool) 
  → ∀ n → isOdd n
  → parity a false n ≡ false → a n ≡ true
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ not b) × (parity a false k ≡ true)

parity-even a zero ev eqf eqt =
  ⊥-rec (true≢false (sym (cong (λ b → b and true or not b and false) eqt) ∙  eqf))
parity-even a (suc n) (suc ev) eqf eqt with dichotomyBool (a 0)
... | inj₁ q = 0 , true , zero , suc-≤-suc zero-≤ , q , cong (λ b → b and true or not b and false) q  
... | inj₂ q with parity-even' (a ∘ suc) n ev (sym (cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false n) q) ∙ eqf) eqt
... | k , false , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r
... | k , true , p , le , eq , r = _  , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r

parity-even' a (suc n) (suc ev) eqf eqt with dichotomyBool (a 0)
... | inj₂ q = 0 , true , zero , suc-≤-suc zero-≤ , q , cong (λ b → b and false or not b and true) q  
... | inj₁ q with parity-even (a ∘ suc) n ev (sym (cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) q) ∙ eqf) eqt
... | k , false , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r
... | k , true , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r

parity-odd : (a : ℕ → Bool) 
  → ∀ n → isOdd n
  → parity a true n ≡ false → a n ≡ false
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ b) × (parity a true k ≡ true)
parity-odd' : (a : ℕ → Bool) 
  → ∀ n → isEven n
  → parity a false n ≡ false → a n ≡ false
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ not b) × (parity a false k ≡ true)

parity-odd a (suc n) (suc odd) eqt eqf with dichotomyBool (a 0)
... | inj₁ q = 0 , true , zero , suc-≤-suc zero-≤ , q , cong (λ b → b and true or not b and false) q
... | inj₂ q with parity-odd' (a ∘ suc) n odd ((sym (cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false n) q) ∙ eqt)) eqf
... | k , false , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r
... | k , true , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r

parity-odd' a zero zero eqt eqf =
  ⊥-rec (true≢false (sym (cong (λ b → b and false or not b and true) eqf) ∙ eqt))
parity-odd' a (suc n) (suc odd) eqt eqf with dichotomyBool (a 0)
... | inj₂ q = 0 , true , zero , suc-≤-suc zero-≤ , q , cong (λ b → b and false or not b and true) q
... | inj₁ q with parity-odd (a ∘ suc) n odd ((sym (cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) q) ∙ eqt)) eqf
... | k , false , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r
... | k , true , p , le , eq , r = _ , _ , suc p , suc-≤-suc le , eq , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r


{-
parity-even : (a : ℕ → Bool) (b : Bool)
  → ∀ n → isEven? b n
  → parity a b n ≡ false → a n ≡ true
  → Σ[ k ∈ ℕ ] Σ[ b' ∈ Bool ] (k < n) × (a k ≡ b' or b)
parity-even a true zero ev eqf eqt =
  ⊥-rec (true≢false (sym (cong (λ b → b and true or not b and false) eqt) ∙  eqf))
parity-even a b (suc n) ev eqf eqt with dichotomyBool (a 0)
parity-even a b (suc n) ev eqf eqt | inj₁ p = 0 , true , suc-≤-suc zero-≤ , {!!}
parity-even a false (suc n) (suc ev) eqf eqt | inj₂ p = {!!}
--  ⊥-rec (false≢true (sym (cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) p) ∙ eqf))
parity-even a true (suc n) (suc ev) eqf eqt | inj₂ p with parity-even (a ∘ suc) false n ev {!!} eqt
... | ih = {!!}
-}

-- parity-even a true p zero ev with p 0 zero
-- ... | q with a 0
-- ... | false = refl
-- ... | true = ⊥-rec (true≢false q)
-- parity-even a b p (suc n) ev with dichotomyBool (a 0)
-- parity-even a false p (suc n) (suc ev) | inj₁ q =
--   parity-even (a ∘ suc) true (λ k r → {!p (suc k) (suc r)!}) n ev
-- parity-even a true p (suc n) (suc ev) | inj₁ q = {!!}
-- parity-even a false p (suc n) (suc ev) | inj₂ q = {!!}
-- parity-even a true p (suc n) (suc ev) | inj₂ q = {!!}


{-
parity-even2 : (a : ℕ → Bool) (b : Bool)
  → ((n : ℕ) → isEven? b n → a n ≡ false)
  → ∀ n → isEven? b n → parity a b n ≡ false
parity-even2 a true p zero ev with dichotomyBool (a 0)
parity-even2 a true p zero ev | inj₁ q = ⊥-rec (false≢true (sym (p 0 zero) ∙ q))
parity-even2 a true p zero ev | inj₂ q = cong (λ b → b and true or not b and false) q
parity-even2 a b p (suc n) ev with dichotomyBool (a 0)
parity-even2 a false p (suc n) (suc ev) | inj₁ x =
  cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) x
  ∙ parity-even2 (a ∘ suc) true (λ n r → p (suc n) (suc r)) n ev
parity-even2 a false p (suc n) (suc ev) | inj₂ x = 
  cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) x
parity-even2 a true p (suc n) ev | inj₁ x = ⊥-rec (false≢true (sym (p 0 zero) ∙ x))
parity-even2 a true p (suc n) (suc ev) | inj₂ x = 
  cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false n) x
  ∙ parity-even2 (a ∘ suc) false (λ n r → p (suc n) (suc r)) n ev
-}

module ToInjective (llpo : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
                        → ∥ (∀ n → isEven n → a n ≡ false) ⊎ (∀ n → isOdd n → a n ≡ false) ∥)
                  (cc : (P : ℕ → Type) → (∀ n → ∥ P n ∥) → ∥ (∀ n → P n) ∥) where

{-
  complete : ∀ x s (z : ℕ → ωPfin)
    → (∀ n → ⟨ z n ∈ₛ s ⟩)
    → (∀ n → z n .fst n ≡ x .fst n)
    → ⟨ x ∈ₛ s ⟩
  complete x =
    elimPfinProp
      {!!} 
      (λ z p q → p 0)
      (λ y z p q →
        ∥map∥
          (λ p → Σ≡Prop {!!}
            (funExt (λ n → sym (q n) ∙ funExt⁻ (cong fst (p n)) n)))
          (cc _ p))
      λ {s}{t} ihs iht z p q → ∥map∥ (λ p → lem {s}{t} ihs iht z p q) (cc _ p) 
    where
      lem : {s t : Pfin ωPfin}
        → (ihs : (z : ℕ → ωPfin) → (∀ n → ⟨ z n ∈ₛ s ⟩) → (∀ n → z n .fst n ≡ x .fst n) → ⟨ x ∈ₛ s ⟩)
        → (iht : (z : ℕ → ωPfin) → (∀ n → ⟨ z n ∈ₛ t ⟩) → (∀ n → z n .fst n ≡ x .fst n) → ⟨ x ∈ₛ t ⟩)
        → (z : ℕ → ωPfin) → (∀ n → ⟨ z n ∈ₛ s ⟩ ⊎ ⟨ z n ∈ₛ t ⟩) → (∀ n → z n .fst n ≡ x .fst n)
        → ⟨ x ∈ₛ s ⟩ ⊎ ⟨ x ∈ₛ t ⟩
      lem {s}{t} ihs iht z p q = {!!}
        where
          a : ℕ → Bool
          a n = rec⊎ (λ _ → true) (λ _ → false) (p n)

          par : ℕ → Bool
          par = parity a true

          magic : ∥ ((n : ℕ) → isEven n → par n ≡ false) ⊎
                    ((n : ℕ) → isOdd n → par n ≡ false) ∥
          magic = llpo par (parity-prop _ true)

          case1 : (∀ n → isEven n → par n ≡ false)
            → ∀ n → isEven n → (mn : ⟨ z n ∈ₛ s ⟩) → p n ≡ inj₁ mn → ⊥
          case1 r n ev mn eq with parity-even a n ev (r n ev) (cong (rec⊎ _ _) eq)
          ... | k , true , evk , le , c , eqp = false≢true (sym (r k evk) ∙ eqp)
          ... | k , false , evk , le , c , eqp with p k
          ... | inj₁ x = true≢false c
          ... | inj₂ mk = {!mn!}
-}

  minj-lem3 : ∀ s t 
    → m s ≡ m t
    → ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
  minj-lem3 s t eq n =
    cong (λ f → mapPfin f s) (funExt (λ x → sym (x .snd n)))
    ∙ sym (mapPfinComp s)
    ∙ funExt⁻ (cong fst eq) (suc n)
    ∙ mapPfinComp t
    ∙ cong (λ f → mapPfin f t) (funExt (λ x → x .snd n))

  minj-lem2 : ∀ x t
    → (∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t ⟩)
    → ⟨ x ∈ₛ t ⟩
  minj-lem2 x = elimPfinProp (λ t → _ , isPropΠ (λ _ → snd (x ∈ₛ t)))
    (λ p → p 0)
    (λ a p → ∥map∥ (λ q → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _)) (funExt q)) (cc _ p))
    λ {s1}{s2} ih1 ih2 p → ∥rec∥ propTruncIsProp (lem s1 s2 ih1 ih2) (cc _ p)
    where
      lem : (s1 s2 : Pfin ωPfin)
        → ((∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩) → ⟨ x ∈ₛ s1 ⟩)
        → ((∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩) → ⟨ x ∈ₛ s2 ⟩)
        → (∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩ ⊎ ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩)
        → ∥ ⟨ x ∈ₛ s1 ⟩ ⊎ ⟨ x ∈ₛ s2 ⟩ ∥
      lem s1 s2 ih1 ih2 p =
        ∥map∥ (map⊎ (ih1 ∘ case-even-gen) (ih2 ∘ case-odd-gen)) magic
        where
          a : ℕ → Bool
          a n with decEven n
          ... | inj₁ ev = not (Dec→Bool (dec∈ₛ (iPfinDecEq n) (x .fst n) (mapPfin (λ x → x .fst n) s1)))
          ... | inj₂ odd = Dec→Bool (dec∈ₛ (iPfinDecEq n) (x .fst n) (mapPfin (λ x → x .fst n) s2))

          par : ℕ → Bool
          par = parity a true

          magic : ∥ ((n : ℕ) → isEven n → par n ≡ false) ⊎
                    ((n : ℕ) → isOdd n → par n ≡ false) ∥
          magic = llpo par (parity-prop _ true)

          a-even : ∀ n → isEven n
            → (⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩ → ⊥) 
            → a n ≡ true
          a-even n ev mn with decEven n
          ... | inj₂ odd = ⊥-rec (even-not-odd ev odd)
          ... | inj₁ _ with dec∈ₛ (iPfinDecEq n) (x .fst n) (mapPfin (λ x₂ → x₂ .fst n) s1)
          ... | yes q = ⊥-rec (mn q)
          ... | no ¬q = refl

          a-odd : ∀ n → isOdd n
            → (⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩ → ⊥) 
            → a n ≡ false
          a-odd n odd mn with decEven n
          ... | inj₁ x = ⊥-rec (even-not-odd x odd)
          ... | inj₂ q with dec∈ₛ (iPfinDecEq n) (x .fst n) (mapPfin (λ x₂ → x₂ .fst n) s2)
          ... | yes p = ⊥-rec (mn p)
          ... | no ¬p = refl

          ¬¬case-even : (∀ n → isEven n → par n ≡ false)
            → ∀ n → isEven n → (⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩ → ⊥) → ⊥
          ¬¬case-even r n evn ¬mn with parity-even a n evn (r n evn) (a-even n evn ¬mn)
          ... | k , true , evk , le , c , eqk = false≢true (sym (r k evk) ∙ eqk)
          ... | k , false , oddk , le , c , eqk with decEven k
          ... | inj₁ evk = ⊥-rec (even-not-odd evk oddk)
          ... | inj₂ _ with dec∈ₛ (iPfinDecEq k) (x .fst k) (mapPfin (λ n₁ → n₁ .fst k) s2)
          ... | yes mk = ⊥-rec (true≢false c)
          ... | no ¬mk with p n
          ... | inj₁ mn = ¬mn mn
          ... | inj₂ mn = ¬mk
            (∥rec∥ (snd (x .fst k ∈ₛ mapPfin (λ x → x .fst k) s2))
               (λ { (y , my , eqy) →
                 subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst k) s2 ⟩)
                      (sym (ires-eq iPfin-ch y n k (<-weaken le))
                       ∙ cong (ires iPfin-ch n k (<-weaken le)) eqy
                       ∙ ires-eq iPfin-ch x n k (<-weaken le))
                      (∈ₛmapPfin _ _ s2 my) } )
               (pre∈ₛmapPfin _ _ s2 mn))


          ¬¬case-odd : (∀ n → isOdd n → par n ≡ false)
            → ∀ n → isOdd n → (⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩ → ⊥) → ⊥
          ¬¬case-odd r n oddn ¬mn with parity-odd a n oddn (r n oddn) (a-odd n oddn ¬mn)
          ... | k , false , oddk , le , c , eqk = false≢true (sym (r k oddk) ∙ eqk)
          ... | k , true , evk , le , c , eqk with decEven k
          ... | inj₂ oddk = ⊥-rec (even-not-odd evk oddk)
          ... | inj₁ _ with dec∈ₛ (iPfinDecEq k) (x .fst k) (mapPfin (λ n₁ → n₁ .fst k) s1)
          ... | yes mk = ⊥-rec (false≢true c)
          ... | no ¬mk with p n
          ... | inj₂ mn = ¬mn mn
          ... | inj₁ mn = ¬mk 
            (∥rec∥ (snd (x .fst k ∈ₛ mapPfin (λ x → x .fst k) s1))
               (λ { (y , my , eqy) →
                 subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst k) s1 ⟩)
                       (sym (ires-eq iPfin-ch y n k (<-weaken le))
                        ∙ cong (ires iPfin-ch n k (<-weaken le)) eqy
                        ∙ ires-eq iPfin-ch x n k (<-weaken le))
                       (∈ₛmapPfin _ _ s1 my) } )
               (pre∈ₛmapPfin _ _ s1 mn))

          case-even : (∀ n → isEven n → par n ≡ false)
            → ∀ n → isEven n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩
          case-even r n ev with dec∈ₛ (iPfinDecEq n) (x .fst n) (mapPfin (λ n₁ → n₁ .fst n) s1)
          ... | yes p = p
          ... | no ¬p = ⊥-rec (¬¬case-even r n ev ¬p)

          case-even-gen : (∀ n → isEven n → par n ≡ false)
            → ∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩
          case-even-gen r n with decEven n
          ... | inj₁ ev = case-even r n ev
          ... | inj₂ odd = ∥rec∥ (snd (x .fst n ∈ₛ mapPfin (λ x → x .fst n) s1))
            (λ { (y , my , eqy) →
              subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) s1 ⟩)
                    (sym (y .snd n) ∙ cong (iMapPfin n) eqy ∙ x .snd n)
                    (∈ₛmapPfin _ _ s1 my) })
            (pre∈ₛmapPfin _ _ s1 (case-even r (suc n) (suc odd)))

          case-odd : (∀ n → isOdd n → par n ≡ false)
            → ∀ n → isOdd n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩
          case-odd r n ev with dec∈ₛ (iPfinDecEq n) (x .fst n) (mapPfin (λ n₁ → n₁ .fst n) s2)
          ... | yes p = p
          ... | no ¬p = ⊥-rec (¬¬case-odd r n ev ¬p)

          case-odd-gen : (∀ n → isOdd n → par n ≡ false)
            → ∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩
          case-odd-gen r n with decEven n
          ... | inj₂ odd = case-odd r n odd
          ... | inj₁ ev = ∥rec∥ (snd (x .fst n ∈ₛ mapPfin (λ x → x .fst n) s2))
            (λ { (y , my , eqy) →
              subst (λ z → ⟨ z ∈ₛ mapPfin (λ x → x .fst n) s2 ⟩)
                    (sym (y .snd n) ∙ cong (iMapPfin n) eqy ∙ x .snd n)
                    (∈ₛmapPfin _ _ s2 my) })
            (pre∈ₛmapPfin _ _ s2 (case-odd r (suc n) (suc ev)))

  minj-lem : ∀ s t
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → s ⊆ t
  minj-lem = elimPfinProp (λ _ → _ , isPropΠ (λ t → isPropΠ (λ _ → isPropΠ (λ x → isPropΠ (λ _ → snd (x ∈ₛ t))))))
    (λ t p x mx → ⊥-rec mx)
    (λ a t p x mx → minj-lem2 x t (λ n → p n (x .fst n) (∥map∥ (cong (λ z → z .fst n)) mx)))
    (λ ih1 ih2 t p x → ∥rec∥ (snd (x ∈ₛ t))
      (λ { (inj₁ mx) → ih1 t (λ n y my → p n y (inl my)) x mx
         ; (inj₂ mx) → ih2 t (λ n y my → p n y (inr my)) x mx }))


  minj : ∀ s t → m s ≡ m t → s ≡ t
  minj s t eq =
    antisym⊆ (minj-lem s t (λ n → subst (mapPfin (λ x → x .fst n) s ⊆_) (minj-lem3 s t eq n) (λ _ mx → mx)))
             (minj-lem t s (λ n → subst (mapPfin (λ x → x .fst n) t ⊆_) (minj-lem3 t s (sym eq) n) (λ _ mx → mx)))

{-
          --with parity-even a n ev (r n ev) (cong (rec⊎ _ _) eq)
          --... | k , true , evk , le , c , eqp = {!!} -- false≢true (sym (r k evk) ∙ eqp)
          --... | k , false , evk , le , c , eqp = ?
--          with p k
--          ... | inj₁ x = true≢false c
--          ... | inj₂ mk = {!mk!} 

-- module ToInjectivity (complete2 : ∀ x s1 s2 (z : ℕ → ωPfin)
--                        → (∀ n → ⟨ z n ∈ₛ (s1 ∪ s2) ⟩)
--                        → (∀ n → z n .fst n ≡ x .fst n)
--                        → ⟨ x ∈ₛ (s1 ∪ s2) ⟩)
--                      (cc : (P : ℕ → Type) → (∀ n → ∥ P n ∥) → ∥ (∀ n → P n) ∥) where
                    
--   minj' : ∀ s t 
--     → m s ≡ m t
--     → ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
--                      ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
--   minj' s t eq n =
--     cong (λ f → mapPfin f s) (funExt (λ x → sym (x .snd n)))
--     ∙ sym (mapPfinComp s)
--     ∙ funExt⁻ (cong fst eq) (suc n)
--     ∙ mapPfinComp t
--     ∙ cong (λ f → mapPfin f t) (funExt (λ x → x .snd n))

--   minj-lem3 : ∀ (x : ωPfin) t
--     → (∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t ⟩)
--     → ∃[ z ∈ (ℕ → ωPfin) ] (∀ n → ⟨ z n ∈ₛ t ⟩  × (z n .fst n ≡ x .fst n))
--   minj-lem3 x t p = ∥map∥ (λ f → (λ n → f n .fst) , λ n → f n .snd .fst , f n .snd .snd) (cc _ lem)
--     where
--       lem : ∀ n → ∃[ z ∈ ωPfin ] ⟨ z ∈ₛ t ⟩  × (z .fst n ≡ x .fst n)
--       lem n = pre∈ₛmapPfin _ _ t (p n)


--   minj-lem2 : ∀ x t
--     → (∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t ⟩)
--     → ⟨ x ∈ₛ t ⟩
--   minj-lem2 x = elimPfinProp (λ t → _ , isPropΠ (λ _ → snd (x ∈ₛ t)))
--     (λ p → p 0)
--     (λ a p → ∥map∥ (λ q → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _)) (funExt q)) (cc _ p))
--     λ {s1}{s2} ih1 ih2 p → ∥rec∥ propTruncIsProp
--       (λ { (z , q) → complete2 x s1 s2 z (λ n → q n .fst) (λ n → q n .snd) })
--       (minj-lem3 x (s1 ∪ s2) p) 

--   minj-lem : ∀ s t
--     → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
--                      ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
--     → s ⊆ t
--   minj-lem = elimPfinProp (λ _ → _ , isPropΠ (λ t → isPropΠ (λ _ → isPropΠ (λ x → isPropΠ (λ _ → snd (x ∈ₛ t))))))
--     (λ t p x mx → ⊥-rec mx)
--     (λ a t p x mx → minj-lem2 x t (λ n → p n (x .fst n) (∥map∥ (cong (λ z → z .fst n)) mx)))
--     (λ ih1 ih2 t p x → ∥rec∥ (snd (x ∈ₛ t))
--       (λ { (inj₁ mx) → ih1 t (λ n y my → p n y (inl my)) x mx
--          ; (inj₂ mx) → ih2 t (λ n y my → p n y (inr my)) x mx }))

--   minj : ∀ s t → m s ≡ m t → s ≡ t
--   minj s t eq =
--     antisym⊆ (minj-lem s t (λ n → subst (mapPfin (λ x → x .fst n) s ⊆_) (minj' s t eq n) (λ _ mx → mx)))
--              (minj-lem t s (λ n → subst (mapPfin (λ x → x .fst n) t ⊆_) (minj' t s (sym eq) n) (λ _ mx → mx)))





-- -- misInjective : ∀ s t → m s ≡ m t → s ≡ t
-- -- misInjective _ _ eq =
-- --   lem-injective-lim iPfin-ch _ _
-- --     {!!}
-- --     _ _ eq
-}


iPfin2 : ℕ → Type 
iPfin2 zero = ωPfin
iPfin2 (suc n) = Pfin (iPfin2 n)

isSetiPfin2 : ∀ n → isSet (iPfin2 n)
isSetiPfin2 zero = isSetωPfin
isSetiPfin2 (suc n) = trunc

iMapPfin2 : ∀ n → iPfin2 (suc n) → iPfin2 n
iMapPfin2 zero = m
iMapPfin2 (suc n) = mapPfin (iMapPfin2 n)

iPfin2-ch : ωChain₀
iPfin2-ch = iPfin2 , iMapPfin2

-- the limit of the ω-chain iPfin2-ch
ωPfin2 : Type
ωPfin2 = ωLimit iPfin2-ch

path2 : ∀ n → iPfin2 n
path2 zero = path-ch
path2 (suc n) = η (path2 n)

path2-res : ∀ n → iMapPfin2 n (path2 (suc n)) ≡ path2 n
path2-res zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _)) (funExt path-res)
path2-res (suc n) = cong η (path2-res n)

path2-ch : ωPfin2
path2-ch = path2 , path2-res

path2? : (a : ℕ → Bool) → ∀ n → iPfin2 n
path2? a zero = path?-ch a
path2? a (suc n) = if a 0 then ø else η (path2? (a ∘ suc) n)

path2?-res : (a : ℕ → Bool) 
  → ∀ n → iMapPfin2 n (path2? a (suc n)) ≡ path2? a n
path2?-res a zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
  (funExt (λ n → cong (iMapPfin n) (lem n (a 0)) ∙ path?-res a n))
  where
    lem : ∀ n → (b : Bool)
      → mapPfin (proj iPfin-ch n) (if b then ø else η (path?-ch (a ∘ suc)))
        ≡ (if b then ø else η (path? (a ∘ suc) n))
    lem n false = refl
    lem n true = refl
path2?-res a (suc n) with a 0
... | false = cong η (path2?-res (a ∘ suc) n)
... | true = refl

path2?-ch : (a : ℕ → Bool) → ωPfin2
path2?-ch a = path2? a , path2?-res a

path2?? : (a : ℕ → Bool) → Bool → ∀ n → iPfin2 n
path2?? a b zero = path??-ch a b
path2?? a b (suc n) =
  if a 0 and b then ø else η (path2?? (a ∘ suc) (not b) n)

path2??-res : (a : ℕ → Bool) (b : Bool)
  → ∀ n → iMapPfin2 n (path2?? a b (suc n)) ≡ path2?? a b n
path2??-res a b zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
  (funExt (λ n → cong (iMapPfin n) (lem n b (a 0)) ∙ path??-res a b n))
  where
    lem : ∀ n → (b b' : Bool)
      → mapPfin (proj iPfin-ch n) (if b' and b then ø else η (path??-ch (a ∘ suc) (not b)))
        ≡ (if b' and b then ø else η (path?? (a ∘ suc) (not b) n))
    lem n false false = refl
    lem n true false = refl
    lem n false true = refl
    lem n true true = refl
path2??-res a b (suc n) with a 0 | b
... | false | false = cong η (path2??-res (a ∘ suc) true n)
... | false | true = cong η (path2??-res (a ∘ suc) false n)
... | true | false = cong η (path2??-res (a ∘ suc) true n)
... | true | true = refl

path2??-ch : (a : ℕ → Bool) → Bool → ωPfin2
path2??-ch a b = path2?? a b , path2??-res a b


module FromInjectivity0 (minj : (s t : ωPfin2) → m (s .fst 1) ≡ m (t .fst 1) → s ≡ t) where

  complete' : ∀ s t 
    → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
    → m s ≡ m t
  complete' s t p = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
    (funExt (λ { zero → refl ;
                 (suc n) → antisym⊆
                   (λ x mx → ∥rec∥ (snd ((x ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) t))))
                     (λ { (y , my , eq) → subst (λ z → ⟨ x ∈ₛ z ⟩)
                                                 (sym (mapPfinComp t
                                                   ∙ cong (λ f → mapPfin f t) (funExt (λ z → z .snd n))
                                                   ∙ sym (p n)
                                                   ∙ cong (λ f → mapPfin f s) (sym (funExt (λ z → z .snd n)))
                                                   ∙ sym (mapPfinComp s)))
                                                 (subst (λ z → ⟨ z ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) s) ⟩)
                                                        eq
                                                        (∈ₛmapPfin (iMapPfin n) y (mapPfin (proj iPfin-ch (suc n)) s) my)) })
                     (pre∈ₛmapPfin (iMapPfin n) x (mapPfin (proj iPfin-ch (suc n)) s) mx))
                   (λ x mx → ∥rec∥ (snd ((x ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) s))))
                     (λ { (y , my , eq) → subst (λ z → ⟨ x ∈ₛ z ⟩)
                                                 (sym (mapPfinComp s
                                                   ∙ cong (λ f → mapPfin f s) (funExt (λ z → z .snd n))
                                                   ∙ p n
                                                   ∙ cong (λ f → mapPfin f t) (sym (funExt (λ z → z .snd n)))
                                                   ∙ sym (mapPfinComp t)))
                                                 (subst (λ z → ⟨ z ∈ₛ mapPfin (iMapPfin n) (mapPfin (proj iPfin-ch (suc n)) t) ⟩)
                                                        eq
                                                        (∈ₛmapPfin (iMapPfin n) y (mapPfin (proj iPfin-ch (suc n)) t) my)) })
                     (pre∈ₛmapPfin (iMapPfin n) x (mapPfin (proj iPfin-ch (suc n)) t) mx))}))


  joinω : (x y : ∀ n → iPfin n) → ∀ n → iPfin n
  joinω x y zero = tt
  joinω x y (suc n) = η (x n) ∪ η (y n)

  joinω-res : (x y : ωPfin)
    → ∀ n → iMapPfin n (joinω (x .fst) (y .fst) (suc n)) ≡ joinω (x .fst) (y .fst) n
  joinω-res x y zero = refl
  joinω-res x y (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong η (y .snd n))

  joinω-ch : (x y : ωPfin) → ωPfin
  joinω-ch x y = joinω (x .fst) (y .fst) , joinω-res x y

  joinω2 : (x y : ∀ n → iPfin2 n) → ∀ n → iPfin2 n
  joinω2 x y zero = joinω-ch (x 0) (y 0)
  joinω2 x y (suc n) = η (x n) ∪ η (y n)

  joinω2-res : (x y : ωPfin2)
    → ∀ n → iMapPfin2 n (joinω2 (x .fst) (y .fst) (suc n)) ≡ joinω2 (x .fst) (y .fst) n
  joinω2-res x y zero =
    Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
           (funExt (joinω-res (x .fst 0) (y .fst 0)))
  joinω2-res x y (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong η (y .snd n))

  joinω2-ch : (x y : ωPfin2) → ωPfin2
  joinω2-ch x y = joinω2 (x .fst) (y .fst) , joinω2-res x y

  3joinω : (x y z : ∀ n → iPfin n) → ∀ n → iPfin n
  3joinω x y z zero = tt
  3joinω x y z (suc n) = η (x n) ∪ (η (y n) ∪ η (z n))

  3joinω-res : (x y z : ωPfin)
    → ∀ n → iMapPfin n (3joinω (x .fst) (y .fst) (z .fst) (suc n)) ≡ 3joinω (x .fst) (y .fst) (z .fst) n
  3joinω-res x y z zero = refl
  3joinω-res x y z (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong₂ _∪_ (cong η (y .snd n)) (cong η (z .snd n)))

  3joinω-ch : (x y z : ωPfin) → ωPfin
  3joinω-ch x y z = 3joinω (x .fst) (y .fst) (z .fst) , 3joinω-res x y z

  3joinω2 : (x y z : ∀ n → iPfin2 n) → ∀ n → iPfin2 n
  3joinω2 x y z zero = 3joinω-ch (x 0) (y 0) (z 0)
  3joinω2 x y z (suc n) = η (x n) ∪ (η (y n) ∪ η (z n))

  3joinω2-res : (x y z : ωPfin2)
    → ∀ n → iMapPfin2 n (3joinω2 (x .fst) (y .fst) (z .fst) (suc n)) ≡ 3joinω2 (x .fst) (y .fst) (z .fst) n
  3joinω2-res x y z zero =
    Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
           (funExt (3joinω-res (x .fst 0) (y .fst 0) (z .fst 0)))
  3joinω2-res x y z (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong₂ _∪_ (cong η (y .snd n)) (cong η (z .snd n)))

  3joinω2-ch : (x y z : ωPfin2) → ωPfin2
  3joinω2-ch x y z = 3joinω2 (x .fst) (y .fst) (z .fst) , 3joinω2-res x y z

  complete : (x : ωPfin2) (y1 y2 : ωPfin2) (z : ℕ → ωPfin)
    → (∀ n → (z n ≡ y1 .fst 0) ⊎ (z n ≡ y2 .fst 0))
    → (∀ n → z n .fst n ≡ x .fst 0 .fst n)
    → ⟨ x .fst 0 ∈ₛ (η (y1 .fst 0) ∪ η (y2 .fst 0)) ⟩
  complete x y1 y2 z p q =
    subst (λ z → ⟨ x .fst 0 ∈ₛ z ⟩) (funExt⁻ (cong fst (minj s t (complete' (s .fst 1) (t .fst 1) eq))) 1) (inl ∣ refl ∣)
    where
      t : ωPfin2
      t = joinω2-ch y1 y2

      s : ωPfin2
      s = 3joinω2-ch x y1 y2

      sub : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) (s .fst 1)
                    ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) (t .fst 1)
      sub zero a _ = ∣ inj₁ ∣ refl ∣ ∣
      sub (suc n) a = ∥rec∥ propTruncIsProp
       (λ { (inj₁ r) →
                  ∥map∥ (λ eq → map⊎ (λ eq' → ∣ eq ∙ sym (q (suc n)) ∙ cong (λ w → w .fst (suc n)) eq' ∣)
                                     (λ eq' → ∣ eq ∙ sym (q (suc n)) ∙ cong (λ w → w .fst (suc n)) eq' ∣)
                                     (p (suc n)))
                        r ;
            (inj₂ r) → r })

      eq : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) (s .fst 1)
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) (t .fst 1)
      eq n = antisym⊆ (sub n) (λ a → inr)


  llpo : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
    → ∥ (∀ n → isEven n → a n ≡ false) ⊎ (∀ n → isOdd n → a n ≡ false) ∥
  llpo a aP = 
    ∥rec∥ propTruncIsProp
      (λ { (inj₁ p) →
             ∥map∥ (λ eq → inj₁ (λ n ev → rec⊎ (λ q → ⊥-rec (case1 eq n ev q)) (λ q → q) (dichotomyBool (a n))))
                   p
         ; (inj₂ p) → 
             ∥map∥ (λ eq → inj₂ (λ n odd → rec⊎ (λ q → ⊥-rec (case2 eq n odd q)) (λ q → q) (dichotomyBool (a n))))
                   p })
      (complete x y1 y2 z lem1 lem2)
    where
      y1 : ωPfin2
      y1 = path2-ch
      
      y2 : ωPfin2
      y2 = path2?-ch a

      z : ℕ → ωPfin
      z = seq-ch a path-ch (path?-ch a) true

      x : ωPfin2
      x = path2??-ch a true

      lem1 : ∀ n → (z n ≡ y1 .fst 0) ⊎ (z n ≡ y2 .fst 0)
      lem1 = seq-ch-cases a _ _ true

      lem2 : ∀ n → z n .fst n ≡ x .fst 0 .fst n
      lem2 n = seq-ch-path?? a aP n

      case1 : x .fst 0 ≡ y1 .fst 0 → ∀ n → isEven n → a n ≡ true → ⊥
      case1 eqx n ev eq = false≢true (sym (path?≠path a aP n bad) ∙ eq) 
        where
          bad : path? a (suc n) ≡ path (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem2 a path-ch (path?-ch a) true (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ seq-ch-path?? a aP (suc n)
            ∙ funExt⁻ (cong fst eqx) (suc n)

      case2 : x .fst 0 ≡ y2 .fst 0 → ∀ n → isOdd n → a n ≡ true → ⊥
      case2 eqx n ev eq = false≢true (sym (path?≠path a aP n (sym bad)) ∙ eq) 
        where
          bad : path (suc n) ≡ path? a (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem3 a aP path-ch (path?-ch a) false (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ seq-ch-path?? a aP (suc n)
            ∙ funExt⁻ (cong fst eqx) (suc n)



-- iMapPfin2isInjective : ∀ n (x y : iPfin2 (suc n))
--   → iMapPfin2 n x ≡ iMapPfin2 n y → x ≡ y
-- iMapPfin2isInjective zero x y eq = misInjective x y eq
-- iMapPfin2isInjective (suc n) x y eq =
--   mapPfinInj (iMapPfin2 n) (iMapPfin2isInjective n) x y eq

-- u : ∀ n → iPfin2 n → ωPfin
-- u zero x = x
-- u (suc n) x = u n (iMapPfin2 n x)

-- uisInjective : ∀ n (x y : iPfin2 n)
--   → u n x ≡ u n y → x ≡ y
-- uisInjective zero x y eq = eq
-- uisInjective (suc n) x y eq =
--   iMapPfin2isInjective n _ _ (uisInjective n _ _ eq)

-- uLem : ∀ (x : ωPfin2) n
--   → u n (iMapPfin2 n (x .fst (suc n))) ≡ m (x .fst 1)
-- uLem x zero = refl
-- uLem x (suc n) = cong (λ z → u n (iMapPfin2 n z)) (x .snd (suc n)) ∙ uLem x n

-- uLem2 : ∀ (x : ×pℕ u) n
--   → u (suc n) (x .fst (suc n)) ≡ u n (x .fst n)
-- uLem2 x zero = x .snd 0
-- uLem2 (x , p) (suc n) = uLem2 ((λ n → iMapPfin2 n (x (suc n))) , λ n → p (suc n) ∙ sym (p 0)) n

-- -- uLem2-sh : ∀ (x : ×pℕ {!!}) n
-- --   → u (suc n) (x .fst (suc n)) ≡ u n (x .fst n)

-- -- subtypeEquiv : {A : Type} {P Q : A → Type}
-- --   → (∀ a → isProp (P a)) → (∀ a → isProp (Q a))
-- --   → (∀ {a} → P a → Q a) → (∀ {a} → Q a → P a)
-- --   → Σ A P ≃ Σ A Q
-- -- subtypeEquiv pP pQ P2Q Q2P = Σ-cong-equiv-snd {!!}
-- --   (λ x → x .fst , P2Q (x .snd)) ,
-- --   record { equiv-proof = λ y → ((y .fst , Q2P (y .snd)) ,
-- --                                  Σ≡Prop pQ refl) ,
-- --                                 λ z → Σ≡Prop {!!} {!!} }  

-- ωPfin2-iso-×pℕ : Iso (ωPfin2) (×pℕ u)
-- ωPfin2-iso-×pℕ = Σ-cong-iso-snd
--   λ x → iso (λ p n → uLem (x , p) n ∙ p 0)
--              (λ q n → uisInjective n _ _ (uLem2 (x , q) n))
--              (λ _ → isPropΠ (λ _ → isSetωPfin _ _) _ _)
--              λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _) _ _

-- ωPfin2≃×pℕ : ωPfin2 ≃ ×pℕ u
-- ωPfin2≃×pℕ = isoToEquiv ωPfin2-iso-×pℕ

-- Pfin-iso : {A B : Type} → Iso A B → Iso (Pfin A) (Pfin B)
-- Pfin-iso AisoB =
--   iso (mapPfin (Iso.fun AisoB))
--       (mapPfin (Iso.inv AisoB))
--       (λ x → mapPfinComp x ∙ (λ i → mapPfin (λ y → Iso.rightInv AisoB y i) x) ∙ mapPfinId x)
--       λ x → mapPfinComp x ∙ (λ i → mapPfin (λ y → Iso.leftInv AisoB y i) x) ∙ mapPfinId x

-- Pfin≃ : {A B : Type} → A ≃ B → Pfin A ≃ Pfin B
-- Pfin≃ eq = isoToEquiv (Pfin-iso (equivToIso eq))

-- -- the limit of the shifted (ω+ω)-chain
-- ωPfin2Sh : Type
-- ωPfin2Sh = ωLimit (shift iPfin2-ch)


-- ×pℕSh-iso-ωPfin2Sh : Iso (×pℕ (mapPfin ∘ u)) ωPfin2Sh
-- ×pℕSh-iso-ωPfin2Sh = Σ-cong-iso-snd
--   λ x → iso (λ p n → mapPfinInj (u n) (uisInjective n) _ _ (mapPfinComp (x (suc n)) ∙ lem x p n))
--              (λ p n → lem2 x (λ n → sym (mapPfinComp (x (suc n))) ∙ cong (mapPfin (u n)) (p n)) n)
--              (λ _ → isPropΠ (λ _ → trunc _ _) _ _)
--              λ _ → isPropΠ (λ _ → trunc _ _) _ _
--   where
--     lem : (x : ∀ n → Pfin (iPfin2 n))
--       → (∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u 0) (x 0))
--       → ∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u n) (x n)
--     lem x p zero = p 0
--     lem x p (suc n) = p (suc n) ∙ sym (p n) 

--     lem2 : (x : ∀ n → Pfin (iPfin2 n))
--       → (∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u n) (x n))
--       → ∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u 0) (x 0)
--     lem2 x p zero = p 0
--     lem2 x p (suc n) = p (suc n) ∙ lem2 x p n


-- -- ×pℕshift-iso : Iso (×pℕ (mapPfin ∘ u)) (×pℕ u)
-- -- ×pℕshift-iso =
-- --   iso (λ x → {!x .fst !} , {!!})
-- --       (λ x → x .fst ∘ suc , λ n → {!x .snd (suc n)!})
-- --       {!!}
-- --       {!!}



-- ×pℕSh≃ωPfin2Sh : ×pℕ (mapPfin ∘ u) ≃ ωPfin2Sh
-- ×pℕSh≃ωPfin2Sh = isoToEquiv ×pℕSh-iso-ωPfin2Sh

-- ωPfin22Sh≃ωPfin2 : ωPfin2Sh ≃ ωPfin2
-- ωPfin22Sh≃ωPfin2 = invEquiv (shift≃ iPfin2-ch isSetiPfin2)

-- τ-equiv : Pfin ωPfin2 ≃ ωPfin2
-- τ-equiv =
--   compEquiv (Pfin≃ ωPfin2≃×pℕ)
--     (compEquiv (Pfin×pℕ {!!} (λ _ → trunc) isSetωPfin u (λ n → uisInjective (suc n)))
--       (compEquiv ×pℕSh≃ωPfin2Sh ωPfin22Sh≃ωPfin2))

ConePfinωPfin2 : Cone iPfin2-ch (Pfin ωPfin2)
ConePfinωPfin2 =
  (λ n x → iMapPfin2 n (mapPfin (proj iPfin2-ch n) x)) ,
  λ n x → cong (iMapPfin2 n)
    (mapPfinComp x ∙ cong (λ f → mapPfin f x)
      (funExt (λ y → y .snd n)))

τ-1 : Pfin ωPfin2 → ωPfin2
τ-1 = Iso.inv (AdjLim iPfin2-ch _) ConePfinωPfin2

-- τ : ωPfin2 → Pfin ωPfin2
-- τ = invEq τ-equiv

-- τ-1≡ : τ-1 ≡ equivFun τ-equiv
-- τ-1≡ = funExt (λ x → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
--   (funExt (λ n → cong (iMapPfin2 n) (sym (mapPfinComp x)))))

-- module Finality (A : Type) (α : A → Pfin A)
--                 (αsim : A → ωPfin2) 
--                 (αsim-mor : ∀ a → τ (αsim a) ≡ mapPfin αsim (α a)) where

--   pα : ∀ n (a : A) → iPfin n
--   pα zero a = tt
--   pα (suc n) a = mapPfin (pα n) (α a)

--   pα-res : ∀ n (a : A) → iMapPfin n (mapPfin (pα n) (α a)) ≡ pα n a
--   pα-res zero a = refl
--   pα-res (suc n) a = mapPfinComp (α a) ∙ cong (λ f → mapPfin f (α a)) (funExt (pα-res n))

--   pα2 : ∀ n (a : A) → iPfin2 n
--   pα2 zero a = (λ n → pα n a) , λ n → pα-res n a 
--   pα2 (suc n) a = mapPfin (pα2 n) (α a)

--   pα2-res : ∀ n (a : A) → iMapPfin2 n (mapPfin (pα2 n) (α a)) ≡ pα2 n a
--   pα2-res zero a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin  _ _ _))
--     (funExt (λ n → cong (iMapPfin n) (mapPfinComp (α a)) ∙ pα-res n a))
--   pα2-res (suc n) a = mapPfinComp (α a) ∙ cong (λ f → mapPfin f (α a)) (funExt (pα2-res n))

--   coneA : Cone iPfin2-ch A
--   coneA = pα2 , pα2-res

--   αbar : A → ωPfin2
--   αbar = Iso.inv (AdjLim iPfin2-ch _) coneA

--   αbar-mor' : ∀ a → αbar a ≡ τ-1 (mapPfin αbar (α a))
--   αbar-mor' a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
--     (funExt (λ n → sym (cong (iMapPfin2 n) (mapPfinComp (α a)) ∙ pα2-res n a)))

--   αbar-mor : ∀ a → τ (αbar a) ≡ mapPfin αbar (α a)
--   αbar-mor a =
--       τ (αbar a)
--     ≡⟨ (λ i → τ (αbar-mor' a i)) ⟩
--       τ (τ-1 (mapPfin αbar (α a)))
--     ≡⟨ (λ i → τ (τ-1≡ i (mapPfin αbar (α a)))) ⟩
--       τ (equivFun τ-equiv (mapPfin αbar (α a)))
--     ≡⟨ (λ i → Iso.leftInv (equivToIso τ-equiv) (mapPfin αbar (α a)) i) ⟩
--       mapPfin αbar (α a)
--     ∎

--   αsim-mor' : ∀ a → αsim a ≡ τ-1 (mapPfin αsim (α a))
--   αsim-mor' a =
--       αsim a
--     ≡⟨ sym (Iso.rightInv (equivToIso τ-equiv) (αsim a)) ⟩
--       equivFun τ-equiv (τ (αsim a))
--     ≡⟨ (λ i → equivFun τ-equiv (αsim-mor a i) ) ⟩
--       equivFun τ-equiv (mapPfin αsim (α a))
--     ≡⟨ (λ i → τ-1≡ (~ i) (mapPfin αsim (α a))) ⟩
--       τ-1 (mapPfin αsim (α a))
--     ∎

--   αbar-eq : ∀ a n → αsim a .fst 0 .fst n ≡ pα n a
--   αbar-eq a zero = refl
--   αbar-eq a (suc n) = 
--     funExt⁻ (cong fst (funExt⁻ (cong fst (αsim-mor' a)) 0)) (suc n)
--     ∙ mapPfinComp ((mapPfin (proj iPfin2-ch 0) (mapPfin αsim (α a))))
--     ∙ mapPfinComp (mapPfin αsim (α a))
--     ∙ mapPfinComp (α a)
--     ∙ cong (λ f → mapPfin f (α a)) (funExt (λ x → αsim x .fst 0 .snd n ∙ αbar-eq x n))

--   αbar-eq2 : ∀ a n → αsim a .fst n ≡ pα2 n a
--   αbar-eq2 a zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
--     (funExt (αbar-eq a))
--   αbar-eq2 a (suc n) =
--     funExt⁻ (cong fst (αsim-mor' a)) (suc n)
--     ∙ mapPfinComp (mapPfin αsim (α a))
--     ∙ mapPfinComp (α a)
--     ∙ cong (λ f → mapPfin f (α a)) (funExt (λ x → αsim x .snd n ∙ αbar-eq2 x n))

--   αbar-uniq : ∀ a → αsim a ≡ αbar a
--   αbar-uniq a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
--     (funExt (αbar-eq2 a))



{-
iPfinEmb : ∀ k n → k ≤N n → iPfin k → iPfin n
iPfinEmb zero zero le x = tt
iPfinEmb zero (suc n) le x = ø
iPfinEmb (suc k) zero le x = ⊥-rec (¬-<-zero le)
iPfinEmb (suc k) (suc n) le x = mapPfin (iPfinEmb k n (pred-≤-pred le)) x

iPfinEmb≡ : ∀ {n k l} → k ≡ l
  → (lek : k ≤N n) (lel : l ≤N n)
  → (x : ∀ n → iPfin n)
  → iPfinEmb k n lek (x k) ≡ iPfinEmb l n lel (x l)
iPfinEmb≡ {n} {k} =
  J (λ l eq → (lek : k ≤N n) (lel : l ≤N n) →  (x : ∀ n → iPfin n)
       → iPfinEmb k n lek (x k) ≡ iPfinEmb l n lel (x l))
    λ lek lel x → cong (λ p → iPfinEmb k n p (x k)) {!!}

iPfinEmb-res : ∀ k n (lek : k ≤N n)
  → (x : iPfin k)
  → iMapPfin n (iPfinEmb k (suc n) (≤-suc lek) x) ≡ iPfinEmb k n lek x
iPfinEmb-res zero zero lek x = refl
iPfinEmb-res zero (suc n) lek x = refl
iPfinEmb-res (suc k) zero lek x = ⊥-rec (¬-<-zero lek)
iPfinEmb-res (suc k) (suc n) lek x =
  mapPfinComp x
  ∙ cong (λ f → mapPfin f x) (funExt (λ y →
      cong (iMapPfin n) (cong (λ p → iPfinEmb k (suc n) p y) {!!})
      ∙ iPfinEmb-res k n (pred-≤-pred lek) y))

iPfinEmbRefl : ∀ n → (x : iPfin n)
  → iPfinEmb n n ≤-refl x ≡ x
iPfinEmbRefl zero x = refl
iPfinEmbRefl (suc n) x =
  cong (λ f → mapPfin f x) (funExt (λ y →
    cong (λ p → iPfinEmb n n p y) {!!}
    ∙ iPfinEmbRefl n y))
  ∙ mapPfinId x


void : ∀ n → iPfin n
void zero = tt
void (suc n) = ø

void-res : ∀ n → iMapPfin n ø ≡ void n
void-res zero = refl
void-res (suc n) = refl

void-ch : ωPfin
void-ch = void , void-res

shiftη : (∀ n → iPfin n) → ∀ n → iPfin n
shiftη x zero = tt
shiftη x (suc n) = η (x n)

-}

{-
path?' : (a : ℕ → Bool) → ∀ n → iPfin n
path?' a zero = tt
path?' a (suc n) with a 0 ≟ true
... | yes p = ø
... | no ¬p = η (path?' (a ∘ suc) n)

path? : (a : ℕ → Bool) → ∀ n → iPfin n
path? a n with true-before? a n
... | yes (k , k≤n , eq) = iPfinEmb k n k≤n (path k)
... | no _ = path n


path?-res : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
  → ∀ n → iMapPfin n (path? a (suc n)) ≡ path? a n
path?-res a aP n with true-before? a (suc n)
... | yes (k , lek , eqk) with true-before? a n
... | yes (l , lel , eql) =
  cong (iMapPfin n) (iPfinEmb≡ (cong fst (aP (k , eqk) (l , eql))) lek (≤-suc lel) path)
  ∙ iPfinEmb-res l n lel (path l)
... | no ¬p =
  cong (iMapPfin n)
    (iPfinEmb≡ {!!} lek ≤-refl path
    ∙ cong η
      (cong (λ p → iPfinEmb n n p (path n)) {!!}
      ∙ iPfinEmbRefl n (path n)))
  ∙ path-res n
path?-res a aP n | no ¬p with true-before? a n
... | yes (k , k≤n , eq) = ⊥-rec (¬p (k , ≤-suc k≤n , eq))
... | no _ = path-res n

path?-ch : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true)) → ωPfin
path?-ch a aP = path? a , path?-res a aP

path?-ø : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
  → a 0 ≡ true → ∀ n → path? a n ≡ void n
path?-ø a aP eq0 n with true-before? a n
path?-ø a aP eq0 zero | yes (k , le , eqk) =
  iPfinEmb≡ (cong fst (aP (k , eqk) (0 , eq0))) le zero-≤ path
path?-ø a aP eq0 (suc n) | yes (k , le , eqk) = 
  iPfinEmb≡ (cong fst (aP (k , eqk) (0 , eq0))) le zero-≤ path
... | no p = ⊥-rec (p (0 , zero-≤ , eq0))

path?-η : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
  → a 0 ≡ false → ∀ n → path? a n ≡ shiftη (path? (a ∘ suc)) n
path?-η a aP eq0 n with true-before? a n
path?-η a aP eq0 zero | yes (zero , le , eqk) = refl
path?-η a aP eq0 zero | yes (suc k , le , eqk) = ⊥-rec (¬-<-zero le)
path?-η a aP eq0 (suc n) | yes (zero , le , eqk) = ⊥-rec {!!}
path?-η a aP eq0 (suc n) | yes (suc k , lek , eqk) with true-before? (a ∘ suc) n
... | yes (l , lel , eql) =
  cong η (iPfinEmb≡ (injSuc (cong fst (aP (suc k , eqk) (suc l , eql)))) (pred-≤-pred lek) lel path)
... | no p = ⊥-rec (p (k , pred-≤-pred lek , eqk))
path?-η a aP eq0 zero | no p = refl
path?-η a aP eq0 (suc n) | no p with true-before? (a ∘ suc) n
... | yes (k , le , eqk) = ⊥-rec (p (suc k , suc-≤-suc le , eqk))
... | no q = refl

path?≡ : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → path? a n ≡ path?' a n
path?≡ a aP 0 = refl
path?≡ a aP (suc n) with a 0 ≟ true
... | yes p = path?-ø a aP p (suc n)  
... | no p with dichotomyBool (a 0)
... | inj₁ q = ⊥-rec (p q)
... | inj₂ q =
  path?-η a aP q (suc n)
  ∙ cong η (path?≡ (a ∘ suc) (λ { (x , eqx) (y , eqy) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (suc x , eqx) (suc y , eqy)))) }) n)  
-}


{-
module FromInjectivity2 (τ-1inj : ∀ s t → τ-1 s ≡ τ-1 t → s ≡ t) where

  equal-proj : ∀ s t 
    → (∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) t)
    → ∀ (n : ℕ) → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst 0 .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst 0 .fst n) t
  equal-proj s t p n =
    sym (mapPfinComp s)
    ∙ cong (mapPfin (λ x → x .fst n)) (p 0)
    ∙ mapPfinComp {g = λ x → x .fst n}{λ x → x .fst 0} t

  complete' : ∀ s t 
    → (∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) t)
    → τ-1 s ≡ τ-1 t
  complete' s t p = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
    (funExt (λ { zero → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
                 (funExt (λ { zero → refl ;
                              (suc n) →
                                mapPfinComp  (mapPfin (proj iPfin2-ch 0) s)
                                ∙ mapPfinComp s
                                ∙ cong (λ f → mapPfin f s) (funExt (λ z → z .fst 0 .snd n))
                                ∙ equal-proj s t p n
                                ∙ cong (λ f → mapPfin f t) (funExt (λ z → sym (z .fst 0 .snd n)))
                                ∙ sym (mapPfinComp t)
                                ∙ sym (mapPfinComp  (mapPfin (proj iPfin2-ch 0) t))})) ;
                 (suc n) → antisym⊆
                   (λ x mx → ∥rec∥ (snd ((x ∈ₛ mapPfin (iMapPfin2 n) (mapPfin (proj iPfin2-ch (suc n)) t))))
                     (λ { (y , my , eq) → subst (λ z → ⟨ x ∈ₛ z ⟩)
                                                 (sym (mapPfinComp t
                                                   ∙ cong (λ f → mapPfin f t) (funExt (λ z → z .snd n))
                                                   ∙ sym (p n)
                                                   ∙ cong (λ f → mapPfin f s) (sym (funExt (λ z → z .snd n)))
                                                   ∙ sym (mapPfinComp s)))
                                                 (subst (λ z → ⟨ z ∈ₛ mapPfin (iMapPfin2 n) (mapPfin (proj iPfin2-ch (suc n)) s) ⟩)
                                                        eq
                                                        (∈ₛmapPfin (iMapPfin2 n) y (mapPfin (proj iPfin2-ch (suc n)) s) my)) })
                     (pre∈ₛmapPfin (iMapPfin2 n) x (mapPfin (proj iPfin2-ch (suc n)) s) mx))
                   (λ x mx → ∥rec∥ (snd ((x ∈ₛ mapPfin (iMapPfin2 n) (mapPfin (proj iPfin2-ch (suc n)) s))))
                     (λ { (y , my , eq) → subst (λ z → ⟨ x ∈ₛ z ⟩)
                                                 (sym (mapPfinComp s
                                                   ∙ cong (λ f → mapPfin f s) (funExt (λ z → z .snd n))
                                                   ∙ p n 
                                                   ∙ cong (λ f → mapPfin f t) (sym (funExt (λ z → z .snd n)))
                                                   ∙ sym (mapPfinComp t)))
                                                 (subst (λ z → ⟨ z ∈ₛ mapPfin (iMapPfin2 n) (mapPfin (proj iPfin2-ch (suc n)) t) ⟩)
                                                        eq
                                                        (∈ₛmapPfin (iMapPfin2 n) y (mapPfin (proj iPfin2-ch (suc n)) t) my)) })
                     (pre∈ₛmapPfin (iMapPfin2 n) x (mapPfin (proj iPfin2-ch (suc n)) t) mx))}))

  complete : (x y1 y2 : ωPfin2) (z : ℕ → ωPfin2)
    → (∀ n → (z n ≡ y1) ⊎ (z n ≡ y2))
    → (∀ n → z n .fst n ≡ x .fst n)
    → ⟨ x ∈ₛ (η y1 ∪ η y2) ⟩
  complete x y1 y2 z p q = subst (λ z → ⟨ x ∈ₛ z ⟩) (τ-1inj s t (complete' s t eq)) (inl ∣ refl ∣)
    where
      t : Pfin ωPfin2
      t = η y1 ∪ η y2

      s : Pfin ωPfin2
      s = η x ∪ t

      sub : ∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) s
                     ⊆ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) t
      sub n a = ∥rec∥ propTruncIsProp
        (λ { (inj₁ r) →
                   ∥map∥ (λ eq → map⊎ (λ eq' → ∣ eq ∙ sym (q n) ∙ cong (λ w → w .fst n) eq' ∣)
                                      (λ eq' → ∣ eq ∙ sym (q n) ∙ cong (λ w → w .fst n) eq' ∣)
                                      (p n))
                         r ;
             (inj₂ r) → r })

      eq : ∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) t
      eq n = antisym⊆ (sub n) (λ a → inr)

--   complete-test : (x y1 y2 : ωPfin2) (z : ℕ → ωPfin2)
--     → (∀ n → (z n ≡ y1) ⊎ (z n ≡ y2))
--     → (∀ n → z n .fst 0 .fst n ≡ x .fst 0 .fst n)
--     → ⟨ x ∈ₛ (η y1 ∪ η y2) ⟩
--   complete-test x y1 y2 z p q = subst (λ z → ⟨ x ∈ₛ z ⟩) (τ-1inj s t (complete' s t eq2 eq)) (inl ∣ refl ∣)
--     where
--       t : Pfin ωPfin2
--       t = η y1 ∪ η y2
-- 
--       s : Pfin ωPfin2
--       s = η x ∪ t
-- 
--       sub : ∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) s
--                      ⊆ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) t
--       sub n a = ∥rec∥ propTruncIsProp
--         (λ { (inj₁ r) →
--                    ∥map∥ (λ eq → map⊎ (λ eq' → {!!})
--                                       (λ eq' → {!!})
--                                       (p n))
--                          r ;
--              (inj₂ r) → r })
-- 
--       eq : ∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) s
--                      ≡ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst n) t
--       eq n = antisym⊆ (sub n) (λ a → inr)
-- 
--       sub2 : (n : ℕ) → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst 0 .fst n) s
--                      ⊆ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst 0 .fst n) t
--       sub2 n a = ∥rec∥ propTruncIsProp
--         (λ { (inj₁ r) →
--                    ∥map∥ (λ eq → map⊎ (λ eq' → ∣ eq ∙ sym (q n) ∙ {!eq'!} ∣)
--                                       (λ eq' → {!q n!})
--                                       (p 0))
--                          r ;
--              (inj₂ r) → r })
-- 
--       eq2 : ∀ n → mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst 0 .fst n) s
--                      ≡ mapPfin (λ (x : ωLimit iPfin2-ch) → x .fst 0 .fst n) t
--       eq2 n = antisym⊆ (sub2 n) (λ a → inr)

  llpo : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
    → (∀ n → isEven n → a n ≡ false) ⊎ (∀ n → isOdd n → a n ≡ false) 
  llpo a aP = {!!}
    where
      y1 : ωPfin2
      y1 = path2-ch
      
      y2 : ωPfin2
      y2 = path2?-ch a



{-    
      y11 : ∀ n → iPfin n
      y11 zero = tt
      y11 (suc n) = η (y11 n)

      y11-res : ∀ n → iMapPfin n (y11 (suc n)) ≡ y11 n
      y11-res zero = refl
      y11-res (suc n) = cong η (y11-res n)

      y11-ch : ωPfin
      y11-ch = y11 , y11-res

      y1 : ∀ n → iPfin2 n
      y1 zero = y11-ch
      y1 (suc n) = η (y1 n)

      y1-res : ∀ n → iMapPfin2 n (y1 (suc n)) ≡ y1 n
      y1-res zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _)) (funExt y11-res)
      y1-res (suc n) = cong η (y1-res n)

      y1-ch : ωPfin2
      y1-ch = y1 , y1-res

      y21 : ∀ n → iPfin n
      y21 n with true-before? a n
      ... | yes (k , k≤n , eq) = iPfinEmb k n k≤n (y11 k)
      ... | no _ = y11 n

      y21-res : ∀ n → iMapPfin n (y21 (suc n)) ≡ y21 n
      y21-res n with true-before? a (suc n)
      ... | yes (k , lek , eqk) with true-before? a n
      ... | yes (l , lel , eql) =
        cong (iMapPfin n) (iPfinEmb≡ (cong fst (aP (k , eqk) (l , eql))) lek (≤-suc lel) y11)
        ∙ iPfinEmb-res l n lel (y11 l)
      ... | no ¬p =
        cong (iMapPfin n)
          (iPfinEmb≡ {!!} lek ≤-refl y11
          ∙ cong η
            (cong (λ p → iPfinEmb n n p (y11 n)) {!!}
            ∙ iPfinEmbRefl n (y11 n)))
        ∙ y11-res n
      y21-res n | no ¬p with true-before? a n
      ... | yes (k , k≤n , eq) = ⊥-rec (¬p (k , ≤-suc k≤n , eq))
      ... | no _ = y11-res n

      y21-ch : ωPfin
      y21-ch = y21 , y21-res


      y21-ø : a 0 ≡ true → ∀ n → y21 n ≡ void n
      y21-ø eq0 n with true-before? a n
      y21-ø eq0 zero | yes (k , le , eqk) =
        iPfinEmb≡ (cong fst (aP (k , eqk) (0 , eq0))) le zero-≤ y11
      y21-ø eq0 (suc n) | yes (k , le , eqk) = 
        iPfinEmb≡ (cong fst (aP (k , eqk) (0 , eq0))) le zero-≤ y11
      ... | no p = ⊥-rec (p (0 , zero-≤ , eq0))

      y21-η : a 0 ≡ false → ∀ n → y21 n ≡ {!!}

{-
      y21-ø : y21 1 ≡ ø → ∀ n → y21 n ≡ void n
      y21-ø eq n with true-before? a n
      y21-ø eq zero | yes (zero , lek , eqk) = refl
      y21-ø eq (suc n) | yes (zero , lek , eqk) = refl
      y21-ø eq zero | yes (suc k , lek , eqk) = ⊥-rec (¬-<-zero lek)
      y21-ø eq (suc n) | yes (suc k , lek , eqk) = {!!}
      ... | no p = {!!}
-}

      y2 : ∀ n → iPfin2 n
      y2 zero = y21-ch
      y2 (suc n) = {!y21 1!}

      y2-ch : ωPfin2
      y2-ch = {!!} , {!!}
-}
-}
