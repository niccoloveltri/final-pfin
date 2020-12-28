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

dec∈ₛ : {A : Type}
  → ((x y : A) → Dec ∥ x ≡ y ∥)
  → (x : A) (s : Pfin A) → Dec ⟨ x ∈ₛ s ⟩
dec∈ₛ decEq x = elimPfinProp
  (λ s → _ , decIsProp (snd (x ∈ₛ s)))
  (no λ x → x)
  (decEq x)
  λ {s1}{s2} → lem {s1}{s2}
  where
    lem : ∀{s1 s2} → Dec ⟨ x ∈ₛ s1 ⟩ → Dec ⟨ x ∈ₛ s2 ⟩
      → Dec ⟨ x ∈ₛ (s1 ∪ s2) ⟩
    lem (yes p) d2 = yes (inl p)
    lem (no ¬p) (yes p) = yes (inr p)
    lem (no ¬p) (no ¬q) = no (∥rec∥ isProp⊥
      (λ { (inj₁ x) → ¬p x ; (inj₂ x) → ¬q x }))

dec⊆ : {A : Type}
  → ((x y : A) → Dec ∥ x ≡ y ∥)
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
PfinDecEq decEq x y = {!!}

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

≤-suc-cases : ∀ k n → k ≤N suc n
  → (k ≤N n) ⊎ (k ≡ suc n)
≤-suc-cases zero n le = inj₁ zero-≤
≤-suc-cases (suc k) zero le = inj₂ (cong suc (≤0→≡0 (pred-≤-pred le)))
≤-suc-cases (suc k) (suc n) le with ≤-suc-cases k n (pred-≤-pred le)
... | inj₁ p = inj₁ (suc-≤-suc p)
... | inj₂ p = inj₂ (cong suc p)



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





misInjective : ∀ s t → m s ≡ m t → s ≡ t
misInjective _ _ eq =
  lem-injective-lim iPfin-ch _ _
    {!!}
    _ _ eq



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

iMapPfin2isInjective : ∀ n (x y : iPfin2 (suc n))
  → iMapPfin2 n x ≡ iMapPfin2 n y → x ≡ y
iMapPfin2isInjective zero x y eq = misInjective x y eq
iMapPfin2isInjective (suc n) x y eq =
  mapPfinInj (iMapPfin2 n) (iMapPfin2isInjective n) x y eq

u : ∀ n → iPfin2 n → ωPfin
u zero x = x
u (suc n) x = u n (iMapPfin2 n x)

uisInjective : ∀ n (x y : iPfin2 n)
  → u n x ≡ u n y → x ≡ y
uisInjective zero x y eq = eq
uisInjective (suc n) x y eq =
  iMapPfin2isInjective n _ _ (uisInjective n _ _ eq)

uLem : ∀ (x : ωPfin2) n
  → u n (iMapPfin2 n (x .fst (suc n))) ≡ m (x .fst 1)
uLem x zero = refl
uLem x (suc n) = cong (λ z → u n (iMapPfin2 n z)) (x .snd (suc n)) ∙ uLem x n

uLem2 : ∀ (x : ×pℕ u) n
  → u (suc n) (x .fst (suc n)) ≡ u n (x .fst n)
uLem2 x zero = x .snd 0
uLem2 (x , p) (suc n) = uLem2 ((λ n → iMapPfin2 n (x (suc n))) , λ n → p (suc n) ∙ sym (p 0)) n

-- uLem2-sh : ∀ (x : ×pℕ {!!}) n
--   → u (suc n) (x .fst (suc n)) ≡ u n (x .fst n)

-- subtypeEquiv : {A : Type} {P Q : A → Type}
--   → (∀ a → isProp (P a)) → (∀ a → isProp (Q a))
--   → (∀ {a} → P a → Q a) → (∀ {a} → Q a → P a)
--   → Σ A P ≃ Σ A Q
-- subtypeEquiv pP pQ P2Q Q2P = Σ-cong-equiv-snd {!!}
--   (λ x → x .fst , P2Q (x .snd)) ,
--   record { equiv-proof = λ y → ((y .fst , Q2P (y .snd)) ,
--                                  Σ≡Prop pQ refl) ,
--                                 λ z → Σ≡Prop {!!} {!!} }  

ωPfin2-iso-×pℕ : Iso (ωPfin2) (×pℕ u)
ωPfin2-iso-×pℕ = Σ-cong-iso-snd
  λ x → iso (λ p n → uLem (x , p) n ∙ p 0)
             (λ q n → uisInjective n _ _ (uLem2 (x , q) n))
             (λ _ → isPropΠ (λ _ → isSetωPfin _ _) _ _)
             λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _) _ _

ωPfin2≃×pℕ : ωPfin2 ≃ ×pℕ u
ωPfin2≃×pℕ = isoToEquiv ωPfin2-iso-×pℕ

Pfin-iso : {A B : Type} → Iso A B → Iso (Pfin A) (Pfin B)
Pfin-iso AisoB =
  iso (mapPfin (Iso.fun AisoB))
      (mapPfin (Iso.inv AisoB))
      (λ x → mapPfinComp x ∙ (λ i → mapPfin (λ y → Iso.rightInv AisoB y i) x) ∙ mapPfinId x)
      λ x → mapPfinComp x ∙ (λ i → mapPfin (λ y → Iso.leftInv AisoB y i) x) ∙ mapPfinId x

Pfin≃ : {A B : Type} → A ≃ B → Pfin A ≃ Pfin B
Pfin≃ eq = isoToEquiv (Pfin-iso (equivToIso eq))

-- the limit of the shifted (ω+ω)-chain
ωPfin2Sh : Type
ωPfin2Sh = ωLimit (shift iPfin2-ch)


×pℕSh-iso-ωPfin2Sh : Iso (×pℕ (mapPfin ∘ u)) ωPfin2Sh
×pℕSh-iso-ωPfin2Sh = Σ-cong-iso-snd
  λ x → iso (λ p n → mapPfinInj (u n) (uisInjective n) _ _ (mapPfinComp (x (suc n)) ∙ lem x p n))
             (λ p n → lem2 x (λ n → sym (mapPfinComp (x (suc n))) ∙ cong (mapPfin (u n)) (p n)) n)
             (λ _ → isPropΠ (λ _ → trunc _ _) _ _)
             λ _ → isPropΠ (λ _ → trunc _ _) _ _
  where
    lem : (x : ∀ n → Pfin (iPfin2 n))
      → (∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u 0) (x 0))
      → ∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u n) (x n)
    lem x p zero = p 0
    lem x p (suc n) = p (suc n) ∙ sym (p n) 

    lem2 : (x : ∀ n → Pfin (iPfin2 n))
      → (∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u n) (x n))
      → ∀ n → mapPfin (u (suc n)) (x (suc n)) ≡ mapPfin (u 0) (x 0)
    lem2 x p zero = p 0
    lem2 x p (suc n) = p (suc n) ∙ lem2 x p n


-- ×pℕshift-iso : Iso (×pℕ (mapPfin ∘ u)) (×pℕ u)
-- ×pℕshift-iso =
--   iso (λ x → {!x .fst !} , {!!})
--       (λ x → x .fst ∘ suc , λ n → {!x .snd (suc n)!})
--       {!!}
--       {!!}



×pℕSh≃ωPfin2Sh : ×pℕ (mapPfin ∘ u) ≃ ωPfin2Sh
×pℕSh≃ωPfin2Sh = isoToEquiv ×pℕSh-iso-ωPfin2Sh

ωPfin22Sh≃ωPfin2 : ωPfin2Sh ≃ ωPfin2
ωPfin22Sh≃ωPfin2 = invEquiv (shift≃ iPfin2-ch isSetiPfin2)

τ-equiv : Pfin ωPfin2 ≃ ωPfin2
τ-equiv =
  compEquiv (Pfin≃ ωPfin2≃×pℕ)
    (compEquiv (Pfin×pℕ {!!} (λ _ → trunc) isSetωPfin u (λ n → uisInjective (suc n)))
      (compEquiv ×pℕSh≃ωPfin2Sh ωPfin22Sh≃ωPfin2))

ConePfinωPfin2 : Cone iPfin2-ch (Pfin ωPfin2)
ConePfinωPfin2 =
  (λ n x → iMapPfin2 n (mapPfin (proj iPfin2-ch n) x)) ,
  λ n x → cong (iMapPfin2 n)
    (mapPfinComp x ∙ cong (λ f → mapPfin f x)
      (funExt (λ y → y .snd n)))

τ-1 : Pfin ωPfin2 → ωPfin2
τ-1 = Iso.inv (AdjLim iPfin2-ch _) ConePfinωPfin2

τ : ωPfin2 → Pfin ωPfin2
τ = invEq τ-equiv

τ-1≡ : τ-1 ≡ equivFun τ-equiv
τ-1≡ = funExt (λ x → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
  (funExt (λ n → cong (iMapPfin2 n) (sym (mapPfinComp x)))))

module Finality (A : Type) (α : A → Pfin A)
                (αsim : A → ωPfin2) 
                (αsim-mor : ∀ a → τ (αsim a) ≡ mapPfin αsim (α a)) where

  pα : ∀ n (a : A) → iPfin n
  pα zero a = tt
  pα (suc n) a = mapPfin (pα n) (α a)

  pα-res : ∀ n (a : A) → iMapPfin n (mapPfin (pα n) (α a)) ≡ pα n a
  pα-res zero a = refl
  pα-res (suc n) a = mapPfinComp (α a) ∙ cong (λ f → mapPfin f (α a)) (funExt (pα-res n))

  pα2 : ∀ n (a : A) → iPfin2 n
  pα2 zero a = (λ n → pα n a) , λ n → pα-res n a 
  pα2 (suc n) a = mapPfin (pα2 n) (α a)

  pα2-res : ∀ n (a : A) → iMapPfin2 n (mapPfin (pα2 n) (α a)) ≡ pα2 n a
  pα2-res zero a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin  _ _ _))
    (funExt (λ n → cong (iMapPfin n) (mapPfinComp (α a)) ∙ pα-res n a))
  pα2-res (suc n) a = mapPfinComp (α a) ∙ cong (λ f → mapPfin f (α a)) (funExt (pα2-res n))

  coneA : Cone iPfin2-ch A
  coneA = pα2 , pα2-res

  αbar : A → ωPfin2
  αbar = Iso.inv (AdjLim iPfin2-ch _) coneA

  αbar-mor' : ∀ a → αbar a ≡ τ-1 (mapPfin αbar (α a))
  αbar-mor' a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
    (funExt (λ n → sym (cong (iMapPfin2 n) (mapPfinComp (α a)) ∙ pα2-res n a)))

  αbar-mor : ∀ a → τ (αbar a) ≡ mapPfin αbar (α a)
  αbar-mor a =
      τ (αbar a)
    ≡⟨ (λ i → τ (αbar-mor' a i)) ⟩
      τ (τ-1 (mapPfin αbar (α a)))
    ≡⟨ (λ i → τ (τ-1≡ i (mapPfin αbar (α a)))) ⟩
      τ (equivFun τ-equiv (mapPfin αbar (α a)))
    ≡⟨ (λ i → Iso.leftInv (equivToIso τ-equiv) (mapPfin αbar (α a)) i) ⟩
      mapPfin αbar (α a)
    ∎

  αsim-mor' : ∀ a → αsim a ≡ τ-1 (mapPfin αsim (α a))
  αsim-mor' a =
      αsim a
    ≡⟨ sym (Iso.rightInv (equivToIso τ-equiv) (αsim a)) ⟩
      equivFun τ-equiv (τ (αsim a))
    ≡⟨ (λ i → equivFun τ-equiv (αsim-mor a i) ) ⟩
      equivFun τ-equiv (mapPfin αsim (α a))
    ≡⟨ (λ i → τ-1≡ (~ i) (mapPfin αsim (α a))) ⟩
      τ-1 (mapPfin αsim (α a))
    ∎

  αbar-eq : ∀ a n → αsim a .fst 0 .fst n ≡ pα n a
  αbar-eq a zero = refl
  αbar-eq a (suc n) = 
    funExt⁻ (cong fst (funExt⁻ (cong fst (αsim-mor' a)) 0)) (suc n)
    ∙ mapPfinComp ((mapPfin (proj iPfin2-ch 0) (mapPfin αsim (α a))))
    ∙ mapPfinComp (mapPfin αsim (α a))
    ∙ mapPfinComp (α a)
    ∙ cong (λ f → mapPfin f (α a)) (funExt (λ x → αsim x .fst 0 .snd n ∙ αbar-eq x n))

  αbar-eq2 : ∀ a n → αsim a .fst n ≡ pα2 n a
  αbar-eq2 a zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
    (funExt (αbar-eq a))
  αbar-eq2 a (suc n) =
    funExt⁻ (cong fst (αsim-mor' a)) (suc n)
    ∙ mapPfinComp (mapPfin αsim (α a))
    ∙ mapPfinComp (α a)
    ∙ cong (λ f → mapPfin f (α a)) (funExt (λ x → αsim x .snd n ∙ αbar-eq2 x n))

  αbar-uniq : ∀ a → αsim a ≡ αbar a
  αbar-uniq a = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin2 _ _ _))
    (funExt (αbar-eq2 a))

