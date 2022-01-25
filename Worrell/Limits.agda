{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module Worrell.Limits where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as Pr
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
open import Basics
open import ListRelations
open import ListStuff
open import Pfin.AsSetQuot
open import Pfin.AsFreeJoinSemilattice
open import Pfin.PreservesCountableIntersections
open BinaryRelation

-- Stuff about ω-limits

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

-- the limit is a cone
proj : ∀{ℓ} (c@(A , r) : ωChain ℓ) n → ωLimit c → A n
proj (A , r) n (x , eq) = x n

ConeωLimit : ∀{ℓ} (c : ωChain ℓ) → Cone c (ωLimit c)
ConeωLimit c@(A , r) = proj c , λ n x → x .snd n

-- isomorphism between cones with vertex C and functions from C to the
-- ω-limit
AdjLim : ∀{ℓ} (c : ωChain ℓ) (C : Type ℓ)
  → Iso (C → ωLimit c) (Cone c C)
AdjLim (A , r) C = iso
  (λ g → (λ n x → g x .fst n) , λ n x → g x .snd n)
  (λ h@(f , eq) x → (λ n → f n x) , (λ n → eq n x))
  (λ _ → refl)
  (λ g → funExt (λ _ → refl))

-- lemma for proving injectivity of functions into a ω-limit
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

-- shifted chain, which has the same (isomorphic) limit
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

-- restrictions between types in a ω-chain
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
Vω : Type
Vω = ωLimit iPfin-ch

-- Vω is a set
isSetVω : isSet Vω
isSetVω =
  isSetΣ (isSetΠ (λ _ → isSetiPfin _))
         (λ _ → isProp→isSet (isPropΠ (λ _ → isSetiPfin _ _ _)))

-- the limit of the shifted ω-chain
VωSh : Type
VωSh = ωLimit (shift iPfin-ch)

-- path equality in (iPfin n) is decidable
iPfinDecEq : ∀ n (x y : iPfin n) → Dec (x ≡ y)
iPfinDecEq zero x y = yes refl
iPfinDecEq (suc n) = PfinDecEq (iPfinDecEq n)

-- this limit is an algebra for Pfin, which is given by the universal
-- property of the limit (i.e. Pfin Vω is a cone)
ConePfinVω : Cone iPfin-ch (Pfin Vω)
ConePfinVω =
  (λ n x → iMapPfin n (mapPfin (proj iPfin-ch n) x)) ,
  λ n x → cong (iMapPfin n)
    (mapPfinComp x ∙ cong (λ f → mapPfin f x)
      (funExt (λ y → y .snd n)))

m : Pfin Vω → Vω
m = Iso.inv (AdjLim iPfin-ch _) ConePfinVω

-- a characterization of the equality (m s ≡ m t)
meq-lem : ∀ s t 
  → (∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                   ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t)
  → m s ≡ m t
meq-lem s t p = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
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

meq-lem2 : ∀ s t 
  → m s ≡ m t
  → ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                   ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
meq-lem2 s t eq n =
  cong (λ f → mapPfin f s) (funExt (λ x → sym (x .snd n)))
  ∙ sym (mapPfinComp s)
  ∙ funExt⁻ (cong fst eq) (suc n)
  ∙ mapPfinComp t
  ∙ cong (λ f → mapPfin f t) (funExt (λ x → x .snd n))


-- an alternative but equivalent construction of the limit Vω using
-- PfinQ (set quotient of lists) instead of Pfin.

iPfinQ : ℕ → Type 
iPfinQ zero = Unit
iPfinQ (suc n) = PfinQ (iPfinQ n)

isSetiPfinQ : ∀ n → isSet (iPfinQ n)
isSetiPfinQ zero = λ _ _ _ _ → refl
isSetiPfinQ (suc n) = squash/

iMapPfinQ : ∀ n → iPfinQ (suc n) → iPfinQ n
iMapPfinQ zero = λ _ → tt
iMapPfinQ (suc n) = mapPfinQ (iMapPfinQ n)

iPfinQ-ch : ωChain₀
iPfinQ-ch = iPfinQ , iMapPfinQ

VωQ : Type
VωQ = ωLimit iPfinQ-ch

-- path equality in (iPfinQ n) is decidable
iPfinQDecEq : ∀ n (x y : iPfinQ n) → Dec (x ≡ y)
iPfinQDecEq zero x y = yes refl
iPfinQDecEq (suc n) = PfinQDecEq (iPfinQDecEq n)

-- the PfinQ-algebra structure on VωQ, analogous to the function m
ConePfinQVωQ : Cone iPfinQ-ch (PfinQ VωQ)
ConePfinQVωQ =
  (λ n x → iMapPfinQ n (mapPfinQ (proj iPfinQ-ch n) x)) ,
  λ n x → cong (iMapPfinQ n)
    (mapPfinQComp x ∙ cong (λ f → mapPfinQ f x)
      (funExt (λ y → y .snd n)))

mQ : PfinQ VωQ → VωQ
mQ = Iso.inv (AdjLim iPfinQ-ch _) ConePfinQVωQ


-- the ω-chain of iterated applications of Pfin to Vω
iPfin2 : ℕ → Type 
iPfin2 zero = Vω
iPfin2 (suc n) = Pfin (iPfin2 n)

isSetiPfin2 : ∀ n → isSet (iPfin2 n)
isSetiPfin2 zero = isSetVω
isSetiPfin2 (suc n) = trunc

iMapPfin2 : ∀ n → iPfin2 (suc n) → iPfin2 n
iMapPfin2 zero = m
iMapPfin2 (suc n) = mapPfin (iMapPfin2 n)

iPfin2-ch : ωChain₀
iPfin2-ch = iPfin2 , iMapPfin2

-- the limit of the ω-chain iPfin2-ch
Vω2 : Type
Vω2 = ωLimit iPfin2-ch

-- algebra map on Vω2
ConePfinVω2 : Cone iPfin2-ch (Pfin Vω2)
ConePfinVω2 =
  (λ n x → iMapPfin2 n (mapPfin (proj iPfin2-ch n) x)) ,
  λ n x → cong (iMapPfin2 n)
    (mapPfinComp x ∙ cong (λ f → mapPfin f x)
      (funExt (λ y → y .snd n)))

τ-1 : Pfin Vω2 → Vω2
τ-1 = Iso.inv (AdjLim iPfin2-ch _) ConePfinVω2

-- the limit of the shifted (ω+ω)-chain
Vω2Sh : Type
Vω2Sh = ωLimit (shift iPfin2-ch)
