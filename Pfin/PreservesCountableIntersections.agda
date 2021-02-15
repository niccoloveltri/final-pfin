{-# OPTIONS --cubical --no-import-sorts #-}

module Pfin.PreservesCountableIntersections where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Everything
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming ([_] to eqCl; rec to recQ; rec2 to recQ2)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat renaming (elim to elimNat)
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Basics
open import ListStuff
open import Cubical.Relation.Nullary

open import Pfin.AsFreeJoinSemilattice 

-- -- Pfin preserves intersections

-- (countable) wide pullpacks
×pℕ : {A : ℕ → Type} {C : Type}
  → (f : ∀ n → A n → C) → Type
×pℕ {A} f = Σ[ a ∈ ((n : ℕ) → A n) ] ∀ n → f (suc n) (a (suc n)) ≡ f 0 (a 0)

-- the wide pullback is a set if the components of the wedge are sets
isSet×pℕ : {A : ℕ → Type} {C : Type}
  → (∀ n → isSet (A n)) → isSet C
  → (f : ∀ n → A n → C) → isSet (×pℕ f)
isSet×pℕ sA sC f = isSetΣ (isSetΠ sA) λ _ → isProp→isSet (isPropΠ (λ _ → sC _ _))

-- equality in the wide pullback
Eq×pℕ : {A : ℕ → Type} {C : Type} → isSet C
  → (f : ∀ n → A n → C)
  → {a a' : ∀ n → A n} → (∀ n → a n ≡ a' n)
  → {eq : ∀ n → f (suc n) (a (suc n)) ≡ f 0 (a 0)}
  → {eq' : ∀ n → f (suc n) (a' (suc n)) ≡ f 0 (a' 0)}
  → _≡_ {A = ×pℕ f} (a , eq) (a' , eq')
Eq×pℕ setC f p =
  Σ≡Prop (λ a → isPropΠ (λ _ → setC _ _))
    λ i n → p n i

-- the construction of a function from the type of finite subsets of a
-- wide pullback to the wide pullback of finite subsets
to×pℕ : {A : ℕ → Type}{C : Type} (f : ∀ n → A n → C) 
  → Pfin (×pℕ {A}{C} f) → ×pℕ {Pfin ∘ A}{Pfin C} (mapPfin ∘ f)
to×pℕ f s =
  (λ n → mapPfin (λ x → x .fst n) s) ,
  λ n →
     mapPfinComp s
     ∙ cong (λ z → mapPfin z s) (λ i x → x .snd n i)
     ∙ sym (mapPfinComp s)

-- some auxiliary constructions
funs : {A : ℕ → Type} {C : Type}
  → (f0 : A 0 → C)
  → (f : ∀ n → A (suc n) → C)
  → ∀ n → A n → C
funs f0 f zero = f0
funs f0 f (suc n) = f n

funsEq : {A : ℕ → Type} {C : Type}
  → (f : ∀ n → A n → C)
  → ∀ n → funs {A} (f 0) (f ∘ suc) n ≡ f n
funsEq f zero = refl
funsEq f (suc n) = refl

args : {A : ℕ → Type} 
  → (a0 : Pfin (A 0))
  → (as : ∀ n → Pfin (A (suc n)))
  → ∀ n → Pfin (A n)
args a0 as zero = a0
args a0 as (suc n) = as n

argsEq : {A : ℕ → Type} 
  → (a : ∀ n → Pfin (A n))
  → ∀ n → args {A} (a 0) (a ∘ suc) n ≡ a n
argsEq a zero = refl
argsEq a (suc n) = refl

args∪ : {A : ℕ → Type} 
  → {a0 b0 : Pfin (A 0)}
  → {as bs : ∀ n → Pfin (A (suc n))}
  → ∀ n → args {A} (a0 ∪ b0) (λ k → as k ∪ bs k) n
         ≡ (args {A} a0 as n ∪ args {A} b0 bs n)
args∪ zero = refl
args∪ (suc n) = refl

-- to prove that a family (a : ∀ n → A n) in the wide pullback (×pℕ f)
-- is in a certain subset s, in case all functions in (f ∘ suc) are
-- injective, then it sufficient to show that a 0 is among the
-- 0-projections in s
∈Pfin×pℕ : {A : ℕ → Type} {C : Type} → isSet C 
  → (f : ∀ n → A n → C)
  → (∀ n (x y : A (suc n)) → f (suc n) x ≡ f (suc n) y → x ≡ y)
  → {a : ∀ n → A n} (eq : ∀ n → f (suc n) (a (suc n)) ≡ f 0 (a 0))
  → (s : Pfin (×pℕ f))
  → ⟨ a 0 ∈ₛ mapPfin (λ x → x .fst 0) s ⟩
  → ⟨ (a , eq) ∈ₛ s ⟩
∈Pfin×pℕ setC f injf {a} eq s ma0 =
  ∥rec∥ (snd ((a , eq) ∈ₛ s))
    (λ { ((a' , eq') , m , r) →
      J {x = a'} (λ y _ → (eq : ∀ n → f (suc n) (y (suc n)) ≡ f 0 (y 0)) → ⟨ (y , eq) ∈ₛ s ⟩)
        (λ eq → subst (λ z → ⟨ (a' , z) ∈ₛ s ⟩) (funExt (λ n → setC _ _ _ _)) m)
        (λ { i zero → r i ; i (suc n) → injf n _ _ ((eq' n ∙ cong (f 0) r ∙ sym (eq n))) i })
        eq})
    (pre∈ₛmapPfin (λ x → x .fst 0) _ s ma0)

-- We show that Pfin preserves a wide pullback ×pℕ in case the family
-- f is made of injective functions, which is to say that Pfin
-- preserves intersections. The construction of an inverse function of
-- to×pℕ requires the assumption of countable choice. We actually prove
-- in one go that to×pℕ is an equivalence.
module _ (cc : (P : ℕ → Type) → (∀ n → ∥ P n ∥) → ∥ (∀ n → P n) ∥) where

  to×pℕEquiv : {A : ℕ → Type} {C : Type}
    → (setA : ∀ n → isSet (A (suc n))) (setC : isSet C)
    → (f0 : A 0 → C)
    → (f : ∀ n → A (suc n) → C)
    → (∀ n (x y : A (suc n)) → f n x ≡ f n y → x ≡ y)
    → (a0 : Pfin (A 0))
    → (as : ∀ n → Pfin (A (suc n)))
    → (eq : ∀ n → mapPfin (f n) (as n) ≡ mapPfin f0 a0)
    → isContr (fiber (to×pℕ (funs {A} f0 f)) (args a0 as , eq))
  to×pℕEquiv {A}{C} setA setC f0 f injf =
    elimPfinProp (λ _ → _ , isPropΠ (λ _ → isPropΠ (λ _ → isPropIsContr)))
      (λ as eq →
        (ø ,
         Eq×pℕ trunc (λ n → mapPfin (funs {A} f0 f n)) (λ { zero → refl ; (suc n) → sym (mapPfinø (f n) (as n) (eq n)) })) ,
         λ { (w , eqw) →
           EqFiber (isSetΣ (isSetΠ (λ _ → trunc)) λ _ → isSetΠ (λ _ → isProp→isSet (trunc _ _))) _ _
                   (antisym⊆ (λ { _ () })
                     λ x m → subst (λ z → ⟨ x .fst 0 ∈ₛ z ⟩) (funExt⁻ (cong fst eqw) 0) (∈ₛmapPfin (λ z → z .fst 0) x w m))
                   _ _ })
      (λ a as eq →
        let a' : ∀ n → Σ[ x ∈ A (suc n) ] as n ≡ η x
            a' n = mapPfinη (setA n) (f n) (injf n) (as n) (f0 a) (eq n)
        in (η ((λ { zero → a ; (suc n) → a' n .fst }) ,
               λ n → ηisInjective setC (cong (mapPfin (f n)) (sym (a' n .snd)) ∙ eq n)) ,
           Eq×pℕ trunc (λ n → mapPfin (funs {A} f0 f n)) (λ { zero → refl ; (suc n) → sym (a' n .snd) })) ,
           λ { (w , eqw) →
             EqFiber (isSetΣ (isSetΠ (λ _ → trunc)) λ _ → isSetΠ (λ _ → isProp→isSet (trunc _ _))) _ _
               (antisym⊆
                 (λ { x@(a' , fa'≡gb') → ∥rec∥ (snd (x ∈ₛ w))
                   λ eqx → ∈Pfin×pℕ setC (funs {A} f0 f) injf fa'≡gb' w
                     (subst (λ z → ⟨ a' 0 ∈ₛ z 0 ⟩) (cong fst (sym eqw)) ∣ funExt⁻ (cong fst eqx) 0 ∣) })
                 λ { x@(a' , fa'≡gb') mx → ∈Pfin×pℕ setC (funs {A} f0 f) injf fa'≡gb' (η (_ , _))
                     (subst (λ z → ⟨ a' 0 ∈ₛ z ⟩) (funExt⁻ (cong fst eqw) 0) (∈ₛmapPfin (λ z → z .fst 0) _ w mx)) })
               _ _ })
      λ {s1} {s2} ih1 ih2 as eq → 
        let p : ∥ (∀ n → Σ[ a1 ∈ Pfin (A (suc n)) ] Σ[ a2 ∈ Pfin (A (suc n)) ]
                  (a1 ∪ a2 ≡ as n) × (mapPfin f0 s1 ≡ mapPfin (f n) a1) × (mapPfin f0 s2 ≡ mapPfin (f n) a2)) ∥
            p = cc _ (λ n → ∪≡mapPfin (f n) (injf n) (as n) (mapPfin f0 s1) (mapPfin f0 s2) (sym (eq n)))
        in ∥rec∥ isPropIsContr
          (λ { p →
            let u1 : ∀ n → Pfin (A (suc n))
                u1 n = p n .fst
                u2 : ∀ n → Pfin (A (suc n))
                u2 n = p n .snd .fst
                eqt : ∀ n → u1 n ∪ u2 n ≡ as n
                eqt n = p n .snd .snd .fst
                eq1 : ∀ n → mapPfin (f n) (u1 n) ≡ mapPfin f0 s1
                eq1 n = sym (p n .snd .snd .snd .fst)
                eq2 : ∀ n → mapPfin (f n) (u2 n) ≡ mapPfin f0 s2
                eq2 n = sym (p n .snd .snd .snd .snd)
                ((v1 , q1) , r1) = ih1 u1 eq1
                ((v2 , q2) , r2) = ih2 u2 eq2
            in ((v1 ∪ v2) ,
                Eq×pℕ trunc (λ n → mapPfin (funs {A} f0 f n))
                  (λ n → cong₂ _∪_ (funExt⁻ (cong fst q1) n) (funExt⁻ (cong fst q2) n)
                          ∙ sym (args∪ n)
                          ∙ cong (λ k → args {A} (s1 ∪ s2) k n)
                                 (funExt (λ n → mapPfinInj (f n) (injf n) _ _ (cong₂ _∪_ (eq1 n) (eq2 n) ∙ sym (eq n)))))) ,
                λ { (w , eqw) →
                  EqFiber (isSetΣ (isSetΠ (λ _ → trunc)) λ _ → isSetΠ (λ _ → isProp→isSet (trunc _ _))) _ _
                    (cong₂ _∪_ (cong fst (r1 (v1 , q1))) (cong fst (r2 (v2 , q2)))
                     ∙ antisym⊆
                         (λ x@(a , fa≡gb) → ∥rec∥ (snd (x ∈ₛ w))
                           (λ { (inj₁ mx) → ∈Pfin×pℕ setC (funs {A} f0 f) injf fa≡gb w
                                  (subst (λ z → ⟨ a 0 ∈ₛ z ⟩)
                                         (funExt⁻ (cong fst (sym eqw)) 0)
                                           (inl (subst (λ z → ⟨ a 0 ∈ₛ z ⟩)
                                                       (funExt⁻ (cong fst q1) 0)
                                                       (∈ₛmapPfin (λ y → y .fst 0) x v1 mx))))
                              ; (inj₂ mx) → ∈Pfin×pℕ setC (funs {A} f0 f) injf fa≡gb w
                                  (subst (λ z → ⟨ a 0 ∈ₛ z ⟩)
                                         (funExt⁻ (cong fst (sym eqw)) 0)
                                           (inr (subst (λ z → ⟨ a 0 ∈ₛ z ⟩)
                                                       (funExt⁻ (cong fst q2) 0)
                                                       (∈ₛmapPfin (λ y → y .fst 0) x v2 mx)))) }))
                         λ { x@(a , fa≡gb) mx → ∥rec∥ propTruncIsProp
                               (λ { (inj₁ ma) → inl (∈Pfin×pℕ setC (funs {A} f0 f) injf fa≡gb v1
                                      (subst (λ z → ⟨ a 0 ∈ₛ z ⟩) (funExt⁻ (cong fst (sym q1)) 0) ma))
                                  ; (inj₂ ma) → inr (∈Pfin×pℕ setC (funs {A} f0 f) injf fa≡gb v2
                                      (subst (λ z → ⟨ a 0 ∈ₛ z ⟩) (funExt⁻ (cong fst (sym q2)) 0) ma)) })
                               (subst (λ z → ⟨ a 0 ∈ₛ z ⟩) (funExt⁻ (cong fst eqw) 0) (∈ₛmapPfin (λ y → y .fst 0) x w mx)) })
                    _ _ } })
          p
  
  
  Pfin×pℕ : {A : ℕ → Type} {C : Type}
    → (setA : ∀ n → isSet (A (suc n))) (setC : isSet C)
    → (f : ∀ n → A n → C)
    → (injf : ∀ n (x y : A (suc n)) → f (suc n) x ≡ f (suc n) y → x ≡ y)
    → Pfin (×pℕ f) ≃ ×pℕ (mapPfin ∘ f)
  Pfin×pℕ {A} setA setC f injf = (to×pℕ f) ,
    (record { equiv-proof =
      subst (λ f → ∀ x → isContr (fiber (to×pℕ f) x))
            (funExt (funsEq {A} f))
            (λ x@(a , eq) → subst (isContr ∘ fiber (to×pℕ (funs {A} (f 0) (f ∘ suc))))
                                  (λ i → (λ n → argsEq {A} a n i) , eq)
                                  (to×pℕEquiv setA setC (f 0) (f ∘ suc) injf (a 0) (a ∘ suc) eq))  })
  

