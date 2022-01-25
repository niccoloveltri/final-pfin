{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module Worrell.FromInjectivity where

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
open import Cubical.Data.Nat hiding (isEven ; isOdd) renaming (elim to elimNat)
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

open import Worrell.Limits

-- We prove that injectivity of (m : Pfin Vω → Vω) implies LLPO

-- The sequence corresponding to the infinite tree in which each node
-- has exactly one subtree.
long : ∀ n → iPfin n
long zero = tt
long (suc n) = η (long n)

long-res : ∀ n → iMapPfin n (long (suc n)) ≡ long n
long-res zero = refl
long-res (suc n) = cong η (long-res n)

long-ch : Vω
long-ch = long , long-res

-- Given a sequence a : ℕ → Bool, we a variant (long? a) of long,
-- which is equal to long if the sequence a contains only value false,
-- but its height stop growing if there is n : ℕ such that (a n) is
-- the first true in a.
long? : (a : ℕ → Bool) → ∀ n → iPfin n
long? a zero = tt
long? a (suc n) =
  if a 0 then ø else η (long? (a ∘ suc) n)

long?-res : (a : ℕ → Bool) 
  → ∀ n → iMapPfin n (long? a (suc n)) ≡ long? a n
long?-res a zero = refl
long?-res a (suc n) with a 0
... | false = cong η (long?-res (a ∘ suc) n)
... | true = refl

long?-ch : (a : ℕ → Bool) → Vω
long?-ch a = long? a , long?-res a

-- connections between long and (long? a)
long?-res' : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → a (suc n) ≡ true → iMapPfin n (long? a (suc n)) ≡ long n
long?-res' a aP zero eq = refl
long?-res' a aP (suc n) eq with dichotomyBool (a 0)
... | inj₁ p = ⊥-rec (znots (cong fst (aP (_ , p) (_ , eq))))
... | inj₂ p =
  cong (λ z → mapPfin (iMapPfin n) (if z then ø else η (if a 1 then ø else η (long? (λ x → a (suc (suc x))) n)))) p
  ∙ cong η (long?-res' (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n eq)

long?≠long : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → long? a (suc n) ≡ long (suc n) → a n ≡ false
long?≠long a aP zero eq with a 0
... | false = refl
... | true = ⊥-rec (ødisjη (sym eq))
long?≠long a aP (suc n) eq with a 0
... | false = long?≠long (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n (ηisInjective trunc eq)
... | true = ⊥-rec (ødisjη (sym eq))

-- given a sequence (a : ℕ → Bool) and two values x,y : A, the
-- sequence (seq-ch a x y true) is defined as follows: it returns y if
-- there exists an even number (k ≤ n) such that (a k = true) and
-- (a j = false) for all j < k; in all other cases seq-ch a x y true n
-- returns x.
seq-ch : {A : Type} (a : ℕ → Bool) (x y : A) → Bool → ℕ → A
seq-ch a x y b zero = if a 0 and b then y else x
seq-ch a x y b (suc n) = if a 0 and b then y else seq-ch (a ∘ suc) x y (not b) n

-- lemmata about the behaviour of seq-ch
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

diag-seq-ch :  (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true)) (n : ℕ) →
  res iPfin-ch n (seq-ch a long-ch (long?-ch a) true (suc n) .fst (suc n)) ≡ seq-ch a long-ch (long?-ch a) true n .fst n
diag-seq-ch a aP n with true-before? a n
... | yes (k , le , eq) with decEven k
... | inj₁ p =
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) k (≤-suc le) eq p)
  ∙ long?-res a n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem2 a long-ch (long?-ch a) true n k le eq p))
... | inj₂ p = 
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) k (≤-suc le) eq p)
  ∙ long-res n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem3 a aP long-ch (long?-ch a) false n k le eq p))
diag-seq-ch a aP n | no ¬p with dichotomyBool (a (suc n))
... | inj₂ q =
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem1 a long-ch (long?-ch a) true (suc n)
    (λ k le → rec⊎ (λ r → ⊥-rec (rec⊎ (λ p → ¬p (k , p , r)) (λ p → false≢true (sym q ∙ cong a (sym p) ∙ r)) (≤-suc-cases _ _ le)))
                    (λ r → r)
                    (dichotomyBool (a k))))
  ∙ long-res n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem1 a long-ch (long?-ch a) true n
      λ k le → rec⊎ (λ r → ⊥-rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))
... | inj₁ q  with decEven (suc n)
... | inj₁ ev = 
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) (suc n) ≤-refl q ev)
  ∙ long?-res' a aP n q
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem1 a long-ch (long?-ch a) true n
      λ k le → rec⊎ (λ r → ⊥-rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))
... | inj₂ odd =
  cong (λ z → res iPfin-ch n (z .fst (suc n))) (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) (suc n) ≤-refl q odd)
  ∙ long-res n
  ∙ cong (λ z → z .fst n) (sym (seq-ch-lem1 a long-ch (long?-ch a) true n
      λ k le → rec⊎ (λ r → ⊥-rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))

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

-- Assuming injectivity of m we prove LLPO.
module FromInjectivity (minj : ∀ s t → m s ≡ m t → s ≡ t) where

-- The implication factors through the fact that two-element subsets
-- of Vω are complete.

  complete : (x y1 y2 : Vω) (z : ℕ → Vω)
    → (∀ n → (z n ≡ y1) ⊎ (z n ≡ y2))
    → (∀ n → z n .fst n ≡ x .fst n)
    → ⟨ x ∈ₛ (η y1 ∪ η y2) ⟩
  complete x y1 y2 z p q = subst (λ z → ⟨ x ∈ₛ z ⟩) (minj s t (meq-lem s t eq)) (inl ∣ refl ∣)
    where
      t : Pfin Vω
      t = η y1 ∪ η y2

      s : Pfin Vω
      s = η x ∪ t

      sub : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
      sub n a = ∥rec∥ Pr.isPropPropTrunc
        (λ { (inj₁ r) →
                   ∥map∥ (λ eq → map⊎ (λ eq' → ∣ eq ∙ sym (q n) ∙ cong (λ w → w .fst n) eq' ∣)
                                      (λ eq' → ∣ eq ∙ sym (q n) ∙ cong (λ w → w .fst n) eq' ∣)
                                      (p n))
                         r ;
             (inj₂ r) → r })

      eq : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) s
                     ≡ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t
      eq n = antisym⊆ (sub n) (λ a → inr)

  llpo : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
    → ∥ (∀ n → isEven n → a n ≡ false) ⊎ (∀ n → isOdd n → a n ≡ false) ∥
  llpo a aP =
    ∥rec∥ Pr.isPropPropTrunc
      (λ { (inj₁ p) →
             ∥map∥ (λ eq → inj₁ (λ n ev → rec⊎ (λ q → ⊥-rec (case1 eq n ev q)) (λ q → q) (dichotomyBool (a n))))
                   p
         ; (inj₂ p) → 
             ∥map∥ (λ eq → inj₂ (λ n odd → rec⊎ (λ q → ⊥-rec (case2 eq n odd q)) (λ q → q) (dichotomyBool (a n))))
                   p })
      (complete x y1 y2 z lem1 lem2)
    where
      y1 : Vω
      y1 = long-ch
      
      y2 : Vω
      y2 = long?-ch a

      z : ℕ → Vω
      z = seq-ch a y1 y2 true

      x : Vω
      x = (λ n → z n .fst n) ,
          diag-seq-ch a aP

      lem1 : ∀ n → (z n ≡ y1) ⊎ (z n ≡ y2)
      lem1 = seq-ch-cases a y1 y2 true

      lem2 : ∀ n → z n .fst n ≡ x .fst n
      lem2 n = refl

      case1 : x ≡ y1 → ∀ n → isEven n → a n ≡ true → ⊥
      case1 eqx n ev eq = false≢true (sym (long?≠long a aP n bad) ∙ eq) 
        where
          bad : long? a (suc n) ≡ long (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ funExt⁻ (cong fst eqx) (suc n)

      case2 : x ≡ y2 → ∀ n → isOdd n → a n ≡ true → ⊥
      case2 eqx n ev eq = false≢true (sym (long?≠long a aP n (sym bad)) ∙ eq) 
        where
          bad : long (suc n) ≡ long? a (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ funExt⁻ (cong fst eqx) (suc n)

