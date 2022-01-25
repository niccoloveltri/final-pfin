{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module Worrell.FromInjectivityOmega where

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
open import Worrell.FromInjectivity

ℓω : Vω2 → Vω
ℓω x = x .fst zero

-- We prove that the injectivity of ℓω implies LLPO

-- The sequences long and (long? a) can be extended to elements of Vω2
long2 : ∀ n → iPfin2 n
long2 zero = long-ch
long2 (suc n) = η (long2 n)

long2-res : ∀ n → iMapPfin2 n (long2 (suc n)) ≡ long2 n
long2-res zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _)) (funExt long-res)
long2-res (suc n) = cong η (long2-res n)

long2-ch : Vω2
long2-ch = long2 , long2-res

long2? : (a : ℕ → Bool) → ∀ n → iPfin2 n
long2? a zero = long?-ch a
long2? a (suc n) = if a 0 then ø else η (long2? (a ∘ suc) n)

long2?-res : (a : ℕ → Bool) 
  → ∀ n → iMapPfin2 n (long2? a (suc n)) ≡ long2? a n
long2?-res a zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
  (funExt (λ n → cong (iMapPfin n) (lem n (a 0)) ∙ long?-res a n))
  where
    lem : ∀ n → (b : Bool)
      → mapPfin (proj iPfin-ch n) (if b then ø else η (long?-ch (a ∘ suc)))
        ≡ (if b then ø else η (long? (a ∘ suc) n))
    lem n false = refl
    lem n true = refl
long2?-res a (suc n) with a 0
... | false = cong η (long2?-res (a ∘ suc) n)
... | true = refl

long2?-ch : (a : ℕ → Bool) → Vω2
long2?-ch a = long2? a , long2?-res a

-- another element of Vω, a variation of (long? a) that takes an
-- additional Boolean value b in input.

-- (long?? a true) is equal to long if the sequence a contains only
-- value false, but its height stop growing if there is *even* n : ℕ
-- such that (a n) is the first true in a.
long?? : (a : ℕ → Bool) → Bool → ∀ n → iPfin n
long?? a b zero = tt
long?? a b (suc n) =
  if a 0 and b then ø else η (long?? (a ∘ suc) (not b) n)

long??-res : (a : ℕ → Bool) (b : Bool)
  → ∀ n → iMapPfin n (long?? a b (suc n)) ≡ long?? a b n
long??-res a b zero = refl
long??-res a b (suc n) with a 0 | b
... | false | false = cong η (long??-res (a ∘ suc) true n)
... | false | true = cong η (long??-res (a ∘ suc) false n)
... | true | false = cong η (long??-res (a ∘ suc) true n)
... | true | true = refl

long??-ch : (a : ℕ → Bool) → Bool → Vω
long??-ch a b = long?? a b , long??-res a b

-- lemmata about the behaviour of long??
long??-lem1 : (a : ℕ → Bool) (b : Bool) (n : ℕ)
  → (∀ k → k ≤N n → a k ≡ false) → long?? a b n ≡ long n
long??-lem1 a b zero p = refl
long??-lem1 a b (suc n) p with dichotomyBool (a 0)
... | inj₁ eq = ⊥-rec (true≢false (sym eq ∙ p 0 zero-≤))
long??-lem1 a true (suc n) p | inj₂ eq =
  cong (λ z → if z and true then ø else η (long?? (a ∘ suc) false n)) eq
  ∙ cong η (long??-lem1 (a ∘ suc) false n (λ k le → p (suc k) (suc-≤-suc le)))
long??-lem1 a false (suc n) p | inj₂ eq =
  cong (λ z → if z and false then ø else η (long?? (a ∘ suc) true n)) eq
  ∙ cong η (long??-lem1 (a ∘ suc) true n (λ k le → p (suc k) (suc-≤-suc le)))

long??-lem2 : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → long?? a b n ≡ long? a n
long??-lem2 a aP b zero k lek eqk evk = refl
long??-lem2 a aP true (suc n) zero lek eqk evk =
  cong (λ z → if z and true then ø else η (long?? (a ∘ suc) false n)) eqk
  ∙ cong (λ z → if z then ø else η (long? (a ∘ suc) n)) (sym eqk) 
long??-lem2 a aP b (suc n) (suc k) lek eqk evk with dichotomyBool (a 0)
long??-lem2 a aP b (suc n) (suc k) lek eqk evk | inj₁ eq0 =
  ⊥-rec (snotz (cong fst (aP (_ , eqk) (_ , eq0))))
long??-lem2 a aP false (suc n) (suc k) lek eqk (suc ev) | inj₂ eq0 =
  cong (λ z → if z and false then ø else η (long?? (a ∘ suc) true n)) eq0
  ∙ cong η (long??-lem2 (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) true n k (pred-≤-pred lek) eqk ev)
  ∙ cong (λ z → if z then ø else η (long? (a ∘ suc) n)) (sym eq0) 
long??-lem2 a aP true (suc n) (suc k) lek eqk (suc odd) | inj₂ eq0 =
  cong (λ z → if z and true then ø else η (long?? (a ∘ suc) false n)) eq0
  ∙ cong η (long??-lem2 (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) false n k (pred-≤-pred lek) eqk odd)
  ∙ cong (λ z → if z then ø else η (long? (a ∘ suc) n)) (sym eq0) 

long??-lem3 : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → long?? a (not b) n ≡ long n
long??-lem3 a aP b zero k le eqk evk = refl
long??-lem3 a aP true (suc n) zero le eq0 evk =
  cong (λ z → if z and false then ø else η (long?? (a ∘ suc) true n)) eq0
  ∙ cong η (long??-lem1 (a ∘ suc) true n
      (λ k le → rec⊎ (λ eqk → ⊥-rec (snotz (cong fst (aP (_ , eqk) (_ , eq0))))) (λ x → x) (dichotomyBool (a (suc k)))))
long??-lem3 a aP b (suc n) (suc k) le eqk evk with dichotomyBool (a 0)
... | inj₁ eq0 = ⊥-rec (snotz (cong fst (aP (_ , eqk) (_ , eq0))))
long??-lem3 a aP false (suc n) (suc k) le eqk (suc ev) | inj₂ eq0 =
  cong (λ z → if z and true then ø else η (long?? (a ∘ suc) false n)) eq0
  ∙ cong η (long??-lem3 (a ∘ suc) ((λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) })) true n k (pred-≤-pred le) eqk ev)
long??-lem3 a aP true (suc n) (suc k) le eqk (suc odd) | inj₂ eq0 = 
  cong (λ z → if z and false then ø else η (long?? (a ∘ suc) true n)) eq0
  ∙ cong η (long??-lem3 (a ∘ suc) ((λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) })) false n k (pred-≤-pred le) eqk odd)

-- (long?? a true) is the same as the diagonal of
-- (seq-ch a long-ch (long?-ch a) true)
seq-ch-long?? : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true)) (n : ℕ)
  → seq-ch a long-ch (long?-ch a) true n .fst n ≡ long??-ch a true .fst n
seq-ch-long?? a aP n with true-before? a n
... | yes (k , le , eq) with decEven k
... | inj₁ ev =
  cong (λ z → z .fst n) (seq-ch-lem2 a long-ch (long?-ch a) true n k le eq ev)
  ∙ sym (long??-lem2 a aP true n k le eq ev)
... | inj₂ odd = 
  cong (λ z → z .fst n) (seq-ch-lem3 a aP long-ch (long?-ch a) false n k le eq odd)
  ∙ sym (long??-lem3 a aP false n k le eq odd )
seq-ch-long?? a aP n | no ¬p =
  cong (λ z → z .fst n) (seq-ch-lem1 a long-ch (long?-ch a) true n
          (λ k le → rec⊎ (λ eq → ⊥-rec (¬p (k , le , eq))) (λ x → x) (dichotomyBool (a k))))
  ∙ sym (long??-lem1 a true n (λ k le → rec⊎ (λ eq → ⊥-rec (¬p (k , le , eq))) (λ x → x) (dichotomyBool (a k))))

-- long?? also extends to an element of Vω2
long2?? : (a : ℕ → Bool) → Bool → ∀ n → iPfin2 n
long2?? a b zero = long??-ch a b
long2?? a b (suc n) =
  if a 0 and b then ø else η (long2?? (a ∘ suc) (not b) n)

long2??-res : (a : ℕ → Bool) (b : Bool)
  → ∀ n → iMapPfin2 n (long2?? a b (suc n)) ≡ long2?? a b n
long2??-res a b zero = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
  (funExt (λ n → cong (iMapPfin n) (lem n b (a 0)) ∙ long??-res a b n))
  where
    lem : ∀ n → (b b' : Bool)
      → mapPfin (proj iPfin-ch n) (if b' and b then ø else η (long??-ch (a ∘ suc) (not b)))
        ≡ (if b' and b then ø else η (long?? (a ∘ suc) (not b) n))
    lem n false false = refl
    lem n true false = refl
    lem n false true = refl
    lem n true true = refl
long2??-res a b (suc n) with a 0 | b
... | false | false = cong η (long2??-res (a ∘ suc) true n)
... | false | true = cong η (long2??-res (a ∘ suc) false n)
... | true | false = cong η (long2??-res (a ∘ suc) true n)
... | true | true = refl

long2??-ch : (a : ℕ → Bool) → Bool → Vω2
long2??-ch a b = long2?? a b , long2??-res a b

-- injectivity of ℓω implies LLPO

-- again the implication factors through some form of completeness
-- theorem
module FromInjectivityOmega (ℓωinj : (s t : Vω2) → ℓω s ≡ ℓω t → s ≡ t) where

  ℓω+1inj : (s t : Vω2) → m (s .fst 1) ≡ m (t .fst 1) → s ≡ t
  ℓω+1inj s t eq = ℓωinj s t (sym (s .snd 0) ∙ eq ∙ t .snd 0)

  joinω : (x y : ∀ n → iPfin n) → ∀ n → iPfin n
  joinω x y zero = tt
  joinω x y (suc n) = η (x n) ∪ η (y n)

  joinω-res : (x y : Vω)
    → ∀ n → iMapPfin n (joinω (x .fst) (y .fst) (suc n)) ≡ joinω (x .fst) (y .fst) n
  joinω-res x y zero = refl
  joinω-res x y (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong η (y .snd n))

  joinω-ch : (x y : Vω) → Vω
  joinω-ch x y = joinω (x .fst) (y .fst) , joinω-res x y

  joinω2 : (x y : ∀ n → iPfin2 n) → ∀ n → iPfin2 n
  joinω2 x y zero = joinω-ch (x 0) (y 0)
  joinω2 x y (suc n) = η (x n) ∪ η (y n)

  joinω2-res : (x y : Vω2)
    → ∀ n → iMapPfin2 n (joinω2 (x .fst) (y .fst) (suc n)) ≡ joinω2 (x .fst) (y .fst) n
  joinω2-res x y zero =
    Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
           (funExt (joinω-res (x .fst 0) (y .fst 0)))
  joinω2-res x y (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong η (y .snd n))

  joinω2-ch : (x y : Vω2) → Vω2
  joinω2-ch x y = joinω2 (x .fst) (y .fst) , joinω2-res x y

  3joinω : (x y z : ∀ n → iPfin n) → ∀ n → iPfin n
  3joinω x y z zero = tt
  3joinω x y z (suc n) = η (x n) ∪ (η (y n) ∪ η (z n))

  3joinω-res : (x y z : Vω)
    → ∀ n → iMapPfin n (3joinω (x .fst) (y .fst) (z .fst) (suc n)) ≡ 3joinω (x .fst) (y .fst) (z .fst) n
  3joinω-res x y z zero = refl
  3joinω-res x y z (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong₂ _∪_ (cong η (y .snd n)) (cong η (z .snd n)))

  3joinω-ch : (x y z : Vω) → Vω
  3joinω-ch x y z = 3joinω (x .fst) (y .fst) (z .fst) , 3joinω-res x y z

  3joinω2 : (x y z : ∀ n → iPfin2 n) → ∀ n → iPfin2 n
  3joinω2 x y z zero = 3joinω-ch (x 0) (y 0) (z 0)
  3joinω2 x y z (suc n) = η (x n) ∪ (η (y n) ∪ η (z n))

  3joinω2-res : (x y z : Vω2)
    → ∀ n → iMapPfin2 n (3joinω2 (x .fst) (y .fst) (z .fst) (suc n)) ≡ 3joinω2 (x .fst) (y .fst) (z .fst) n
  3joinω2-res x y z zero =
    Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _))
           (funExt (3joinω-res (x .fst 0) (y .fst 0) (z .fst 0)))
  3joinω2-res x y z (suc n) = cong₂ _∪_ (cong η (x .snd n)) (cong₂ _∪_ (cong η (y .snd n)) (cong η (z .snd n)))

  3joinω2-ch : (x y z : Vω2) → Vω2
  3joinω2-ch x y z = 3joinω2 (x .fst) (y .fst) (z .fst) , 3joinω2-res x y z

  complete : (x : Vω2) (y1 y2 : Vω2) (z : ℕ → Vω)
    → (∀ n → (z n ≡ y1 .fst 0) ⊎ (z n ≡ y2 .fst 0))
    → (∀ n → z n .fst n ≡ x .fst 0 .fst n)
    → ⟨ x .fst 0 ∈ₛ (η (y1 .fst 0) ∪ η (y2 .fst 0)) ⟩
  complete x y1 y2 z p q =
    subst (λ z → ⟨ x .fst 0 ∈ₛ z ⟩) (funExt⁻ (cong fst (ℓω+1inj s t (meq-lem (s .fst 1) (t .fst 1) eq))) 1) (inl ∣ refl ∣)
    where
      t : Vω2
      t = joinω2-ch y1 y2

      s : Vω2
      s = 3joinω2-ch x y1 y2

      sub : ∀ n → mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) (s .fst 1)
                    ⊆ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) (t .fst 1)
      sub zero a _ = ∣ inj₁ ∣ refl ∣ ∣
      sub (suc n) a = ∥rec∥ Pr.isPropPropTrunc
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
    ∥rec∥ Pr.isPropPropTrunc
      (λ { (inj₁ p) →
             ∥map∥ (λ eq → inj₁ (λ n ev → rec⊎ (λ q → ⊥-rec (case1 eq n ev q)) (λ q → q) (dichotomyBool (a n))))
                   p
         ; (inj₂ p) → 
             ∥map∥ (λ eq → inj₂ (λ n odd → rec⊎ (λ q → ⊥-rec (case2 eq n odd q)) (λ q → q) (dichotomyBool (a n))))
                   p })
      (complete x y1 y2 z lem1 lem2)
    where
      y1 : Vω2
      y1 = long2-ch
      
      y2 : Vω2
      y2 = long2?-ch a

      z : ℕ → Vω
      z = seq-ch a long-ch (long?-ch a) true

      x : Vω2
      x = long2??-ch a true

      lem1 : ∀ n → (z n ≡ y1 .fst 0) ⊎ (z n ≡ y2 .fst 0)
      lem1 = seq-ch-cases a _ _ true

      lem2 : ∀ n → z n .fst n ≡ x .fst 0 .fst n
      lem2 n = seq-ch-long?? a aP n

      case1 : x .fst 0 ≡ y1 .fst 0 → ∀ n → isEven n → a n ≡ true → ⊥
      case1 eqx n ev eq = false≢true (sym (long?≠long a aP n bad) ∙ eq) 
        where
          bad : long? a (suc n) ≡ long (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ seq-ch-long?? a aP (suc n)
            ∙ funExt⁻ (cong fst eqx) (suc n)

      case2 : x .fst 0 ≡ y2 .fst 0 → ∀ n → isOdd n → a n ≡ true → ⊥
      case2 eqx n ev eq = false≢true (sym (long?≠long a aP n (sym bad)) ∙ eq) 
        where
          bad : long (suc n) ≡ long? a (suc n)
          bad =
            sym (funExt⁻ (cong fst (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
            ∙ seq-ch-long?? a aP (suc n)
            ∙ funExt⁻ (cong fst eqx) (suc n)

