{-# OPTIONS --cubical --no-import-sorts #-}

module Basics where

open import Cubical.Foundations.Everything
open import Cubical.Relation.Binary hiding (Rel)
open import Cubical.Data.Nat
open import Cubical.Data.Sum renaming (rec to rec⊎)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order hiding (eq) renaming (_≟_ to _≟N_)
open BinaryRelation
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)

-- some basic stuff
hProp₀ = hProp ℓ-zero

isPropFunEq : ∀{ℓ}{A B : Type ℓ} (f g : A → B)
  → (∀ x → isProp (f x ≡ g x))
  → isProp (f ≡ g)
isPropFunEq f g p eq1 eq2 i j x =
  p x (λ k → eq1 k x) (λ k → eq2 k x) i j 

EqFiber : {A B : Type} → isSet B
  → (f : A → B) (b : B)
  → {a a' : A} → a ≡ a'
  → (eq : f a ≡ b) (eq' : f a' ≡ b)
  → _≡_ {A = fiber f b} (a , eq) (a' , eq')
EqFiber setB f b =
  J (λ a _ → (eq : f _ ≡ b) (eq' : f a ≡ b)
       → _≡_ {A = fiber f b} (_ , eq) (a , eq'))
    λ p q → cong (_ ,_) (setB _ _ p q)

≤-suc-cases : ∀ k n → k ≤ suc n
  → (k ≤ n) ⊎ (k ≡ suc n)
≤-suc-cases zero n le = inl zero-≤
≤-suc-cases (suc k) zero le = inr (cong suc (≤0→≡0 (pred-≤-pred le)))
≤-suc-cases (suc k) (suc n) le with ≤-suc-cases k n (pred-≤-pred le)
... | inl p = inl (suc-≤-suc p)
... | inr p = inr (cong suc p)

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

decEven : ∀ n → isEven n ⊎ isOdd n
decEven zero = inl zero
decEven (suc n) =
  rec⊎ (λ z → inr (suc z)) (λ z → inl (suc z)) (decEven n)

even-not-odd : ∀ {n} → isEven n → isOdd n → ⊥
even-not-odd (suc x₁) (suc x) = even-not-odd x x₁

decIsProp : {A : Type}
  → isProp A
  → isProp (Dec A)
decIsProp propA (yes p) (yes q) = cong yes (propA _ _)
decIsProp propA (yes p) (no ¬p) = ⊥-rec (¬p p)
decIsProp propA (no ¬p) (yes p) = ⊥-rec (¬p p)
decIsProp propA (no ¬p) (no ¬q) = cong no (funExt (λ _ → isProp⊥ _ _))

decPropTrunc : {A : Type} → Dec A → Dec ∥ A ∥ 
decPropTrunc (yes a) = yes ∣ a ∣
decPropTrunc (no ¬a) = no (∥rec∥ isProp⊥ ¬a)

true-before? : (a : ℕ → Bool) (n : ℕ)
  → Dec (Σ[ k ∈ ℕ ] (k ≤ n) × (a k ≡ true))
true-before? a zero with a zero ≟ true
... | yes p = yes (0 , ≤-refl , p)
... | no ¬p = no (λ { (k , k≤ , eq) →
  ¬p (cong a (sym (≤0→≡0 k≤)) ∙ eq) })
true-before? a (suc n) with true-before? a n
... | yes (k , k≤ , eq) = yes (k , ≤-suc k≤ , eq)
... | no ¬ih with a (suc n) ≟ true
... | yes p = yes (suc n , ≤-refl , p)
... | no ¬p = no (λ { (k , k≤ , eq) → rec⊎ (λ r → ¬ih (_ , r , eq)) (λ r → ¬p (cong a (sym r) ∙ eq)) (≤-suc-cases k n k≤) })



