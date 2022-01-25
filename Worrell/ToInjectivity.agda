{-# OPTIONS --sized-types --cubical --no-import-sorts #-}

module Worrell.ToInjectivity where

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

-- Proving that LLPO and countable choice imply injectivity of
-- (m : Pfin Vω → Vω)

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



module ToInjective (llpo : (a : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
                        → ∥ (∀ n → isEven n → a n ≡ false) ⊎ (∀ n → isOdd n → a n ≡ false) ∥)
                  (cc : (P : ℕ → Type) → (∀ n → ∥ P n ∥) → ∥ (∀ n → P n) ∥) where


  minj-lem2 : ∀ x t
    → (∀ n → ⟨ x .fst n ∈ₛ mapPfin (λ (x : ωLimit iPfin-ch) → x .fst n) t ⟩)
    → ⟨ x ∈ₛ t ⟩
  minj-lem2 x = elimPfinProp (λ t → _ , isPropΠ (λ _ → snd (x ∈ₛ t)))
    (λ p → p 0)
    (λ a p → ∥map∥ (λ q → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetiPfin _ _ _)) (funExt q)) (cc _ p))
    λ {s1}{s2} ih1 ih2 p → ∥rec∥ Pr.isPropPropTrunc (lem s1 s2 ih1 ih2) (cc _ p)
    where
      lem : (s1 s2 : Pfin Vω)
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
    antisym⊆ (minj-lem s t (λ n → subst (mapPfin (λ x → x .fst n) s ⊆_) (meq-lem2 s t eq n) (λ _ mx → mx)))
             (minj-lem t s (λ n → subst (mapPfin (λ x → x .fst n) t ⊆_) (meq-lem2 t s (sym eq) n) (λ _ mx → mx)))

