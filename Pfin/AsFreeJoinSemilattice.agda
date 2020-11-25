{-# OPTIONS --cubical --no-import-sorts #-}

module Pfin.AsFreeJoinSemilattice where

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
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Preliminaries

-- finite powerset as a HIT (the free join semilattice on A)
data Pfin (A : Type) : Type where
  ø     : Pfin A
  η     : A → Pfin A
  _∪_   : Pfin A → Pfin A → Pfin A
  com  : ∀ x y → x ∪ y ≡ y ∪ x
  ass : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  idem  : ∀ x → x ∪ x ≡ x
  nr  : ∀ x → x ∪ ø ≡ x
  trunc : isSet (Pfin A)

-- recursion principle of Pfin
module _ {A B : Type₀} (Bset : isSet B)
         (bø : B) (bη : A → B)
         (_b∪_ : B → B → B)
         (bcom  : ∀ x y → x b∪ y ≡ y b∪ x)
         (bass : ∀ x y z → x b∪ (y b∪ z) ≡ (x b∪ y) b∪ z)
         (bidem  : ∀ x → x b∪ x ≡ x)
         (bnr  : ∀ x → x b∪ bø ≡ x) where

  recPfin : Pfin A → B
  recPfin ø = bø
  recPfin (η x) = bη x
  recPfin (s ∪ s₁) = (recPfin s) b∪ (recPfin s₁)
  recPfin (com s s₁ i) = bcom (recPfin s) (recPfin s₁) i
  recPfin (ass s s₁ s₂ i) = bass (recPfin s) (recPfin s₁) (recPfin s₂) i
  recPfin (idem s i) = bidem (recPfin s) i
  recPfin (nr s i) = bnr (recPfin s) i
  recPfin (trunc s s₁ x y i i₁) =
    Bset (recPfin s) (recPfin s₁)
         (\ j → recPfin (x j)) (\ j → recPfin (y j))
         i i₁

-- finite subset membership
_∈ₛ_ : ∀{A} → A → Pfin A → hProp ℓ-zero
x ∈ₛ ø = ⊥ₚ
x ∈ₛ η y = x ≡ₚ y
x ∈ₛ (s₁ ∪ s₂) = (x ∈ₛ s₁) ⊔ (x ∈ₛ s₂)
x ∈ₛ com s₁ s₂ i =
  ⇔toPath {_} {x ∈ₛ s₁ ⊔ x ∈ₛ s₂} {x ∈ₛ s₂ ⊔ x ∈ₛ s₁}
    (∥map∥ λ { (inj₁ m) → inj₂ m ; (inj₂ m) → inj₁ m})
    (∥map∥ λ { (inj₁ m) → inj₂ m ; (inj₂ m) → inj₁ m})
    i
x ∈ₛ ass s₁ s₂ s₃ i = 
  ⇔toPath {_} {x ∈ₛ s₁ ⊔ x ∈ₛ s₂ ⊔ x ∈ₛ s₃} {(x ∈ₛ s₁ ⊔ x ∈ₛ s₂) ⊔ x ∈ₛ s₃}
    (∥rec∥ propTruncIsProp λ { (inj₁ m) → inl (inl m)
                            ; (inj₂ m) → ∥map∥ (map⊎ inr (λ y → y)) m})
    (∥rec∥ propTruncIsProp λ { (inj₁ m) → ∥map∥ (map⊎ (λ y → y) inl) m
                            ; (inj₂ m) → inr (inr m)})
    i
x ∈ₛ idem s i =
  ⇔toPath {_} {x ∈ₛ s ⊔ x ∈ₛ s} {x ∈ₛ s}
    (∥rec∥ (isProp⟨⟩ (x ∈ₛ s)) (λ { (inj₁ m) → m ; (inj₂ m) → m }))
    inl
    i
x ∈ₛ nr s i = 
  ⇔toPath {_} {x ∈ₛ s ⊔ ⊥ₚ} {x ∈ₛ s}
  (∥rec∥ (isProp⟨⟩ (x ∈ₛ s)) (λ { (inj₁ m) → m ; (inj₂ ()) }))
  inl
  i
x ∈ₛ trunc s₁ s₂ p q i j =
  isSetHProp (x ∈ₛ s₁) (x ∈ₛ s₂) (cong (x ∈ₛ_) p) (cong (x ∈ₛ_) q) i j

-- action on functions
mapPfin : ∀ {A B} → (A → B) → Pfin A → Pfin B
mapPfin f ø = ø
mapPfin f (η x) = η (f x)
mapPfin f (x ∪ y) = (mapPfin f x) ∪ (mapPfin f y)
mapPfin f (com x y i) = com (mapPfin f x) (mapPfin f y) i
mapPfin f (ass p p₁ p₂ i) = ass (mapPfin f p) (mapPfin f p₁) (mapPfin f p₂) i
mapPfin f (idem p i) = idem (mapPfin f p) i
mapPfin f (nr p i) = nr (mapPfin f p) i
mapPfin f (trunc p q x y i j) =
  trunc _ _ (cong (mapPfin f) x) (cong (mapPfin f) y) i j

-- elimination principle into a mere proposition
module _ {A : Type₀}
         (P : Pfin A → hProp ℓ-zero) (pø : ⟨ P ø ⟩) (pη : ∀ a → ⟨ P (η a) ⟩)
         (p∪ : ∀ {s₁ s₂} → ⟨ P s₁ ⟩ → ⟨ P s₂ ⟩ → ⟨ P (s₁ ∪ s₂) ⟩) where

  elimPfinProp : ∀ x → ⟨ P x ⟩
  elimPfinProp ø = pø
  elimPfinProp (η x) = pη x
  elimPfinProp (s ∪ s') = p∪ (elimPfinProp s) (elimPfinProp s')
  elimPfinProp (com s s' i) =
    isProp→PathP (λ j → snd (P (com s s' j)))
      (p∪ (elimPfinProp s) (elimPfinProp s'))
      (p∪ (elimPfinProp s') (elimPfinProp s))
      i
  elimPfinProp (ass s s₁ s₂ i) =
    isProp→PathP (λ j → snd (P (ass s s₁ s₂ j)))
      (p∪ (elimPfinProp s) (p∪ (elimPfinProp s₁) (elimPfinProp s₂)))
      (p∪ (p∪ (elimPfinProp s) (elimPfinProp s₁)) (elimPfinProp s₂))
      i
  elimPfinProp (idem s i) =
    isProp→PathP (λ j → snd (P (idem s j)))
      (p∪ (elimPfinProp s) (elimPfinProp s))
      (elimPfinProp s)
      i 
  elimPfinProp (nr s i) =
    isProp→PathP (λ j → snd (P (nr s j)))
      (p∪ (elimPfinProp s) pø)
      (elimPfinProp s)
      i 
  elimPfinProp (trunc s s' p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (snd (P x)))
      (elimPfinProp s) (elimPfinProp s')
      (cong elimPfinProp p) (cong elimPfinProp q)
      (trunc s s' p q)
      i j

-- an algebraic order, given by the presence of joins
_≤_ : ∀{A} → Pfin A → Pfin A → Type₀
s ≤ t = (s ∪ t) ≡ t

antisym≤ : ∀{A}{s t : Pfin A} → s ≤ t → t ≤ s → s ≡ t
antisym≤ p q = sym q ∙ com _ _ ∙ p

isProp≤ : ∀{A}{s t : Pfin A} → isProp (s ≤ t)
isProp≤ = trunc _ _

-- joins are least upper bounds wrt. ≤
∪isLub : ∀{A}{s t : Pfin A} (u : Pfin A)
  → s ≤ u → t ≤ u → (s ∪ t) ≤ u
∪isLub {s = s}{t} u ls lt =
  sym (ass _ _ _)
  ∙ cong (s ∪_) lt
  ∙ ls

-- subset relation
_⊆_ : ∀{A} → Pfin A → Pfin A → Type₀
s ⊆ t = ∀ x → ⟨ x ∈ₛ s ⟩ → ⟨ x ∈ₛ t ⟩

-- ⊆ implies ≤ 
⊂2≤-η : ∀{A}(a : A) (s : Pfin A) → ⟨ a ∈ₛ s ⟩ → η a ≤ s
⊂2≤-η a = elimPfinProp (λ _ → _ , isPropΠ λ x → isProp≤)
  (λ ())
  (λ b → ∥rec∥ isProp≤ λ eq → cong (_∪ η b) (cong η eq) ∙ idem _)
  (λ {s₁}{s₂} p₁ p₂ → ∥rec∥ isProp≤
    λ { (inj₁ m) → ass _ _ _ ∙ cong (_∪ _) (p₁ m)
      ; (inj₂ m) → ass _ _ _ ∙ cong (_∪ s₂) (com _ _) ∙ sym (ass _ _ _) ∙ cong (_ ∪_) (p₂ m)})

⊂2≤ : ∀{A}(s t : Pfin A) → t ⊆ s → t ≤ s
⊂2≤ s = elimPfinProp (λ _ → _ , isPropΠ λ x → isProp≤)
  (λ p → com ø s ∙ nr s)
  (λ a m → ⊂2≤-η a s (m a ∣ refl ∣))
  (λ p₁ p₂ q →
    ∪isLub s (p₁ (λ x m → q x (inl m))) (p₂ (λ x m → q x (inr m))))

-- canonical directed relation lifting on Pfin
PfinDRel : ∀{X Y} (R : X → Y → Type₀)
  → Pfin X → Pfin Y → Type₀
PfinDRel R s₁ s₂ =
  ∀ x → ⟨ x ∈ₛ s₁ ⟩ → ∃[ y ∈ _ ] ⟨ y ∈ₛ s₂ ⟩ × R x y

-- symmetric relation lifting
PfinRel : ∀{X} (R : X → X → Type₀)
  → Pfin X → Pfin X → Type₀
PfinRel R s₁ s₂ = 
  PfinDRel R s₁ s₂ × PfinDRel R s₂ s₁

isPropPfinRel : ∀{X} (R : X → X → Type₀)
  → ∀ s t → isProp (PfinRel R s t)
isPropPfinRel R s t =
  isProp× (isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))
          (isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))  

PfinRelₚ : ∀{X} (R : X → X → hProp₀)
  → Pfin X → Pfin X → hProp₀
PfinRelₚ R s t =
  PfinRel (λ x y → ⟨ R x y ⟩) s t , isPropPfinRel _ s t

-- extensional equality of finite subsets: they are equal if they
-- contain the same elements
PfinEq : ∀{X} → Pfin X → Pfin X → Type₀
PfinEq = PfinRel _≡_

-- extensional equality of finite subsets is equivalent to path
-- equality
PfinDRel⊆ : ∀{X}(s t : Pfin X) → PfinDRel _≡_ s t → s ⊆ t
PfinDRel⊆ s t p x mx =
  ∥rec∥ (snd (x ∈ₛ t))
    (λ { (y , my , eq) → subst (λ z → ⟨ z ∈ₛ t ⟩) (sym eq) my }) (p x mx)

PfinDRel⊆2 : ∀{X}(s t : Pfin X) → PfinDRel (λ y x → x ≡ y) t s → t ⊆ s
PfinDRel⊆2 s t p x mx = 
  ∥rec∥ (snd (x ∈ₛ s))
    (λ { (y , my , eq) → subst (λ z → ⟨ z ∈ₛ s ⟩) eq my }) (p x mx)

PfinEq→Eq : ∀{X} {s t : Pfin X} → PfinEq s t → s ≡ t
PfinEq→Eq {s = s}{t} (p₁ , p₂) =
  antisym≤ (⊂2≤ _ _ (PfinDRel⊆ s t p₁)) (⊂2≤ _ _ (PfinDRel⊆ t s p₂))

-- properties of membership in the image of a finite subset
∈ₛmapPfin : ∀{A B} (f : A → B) (a : A) (s : Pfin A)
  → ⟨ a ∈ₛ s ⟩ → ⟨ f a ∈ₛ mapPfin f s ⟩
∈ₛmapPfin f a =
  elimPfinProp (λ x → _ , isPropΠ (λ _ → snd (f a ∈ₛ mapPfin f x)))
    (λ ())
    (λ b → ∥map∥ (cong f))
    λ p₁ p₂ → ∥map∥ (map⊎ p₁ p₂)

pre∈ₛmapPfin : ∀{A B} (f : A → B) (b : B) (s : Pfin A)
  → ⟨ b ∈ₛ mapPfin f s ⟩ → ∃[ a ∈ A ] ⟨ a ∈ₛ s ⟩ × (f a ≡ b)
pre∈ₛmapPfin f b =
  elimPfinProp (λ x → _ , isPropΠ (λ _ → propTruncIsProp))
    (λ ())
    (λ a → ∥map∥ (λ eq → a , ∣ refl ∣ , sym eq))
    λ p₁ p₂ → ∥rec∥ propTruncIsProp
      (λ { (inj₁ m) → ∥map∥ (λ {(a , m , eq) → a , inl m , eq}) (p₁ m)
         ; (inj₂ m) → ∥map∥ (λ {(a , m , eq) → a , inr m , eq}) (p₂ m) })

-- turning a list into a finite subset
List→Pfin : ∀{A} → List A → Pfin A
List→Pfin [] = ø
List→Pfin (x ∷ xs) = η x ∪ List→Pfin xs

-- properties of membership in the finite subset associated to a list
∈ₛList→Pfin : ∀{A} (xs : List A){a : A}
  → ⟨ a ∈ₛ List→Pfin xs ⟩ → ∥ a ∈ xs ∥
∈ₛList→Pfin (x ∷ xs) = ∥rec∥ propTruncIsProp
  λ { (inj₁ p) → ∥map∥ (λ eq → subst (_∈ _) (sym eq) here) p
    ; (inj₂ p) → ∥map∥ there (∈ₛList→Pfin xs p)} 

List→Pfin∈ : ∀{A} (xs : List A){a : A}
  → a ∈ xs → ⟨ a ∈ₛ List→Pfin xs ⟩
List→Pfin∈ (x ∷ xs) here = inl ∣ refl ∣
List→Pfin∈ (x ∷ xs) (there p) = inr (List→Pfin∈ xs p)






