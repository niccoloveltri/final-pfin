{-# OPTIONS --cubical --no-import-sorts #-}

module Pfin.AsFreeJoinSemilattice where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as Pr
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

-- finite powerset as a HIT (the free join semilattice on A)
data Pfin {ℓ} (A : Type ℓ) : Type ℓ where
  ø     : Pfin A
  η     : A → Pfin A
  _∪_   : Pfin A → Pfin A → Pfin A
  com  : ∀ x y → x ∪ y ≡ y ∪ x
  ass : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  idem  : ∀ x → x ∪ x ≡ x
  nr  : ∀ x → x ∪ ø ≡ x
  trunc : isSet (Pfin A)

-- recursion principle of Pfin
module _ {ℓ}{A B : Type ℓ} (Bset : isSet B)
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
_∈ₛ_ : ∀{A : Type} → A → Pfin A → hProp₀
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
    (∥rec∥ Pr.isPropPropTrunc λ { (inj₁ m) → inl (inl m)
                            ; (inj₂ m) → ∥map∥ (map⊎ inr (λ y → y)) m})
    (∥rec∥ Pr.isPropPropTrunc λ { (inj₁ m) → ∥map∥ (map⊎ (λ y → y) inl) m
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

-- Pfin action on functions
mapPfin : ∀ {ℓ}{A B : Type ℓ} → (A → B) → Pfin A → Pfin B
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
module _ {ℓ}{A : Type ℓ}
         (P : Pfin A → hProp ℓ) (pø : ⟨ P ø ⟩) (pη : ∀ a → ⟨ P (η a) ⟩)
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

-- functor laws of mapPfin
mapPfinId : ∀{ℓ} {A : Type ℓ} (s : Pfin A)
  → mapPfin (λ x → x) s ≡ s
mapPfinId =
  elimPfinProp (λ _ → _ , trunc _ _)
    refl
    (λ _ → refl)
    λ eq1 eq2 → cong₂ _∪_ eq1 eq2

mapPfinComp : ∀{ℓ} {A B C : Type ℓ} {g : B → C} {f : A → B} (s : Pfin A)
  → mapPfin g (mapPfin f s) ≡ mapPfin (g ∘ f) s
mapPfinComp =
  elimPfinProp (λ _ → _ , trunc _ _)
    refl
    (λ _ → refl)
    λ eq1 eq2 → cong₂ _∪_ eq1 eq2

-- an algebraic order on subsets , given by the presence of joins
_≤_ : ∀{A : Type} → Pfin A → Pfin A → Type₀
s ≤ t = (s ∪ t) ≡ t

antisym≤ : ∀{A : Type}{s t : Pfin A} → s ≤ t → t ≤ s → s ≡ t
antisym≤ p q = sym q ∙ com _ _ ∙ p

isProp≤ : ∀{A : Type}{s t : Pfin A} → isProp (s ≤ t)
isProp≤ = trunc _ _

-- joins are least upper bounds wrt. ≤
∪isLub : ∀{A : Type}{s t : Pfin A} (u : Pfin A)
  → s ≤ u → t ≤ u → (s ∪ t) ≤ u
∪isLub {s = s}{t} u ls lt =
  sym (ass _ _ _)
  ∙ cong (s ∪_) lt
  ∙ ls

-- subset relation expressed in terms of membership
_⊆_ : ∀{A : Type} → Pfin A → Pfin A → Type₀
s ⊆ t = ∀ x → ⟨ x ∈ₛ s ⟩ → ⟨ x ∈ₛ t ⟩

trans⊆ : ∀{A : Type} {xs ys zs : Pfin A}
  → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
trans⊆ p q x m = q x (p x m)  

-- ⊆ implies ≤ 
⊂2≤-η : ∀{A : Type}(a : A) (s : Pfin A) → ⟨ a ∈ₛ s ⟩ → η a ≤ s
⊂2≤-η a = elimPfinProp (λ _ → _ , isPropΠ λ x → isProp≤)
  (λ ())
  (λ b → ∥rec∥ isProp≤ λ eq → cong (_∪ η b) (cong η eq) ∙ idem _)
  (λ {s₁}{s₂} p₁ p₂ → ∥rec∥ isProp≤
    λ { (inj₁ m) → ass _ _ _ ∙ cong (_∪ _) (p₁ m)
      ; (inj₂ m) → ass _ _ _ ∙ cong (_∪ s₂) (com _ _) ∙ sym (ass _ _ _) ∙ cong (_ ∪_) (p₂ m)})

⊂2≤ : ∀{A : Type}(s t : Pfin A) → t ⊆ s → t ≤ s
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
  isProp× (isPropΠ (λ _ → isPropΠ (λ _ → Pr.isPropPropTrunc)))
          (isPropΠ (λ _ → isPropΠ (λ _ → Pr.isPropPropTrunc)))  

PfinRelₚ : ∀{X} (R : X → X → hProp₀)
  → Pfin X → Pfin X → hProp₀
PfinRelₚ R s t =
  PfinRel (λ x y → ⟨ R x y ⟩) s t , isPropPfinRel _ s t

-- relation lifting is a congruence
PfinRel∪ : ∀{X} (R : X → X → Type₀)
  → (s s' t t' : Pfin X)
  → PfinRel R s t → PfinRel R s' t'
  → PfinRel R (s ∪ s') (t ∪ t')
PfinRel∪ R s s' t t' (p , p') (q , q') =
  (λ x →
    ∥rec∥ Pr.isPropPropTrunc
      λ { (inj₁ m) → ∥map∥ (λ { (y , my , r) → y , inl my , r}) (p _ m)
        ; (inj₂ m) → ∥map∥ (λ { (y , my , r) → y , inr my , r}) (q _ m) }) ,
  (λ x →
    ∥rec∥ Pr.isPropPropTrunc
      λ { (inj₁ m) → ∥map∥ (λ { (y , my , r) → y , inl my , r}) (p' _ m)
        ; (inj₂ m) → ∥map∥ (λ { (y , my , r) → y , inr my , r}) (q' _ m) }) 

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
  elimPfinProp (λ x → _ , isPropΠ (λ _ → Pr.isPropPropTrunc))
    (λ ())
    (λ a → ∥map∥ (λ eq → a , ∣ refl ∣ , sym eq))
    λ p₁ p₂ → ∥rec∥ Pr.isPropPropTrunc
      (λ { (inj₁ m) → ∥map∥ (λ {(a , m , eq) → a , inl m , eq}) (p₁ m)
         ; (inj₂ m) → ∥map∥ (λ {(a , m , eq) → a , inr m , eq}) (p₂ m) })


-- some properties of ⊆
∪⊆ : ∀{A : Type} (s1 s2 t : Pfin A) →  s1 ⊆ t → s2 ⊆ t → (s1 ∪ s2) ⊆ t
∪⊆ s1 s2 t p q x =
  ∥rec∥ (snd (x ∈ₛ t)) λ { (inj₁ m) → p x m ; (inj₂ m) → q x m } 

∪⊆1 : ∀{A : Type} (s1 s2 t : Pfin A) →  (s1 ∪ s2) ⊆ t → s1 ⊆ t
∪⊆1 s1 s2 t p x m = p x (inl m)

∪⊆2 : ∀{A : Type} (s1 s2 t : Pfin A) →  (s1 ∪ s2) ⊆ t → s2 ⊆ t
∪⊆2 s1 s2 t p x m = p x (inr m)

map∪⊆ : ∀{A : Type} (s1 s2 t1 t2 : Pfin A) →  s1 ⊆ t1 → s2 ⊆ t2 → (s1 ∪ s2) ⊆ (t1 ∪ t2)
map∪⊆ s1 s2 t1 t2 p q x =
  ∥map∥ λ { (inj₁ m) → inj₁ (p x m) ; (inj₂ m) → inj₂ (q x m) }

⊆∪ : ∀{A : Type} (s1 s2 t : Pfin A)
  → t ⊆ (s1 ∪ s2) → ∃[ t1 ∈ Pfin A ] Σ[ t2 ∈ Pfin A ] (t1 ⊆ s1) × (t2 ⊆ s2) × (t ≡ t1 ∪ t2)
⊆∪ s1 s2 =
  elimPfinProp (λ _ → _ , isPropΠ (λ _ → Pr.isPropPropTrunc))
    (λ x → ∣ ø , ø , (λ { _ () }) , (λ { _ () }) , sym (idem _) ∣)
    (λ a m →
      ∥map∥
        (λ { (inj₁ p) → η a , ø ,
                         (λ x → ∥rec∥ (snd (x ∈ₛ s1)) λ eq → subst (λ z → ⟨ z ∈ₛ s1 ⟩) (sym eq) p) ,
                         (λ { _ () }) ,
                         sym (nr _) ;
             (inj₂ p) → ø , η a ,
                        (λ { _ () }) ,
                        (λ x → ∥rec∥ (snd (x ∈ₛ s2)) λ eq → subst (λ z → ⟨ z ∈ₛ s2 ⟩) (sym eq) p) ,
                        sym (com _ _ ∙ nr _) })
        (m a ∣ refl ∣))
    λ ih1 ih2 p →
      ∥rec∥ Pr.isPropPropTrunc
        (λ { (u1 , u2 , m1 , m2 , eq1) →
          ∥map∥
            (λ { (v1 , v2 , n1 , n2 , eq2) →
               (u1 ∪ v1) , (u2 ∪ v2) ,
               ∪⊆ u1 v1 s1 m1 n1 ,
               ∪⊆ u2 v2 s2 m2 n2 ,
               cong₂ _∪_ eq1 eq2
               ∙ ass _ _ _
               ∙ cong (_∪ v2) (sym (ass _ _ _)
                               ∙ cong (u1 ∪_) (com _ _)
                               ∙ ass _ _ _)
               ∙ sym (ass _ _ _) })
            (ih2 (λ x m → p x (inr m))) })
        (ih1 λ x m → p x (inl m))


pre⊆mapPfin : ∀{A B} (f : A → B) (s : Pfin A) (t : Pfin B)
  → t ⊆ mapPfin f s → ∃[ s' ∈ Pfin A ] (s' ⊆ s) × (mapPfin f s' ≡ t)
pre⊆mapPfin f s =
  elimPfinProp (λ x → _ , isPropΠ (λ _ → Pr.isPropPropTrunc))
    (λ x → ∣ ø , (λ { _ () }) , refl ∣)
    (λ b p →
      ∥map∥
        (λ { (a , m , eq) →
            η a ,
            (λ x → ∥rec∥ (snd (x ∈ₛ s)) λ r → subst (λ y → ⟨ y ∈ₛ s ⟩) (sym r) m) ,
            cong η eq})
        (pre∈ₛmapPfin f b s (p b ∣ refl ∣)))
    λ {t1} {t2} ih1 ih2 p →
      ∥rec∥ Pr.isPropPropTrunc
        (λ { (u1 , m1 , eq1) →
          ∥map∥
            (λ { (u2 , m2 , eq2) → (u1 ∪ u2) , ∪⊆ u1 u2 s m1 m2 , cong₂ _∪_ eq1 eq2 })
            (ih2 (∪⊆2 t1 t2 (mapPfin f s) p)) })
        (ih1 (∪⊆1 t1 t2 (mapPfin f s) p))

antisym⊆ : ∀{A : Type}{s t : Pfin A} → s ⊆ t → t ⊆ s → s ≡ t
antisym⊆ p q = antisym≤ (⊂2≤ _ _ p) (⊂2≤ _ _ q)

-- an equivalent definition of extensional equality of finite subsets
_≡ₛ_ : ∀{A : Type} → Pfin A → Pfin A → Type
s ≡ₛ t = (s ⊆ t) × (t ⊆ s)

-- injectivity of η

ηisInjective' : {A : Type} (setA : isSet A)
  → {a b : A}
  → η a ⊆ η b → a ≡ b
ηisInjective' setA {a} p =
  ∥rec∥ (setA _ _)
    (λ x → x)
    (p a ∣ refl ∣)

ηisInjective : {A : Type} (setA : isSet A)
  → {a b : A}
  → η a ≡ η b → a ≡ b
ηisInjective setA {a} eq = 
  ηisInjective' setA (subst (η a ⊆_) eq (λ _ m → m))  

-- ø dijoint from η

ødisjη' : {A : Type} {a : A} → η a ⊆ ø → ⊥
ødisjη' {a = a} p = p a ∣ refl ∣

ødisjη : {A : Type} {a : A} → η a ≡ ø → ⊥
ødisjη {a = a} eq = ødisjη' (subst (η a ⊆_) eq (λ _ m → m))

-- if a function g is injective, then mapPfin g is injective as well
mapPfinInj' : ∀{A B} (g : A → B) → (∀ x y → g x ≡ g y → x ≡ y)
  → (s t : Pfin A) → mapPfin g s ⊆ mapPfin g t → s ⊆ t
mapPfinInj' g injg s t p x m =
  ∥rec∥ (snd (x ∈ₛ t))
    (λ { (x' , m' , eq) → subst (λ z → ⟨ z ∈ₛ t ⟩) (injg _ _ eq) m' })
    (pre∈ₛmapPfin g _ t (p (g x) (∈ₛmapPfin g x s m)))

mapPfinInj : ∀{A B} (g : A → B) → (∀ x y → g x ≡ g y → x ≡ y)
  → (s t : Pfin A) → mapPfin g s ≡ mapPfin g t → s ≡ t
mapPfinInj g injg s t p =
  antisym⊆
    (mapPfinInj' g injg s t (subst (mapPfin g s ⊆_) p (λ _ m → m)))
    (mapPfinInj' g injg t s (subst (_⊆ mapPfin g s) p (λ _ m → m)))

-- mapPfin f s is empty iff s is empty
mapPfinø' : ∀{A B} (f : A → B) (s : Pfin A)
  → mapPfin f s ⊆ ø → s ⊆ ø
mapPfinø' f s p x m = p (f x) (∈ₛmapPfin f x s m)

mapPfinø : ∀{A B} (f : A → B) (s : Pfin A)
  → mapPfin f s ≡ ø → s ≡ ø
mapPfinø f s eq =
  antisym⊆
    (mapPfinø' f s (subst (mapPfin f s ⊆_) eq (λ _ m → m)))
    λ { _ ()}   

-- if mapPfin f s is a singleton η b, then s is a singleton in case f
-- is injective
mapPfinη' : ∀{A B} (setA : isSet A)
  → (f : A → B)  → (∀ x y → f x ≡ f y → x ≡ y)
  → (s : Pfin A) (b : B)
  → mapPfin f s ⊆ η b → η b ⊆ mapPfin f s
  → Σ[ a ∈ A ] s ≡ η a
mapPfinη' setA f injf s b p q =
  ∥rec∥ (λ { (x , r1) (y , r2) → Σ≡Prop (λ _ → trunc _ _) (ηisInjective setA (sym r1 ∙ r2)) })
    (λ { (a , ma , eq) → a ,
          (antisym⊆ (λ x mx → ∥map∥ (λ eq' → injf x a (eq' ∙ sym eq)) (p (f x) (∈ₛmapPfin f x s mx)))
                    (λ x → ∥rec∥ (snd (x ∈ₛ s)) (λ eqx → subst (λ z → ⟨ z ∈ₛ s ⟩) (sym eqx) ma))) })
    (pre∈ₛmapPfin f b s (q b ∣ refl ∣))

mapPfinη : ∀{A B} (setA : isSet A) 
  → (f : A → B)  → (∀ x y → f x ≡ f y → x ≡ y)
  → (s : Pfin A) (b : B)
  → mapPfin f s ≡ η b → Σ[ a ∈ A ] s ≡ η a
mapPfinη {A} setA f injf s b eq =
  mapPfinη' setA f injf s b
    (subst (mapPfin f s ⊆_) eq (λ _ m → m)) (subst (η b ⊆_) (sym eq) (λ _ m → m))

-- if mapPfin f s is a binary union t1 ∪ t2, then s is a binary union
-- s1 ∪ s2 with mapPfin f s1 ≡ t1 and mapPfin f s2 ≡ t2 in case f is
-- injective
∪⊆mapPfin : ∀{A B} (f : A → B)
  → (s : Pfin A) (t1 t2 : Pfin B)
  → (t1 ∪ t2) ⊆ mapPfin f s
  → ∃[ s1 ∈ Pfin A ] Σ[ s2 ∈ Pfin A ] ((s1 ∪ s2) ⊆ s) × (t1 ≡ mapPfin f s1) × (t2 ≡ mapPfin f s2)
∪⊆mapPfin f s t1 t2 mt =
  ∥rec∥ Pr.isPropPropTrunc
    (λ { (u1 , m1 , eq1) → ∥map∥
      (λ { (u2 , m2 , eq2) → u1 , u2 , ∪⊆ u1 u2 s m1 m2 , sym eq1 , sym eq2 })
      (pre⊆mapPfin f s t2 λ x mx → mt x (inr mx)) })
    (pre⊆mapPfin f s t1 λ x mx → mt x (inl mx))

∪≡mapPfin : ∀{A B} (f : A → B) → (∀ x y → f x ≡ f y → x ≡ y)
  → (s : Pfin A) (t1 t2 : Pfin B)
  → (t1 ∪ t2) ≡ mapPfin f s
  → ∃[ s1 ∈ Pfin A ] Σ[ s2 ∈ Pfin A ] (s1 ∪ s2 ≡ s) × (t1 ≡ mapPfin f s1) × (t2 ≡ mapPfin f s2)
∪≡mapPfin f injf s t1 t2 eq =
  ∥rec∥ Pr.isPropPropTrunc
    (λ { (u1 , m1 , eq1) → ∥map∥
      (λ { (u2 , m2 , eq2) → u1 , u2 , mapPfinInj f injf _ _ (cong₂ _∪_ eq1 eq2 ∙ eq) , sym eq1 , sym eq2 })
      (pre⊆mapPfin f s t2 (subst (t2 ⊆_) eq (λ _ → inr))) })
    (pre⊆mapPfin f s t1 (subst (t1 ⊆_) eq (λ _ → inl)))


-- if path equality on A is decidable, then also the membership
-- relation between A and Pfin A is decidable
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

-- if path equality on A is decidable, then also the subset relation
-- on Pfin A is decidable
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

-- if path equality on A is decidable, then also path equality on Pfin A
-- is decidable
PfinDecEq : {A : Type}
  → ((x y : A) → Dec (x ≡ y))
  → (x y : Pfin A) → Dec (x ≡ y)
PfinDecEq decEq x y with dec⊆ decEq x y | dec⊆ decEq y x
... | yes p | yes q = yes (antisym⊆ p q)
... | yes p | no ¬q = no (λ eq → ¬q (λ a → subst (λ z → ⟨ a ∈ₛ z ⟩) (sym eq)))
... | no ¬p | _ = no (λ eq → ¬p (λ a → subst (λ z → ⟨ a ∈ₛ z ⟩) eq))

-- Pfin preserves isomorphisms and equivalences
Pfin-iso : {A B : Type} → Iso A B → Iso (Pfin A) (Pfin B)
Pfin-iso AisoB =
  iso (mapPfin (Iso.fun AisoB))
      (mapPfin (Iso.inv AisoB))
      (λ x → mapPfinComp x ∙ (λ i → mapPfin (λ y → Iso.rightInv AisoB y i) x) ∙ mapPfinId x)
      λ x → mapPfinComp x ∙ (λ i → mapPfin (λ y → Iso.leftInv AisoB y i) x) ∙ mapPfinId x

Pfin≃ : {A B : Type} → A ≃ B → Pfin A ≃ Pfin B
Pfin≃ eq = isoToEquiv (Pfin-iso (equivToIso eq))
