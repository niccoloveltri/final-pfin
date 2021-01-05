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
open import Cubical.Data.Nat renaming (elim to elimNat)
open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Binary
open import Preliminaries
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

-- an algebraic order, given by the presence of joins
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

-- subset relation
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
  isProp× (isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))
          (isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))  

PfinRelₚ : ∀{X} (R : X → X → hProp₀)
  → Pfin X → Pfin X → hProp₀
PfinRelₚ R s t =
  PfinRel (λ x y → ⟨ R x y ⟩) s t , isPropPfinRel _ s t

PfinRel∪ : ∀{X} (R : X → X → Type₀)
  → (s s' t t' : Pfin X)
  → PfinRel R s t → PfinRel R s' t'
  → PfinRel R (s ∪ s') (t ∪ t')
PfinRel∪ R s s' t t' (p , p') (q , q') =
  (λ x →
    ∥rec∥ propTruncIsProp
      λ { (inj₁ m) → ∥map∥ (λ { (y , my , r) → y , inl my , r}) (p _ m)
        ; (inj₂ m) → ∥map∥ (λ { (y , my , r) → y , inr my , r}) (q _ m) }) ,
  (λ x →
    ∥rec∥ propTruncIsProp
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
  elimPfinProp (λ x → _ , isPropΠ (λ _ → propTruncIsProp))
    (λ ())
    (λ a → ∥map∥ (λ eq → a , ∣ refl ∣ , sym eq))
    λ p₁ p₂ → ∥rec∥ propTruncIsProp
      (λ { (inj₁ m) → ∥map∥ (λ {(a , m , eq) → a , inl m , eq}) (p₁ m)
         ; (inj₂ m) → ∥map∥ (λ {(a , m , eq) → a , inr m , eq}) (p₂ m) })

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
  elimPfinProp (λ _ → _ , isPropΠ (λ _ → propTruncIsProp))
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
      ∥rec∥ propTruncIsProp
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
  elimPfinProp (λ x → _ , isPropΠ (λ _ → propTruncIsProp))
    (λ x → ∣ ø , (λ { _ () }) , refl ∣)
    (λ b p →
      ∥map∥
        (λ { (a , m , eq) →
            η a ,
            (λ x → ∥rec∥ (snd (x ∈ₛ s)) λ r → subst (λ y → ⟨ y ∈ₛ s ⟩) (sym r) m) ,
            cong η eq})
        (pre∈ₛmapPfin f b s (p b ∣ refl ∣)))
    λ {t1} {t2} ih1 ih2 p →
      ∥rec∥ propTruncIsProp
        (λ { (u1 , m1 , eq1) →
          ∥map∥
            (λ { (u2 , m2 , eq2) → (u1 ∪ u2) , ∪⊆ u1 u2 s m1 m2 , cong₂ _∪_ eq1 eq2 })
            (ih2 (∪⊆2 t1 t2 (mapPfin f s) p)) })
        (ih1 (∪⊆1 t1 t2 (mapPfin f s) p))


{-
pre⊆mapPfin : ∀{A B} (f : A → B) (s : Pfin A) (t : Pfin B)
  → t ⊆ mapPfin f s → ∃[ s' ∈ Pfin A ] (s' ⊆ s) × (mapPfin f s' ≡ t)
pre⊆mapPfin f =
  elimPfinProp (λ x → _ , isPropΠ (λ _ → isPropΠ (λ _ → propTruncIsProp)))
    (λ _ p → ∣ ø , (λ _ z → z) , PfinEq→Eq ((λ { _ () }) , λ b m → ⊥-elim (p b m)) ∣)
    (λ a t p → ∣ η a , (λ x m → m) , {!!} ∣)
    λ {s1} {s2} ih1 ih2 t p →
      ∥rec∥ propTruncIsProp
        (λ { (t1 , t2 , m1 , m2 , eq) →
          ∥rec∥ propTruncIsProp
            (λ { (u1 , n1 , eq1) →
              ∥map∥
                (λ { (u2 , n2 , eq2) →
                   (u1 ∪ u2) ,
                   map∪⊆ u1 u2 s1 s2 n1 n2 ,
                   cong₂ _∪_ eq1 eq2 ∙ sym eq })
                (ih2 t2 m2) })
            (ih1 t1 m1) })
        (⊆∪ (mapPfin f s1) (mapPfin f s2) t p)
-}  


-- turning a list into a finite subset
List→Pfin : ∀{A : Type} → List A → Pfin A
List→Pfin [] = ø
List→Pfin (x ∷ xs) = η x ∪ List→Pfin xs

-- properties of membership in the finite subset associated to a list
∈ₛList→Pfin : ∀{A : Type} (xs : List A){a : A}
  → ⟨ a ∈ₛ List→Pfin xs ⟩ → ∥ a ∈ xs ∥
∈ₛList→Pfin (x ∷ xs) = ∥rec∥ propTruncIsProp
  λ { (inj₁ p) → ∥map∥ (λ eq → subst (_∈ _) (sym eq) here) p
    ; (inj₂ p) → ∥map∥ there (∈ₛList→Pfin xs p)} 

List→Pfin∈ : ∀{A : Type} (xs : List A){a : A}
  → a ∈ xs → ⟨ a ∈ₛ List→Pfin xs ⟩
List→Pfin∈ (x ∷ xs) here = inl ∣ refl ∣
List→Pfin∈ (x ∷ xs) (there p) = inr (List→Pfin∈ xs p)



antisym⊆ : ∀{A : Type}{s t : Pfin A} → s ⊆ t → t ⊆ s → s ≡ t
antisym⊆ p q = antisym≤ (⊂2≤ _ _ p) (⊂2≤ _ _ q)

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

_≡ₛ_ : ∀{A : Type} → Pfin A → Pfin A → Type
s ≡ₛ t = (s ⊆ t) × (t ⊆ s)

_×p_ : {A B C : Type} → (A → C) → (B → C) → Type
_×p_ {A}{B} f g = Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ g b

Eq×p : {A B C : Type} → isSet C
  → (f : A → C)(g : B → C)
  → {a a' : A} → a ≡ a' 
  → {b b' : B} → b ≡ b'
  → (eq : f a ≡ g b) (eq' : f a' ≡ g b')
  → _≡_ {A = f ×p g} (a , b , eq) (a' , b' , eq')
Eq×p setC f g =
  J (λ y _ → ∀ {b b'} → b ≡ b'
     → (eq : f _ ≡ g b) (eq' : f y ≡ g b')
     → _≡_ {A = f ×p g} (_ , b , eq) (y , b' , eq'))
  (J (λ y _ → (eq : f _ ≡ g _) (eq' : f _ ≡ g y)
        → _≡_ {A = f ×p g} (_ , _ , eq) (_ , y , eq'))
     λ p q → cong (λ x → _ , _ , x) (setC _ _ p q))

{-
≡Pfin×p' : {A B C : Type} → isSet C
  → (f : A → C) → (∀ x y → f x ≡ f y → x ≡ y)
  → (g : B → C) → (∀ x y → g x ≡ g y → x ≡ y)
  → (s t : Pfin (f ×p g))
  → mapPfin fst s ⊆ mapPfin fst t
  → mapPfin (fst ∘ snd) s ⊆ mapPfin (fst ∘ snd) t
  → s ⊆ t
≡Pfin×p' setC f injf g injg s t p q x@(a , b , eq) m =
  {!p a (∈ₛmapPfin fst x s m)!}

≡Pfin×p : {A B C : Type} → isSet C
  → (f : A → C) → (∀ x y → f x ≡ f y → x ≡ y)
  → (g : B → C) → (∀ x y → g x ≡ g y → x ≡ y)
  → (s t : Pfin (f ×p g))
  → mapPfin fst s ≡ mapPfin fst t
  → mapPfin (fst ∘ snd) s ≡ mapPfin (fst ∘ snd) t
  → s ≡ t
≡Pfin×p = {!!}
-}


∈Pfin×p : {A B C : Type} → isSet C 
  → (f : A → C) (g : B → C) → (∀ x y → g x ≡ g y → x ≡ y)
  → {a : A} {b : B} (eq : f a ≡ g b) (s : Pfin (f ×p g))
  → ⟨ a ∈ₛ mapPfin fst s ⟩
  → ⟨ (a , b , eq) ∈ₛ s ⟩
∈Pfin×p setC f g injg eq s ma =
  ∥rec∥ (snd ((_ , _ , eq) ∈ₛ s))
    (λ { ((a' , b' , eq') , m , r) →
      J (λ y _ → (eq : f y ≡ g _) → ⟨ (y , _ , eq) ∈ₛ s ⟩ )
        (λ eq →
          J (λ y _ → (eq : f _ ≡ g y) → ⟨ (a' , y , eq) ∈ₛ s ⟩ )
            (λ eq → subst (λ z → ⟨ (a' , b' , z) ∈ₛ s ⟩) (setC _ _ _ _) m)
            (injg b' _ (sym eq' ∙ eq)) eq)
        r eq })
    (pre∈ₛmapPfin fst _ s ma)


EqFiber : {A B : Type} → isSet B
  → (f : A → B) (b : B)
  → {a a' : A} → a ≡ a'
  → (eq : f a ≡ b) (eq' : f a' ≡ b)
  → _≡_ {A = fiber f b} (a , eq) (a' , eq')
EqFiber setB f b =
  J (λ a _ → (eq : f _ ≡ b) (eq' : f a ≡ b)
       → _≡_ {A = fiber f b} (_ , eq) (a , eq'))
    λ p q → cong (_ ,_) (setB _ _ p q)

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


mapPfinø' : ∀{A B} (f : A → B) (s : Pfin A)
  → mapPfin f s ⊆ ø → s ⊆ ø
mapPfinø' f s p x m = p (f x) (∈ₛmapPfin f x s m)

mapPfinø : ∀{A B} (f : A → B) (s : Pfin A)
  → mapPfin f s ≡ ø → s ≡ ø
mapPfinø f s eq =
  antisym⊆
    (mapPfinø' f s (subst (mapPfin f s ⊆_) eq (λ _ m → m)))
    λ { _ ()}   

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

∪⊆mapPfin : ∀{A B} (f : A → B)
  → (s : Pfin A) (t1 t2 : Pfin B)
  → (t1 ∪ t2) ⊆ mapPfin f s
  → ∃[ s1 ∈ Pfin A ] Σ[ s2 ∈ Pfin A ] ((s1 ∪ s2) ⊆ s) × (t1 ≡ mapPfin f s1) × (t2 ≡ mapPfin f s2)
∪⊆mapPfin f s t1 t2 mt =
  ∥rec∥ propTruncIsProp
    (λ { (u1 , m1 , eq1) → ∥map∥
      (λ { (u2 , m2 , eq2) → u1 , u2 , ∪⊆ u1 u2 s m1 m2 , sym eq1 , sym eq2 })
      (pre⊆mapPfin f s t2 λ x mx → mt x (inr mx)) })
    (pre⊆mapPfin f s t1 λ x mx → mt x (inl mx))

∪≡mapPfin : ∀{A B} (f : A → B) → (∀ x y → f x ≡ f y → x ≡ y)
  → (s : Pfin A) (t1 t2 : Pfin B)
  → (t1 ∪ t2) ≡ mapPfin f s
  → ∃[ s1 ∈ Pfin A ] Σ[ s2 ∈ Pfin A ] (s1 ∪ s2 ≡ s) × (t1 ≡ mapPfin f s1) × (t2 ≡ mapPfin f s2)
∪≡mapPfin f injf s t1 t2 eq =
  ∥rec∥ propTruncIsProp
    (λ { (u1 , m1 , eq1) → ∥map∥
      (λ { (u2 , m2 , eq2) → u1 , u2 , mapPfinInj f injf _ _ (cong₂ _∪_ eq1 eq2 ∙ eq) , sym eq1 , sym eq2 })
      (pre⊆mapPfin f s t2 (subst (t2 ⊆_) eq (λ _ → inr))) })
    (pre⊆mapPfin f s t1 (subst (t1 ⊆_) eq (λ _ → inl)))

to×p : ∀{A B C} (f : A → C) (g : B → C)
  → Pfin (f ×p g) → mapPfin f ×p mapPfin g
to×p f g s = mapPfin fst s , mapPfin (fst ∘ snd) s ,
  mapPfinComp s
  ∙ cong (λ z → mapPfin z s) (λ i p → snd (snd p) i)
  ∙ sym (mapPfinComp s)

to×pEquiv : ∀{A B C} (setB : isSet B) (setC : isSet C)
  → (f : A → C) (g : B → C)
  → ((∀ x y → g x ≡ g y → x ≡ y))
  → (as : Pfin A) (bs : Pfin B) (p : mapPfin f as ≡ mapPfin g bs)
  → isContr (fiber (to×p f g) (as , bs , p))
to×pEquiv setB setC f g injg =
  elimPfinProp (λ _ → _ , isPropΠ (λ _ → isPropΠ (λ _ → isPropIsContr)))
    (λ t eq →
      (ø ,
       Eq×p trunc _ _ refl (sym (mapPfinø g _ (sym eq))) _ eq) ,
       λ { (cs , eq') →
         EqFiber
          (isSetΣ trunc (λ _ → isSetΣ trunc (λ _ → isProp→isSet (trunc _ _)))) _ _
          (sym (mapPfinø fst cs (cong fst eq'))) _ _ }) 
    (λ a t eq →
      let (b , eq') = mapPfinη setB g injg t (f a) (sym eq) in
        ((η (a , b , ηisInjective setC (eq ∙ cong (mapPfin g) eq'))) ,
         Eq×p trunc _ _ refl (sym eq') _ _) ,
         λ { (w , eqw) →
           EqFiber (isSetΣ trunc (λ _ → isSetΣ trunc (λ _ → isProp→isSet (trunc _ _)))) _ _
                   (antisym⊆
                     (λ { x@(a' , b' , fa'≡gb') → ∥rec∥ (snd (x ∈ₛ w))
                       (λ eqx →
                         ∈Pfin×p setC f g injg fa'≡gb' w
                                 (subst (λ z → ⟨ a' ∈ₛ z ⟩) (cong fst (sym eqw)) ∣ cong fst eqx ∣)) })
                     λ { x@(a' , b' , fa'≡gb') mx →
                       ∈Pfin×p setC f g injg fa'≡gb' (η (a , b , _))
                               (subst (λ z → ⟨ a' ∈ₛ z ⟩) (cong fst eqw) (∈ₛmapPfin fst x w mx))})
                   _ _ }) 
    λ {s1} {s2} ih1 ih2 t eq →
      ∥rec∥ isPropIsContr
        (λ { (u1 , u2 , eqt , eq1 , eq2) → 
          let ((v1 , q1) , r1) = ih1 u1 eq1 in
          let ((v2 , q2) , r2) = ih2 u2 eq2 in
            ((v1 ∪ v2) ,
             Eq×p trunc _ _
                  (cong₂ _∪_ (cong fst q1) (cong fst q2))
                  (cong₂ _∪_ (cong (fst ∘ snd) q1) (cong (fst ∘ snd) q2)
                   ∙ mapPfinInj g injg _ _ (cong₂ _∪_ (sym eq1) (sym eq2) ∙ eq))
                  _ _) ,
             λ { (w , eqw) →
               EqFiber (isSetΣ trunc (λ _ → isSetΣ trunc (λ _ → isProp→isSet (trunc _ _)))) _ _
                       (cong₂ _∪_ (cong fst (r1 (v1 , q1)))
                                  (cong fst (r2 (v2 , q2)))
                       ∙ antisym⊆
                           (λ x@(a , b , fa≡gb) → ∥rec∥ (snd (x ∈ₛ w))
                             (λ { (inj₁ mx) →
                                   ∈Pfin×p setC f g injg fa≡gb w
                                           (subst (λ z → ⟨ a ∈ₛ z ⟩)
                                                (cong fst (sym eqw))
                                                (inl (subst (λ z → ⟨ a ∈ₛ z ⟩)
                                                            (cong fst q1)
                                                            (∈ₛmapPfin fst x v1 mx))))
                                ; (inj₂ mx) →
                                    ∈Pfin×p setC f g injg fa≡gb w
                                            (subst (λ z → ⟨ a ∈ₛ z ⟩)
                                                (cong fst (sym eqw))
                                                (inr (subst (λ z → ⟨ a ∈ₛ z ⟩)
                                                            (cong fst q2)
                                                            (∈ₛmapPfin fst x v2 mx)))) }))
                           (λ { x@(a , b , fa≡gb) mx → ∥rec∥ propTruncIsProp
                              (λ { (inj₁ ma) →
                                         inl (∈Pfin×p setC f g injg fa≡gb v1
                                                      (subst (λ z → ⟨ a ∈ₛ z ⟩) (cong fst (sym q1)) ma))
                                 ; (inj₂ ma) →
                                         inr (∈Pfin×p setC f g injg fa≡gb v2
                                                      (subst (λ z → ⟨ a ∈ₛ z ⟩) (cong fst (sym q2)) ma))}) 
                              (subst (λ z → ⟨ a ∈ₛ z ⟩) (cong fst eqw) (∈ₛmapPfin fst x w mx)) }))
                       _ _ } })
        (∪≡mapPfin g injg t _ _ eq)


Pfin×p : ∀{A B C} (setB : isSet B) (setC : isSet C)
  → (f : A → C) (g : B → C)
  → (∀ x y → g x ≡ g y → x ≡ y)
  → Pfin (f ×p g) ≃ (mapPfin f ×p mapPfin g)
Pfin×p setB setC f g injg =
  (to×p f g) ,
  (record { equiv-proof = λ { (s , t , eq)
    → to×pEquiv setB setC f g injg s t eq } })

×pℕ : {A : ℕ → Type} {C : Type}
  → (f : ∀ n → A n → C) → Type
×pℕ {A} f = Σ[ a ∈ ((n : ℕ) → A n) ] ∀ n → f (suc n) (a (suc n)) ≡ f 0 (a 0)

isSet×pℕ : {A : ℕ → Type} {C : Type}
  → (∀ n → isSet (A n)) → isSet C
  → (f : ∀ n → A n → C) → isSet (×pℕ f)
isSet×pℕ sA sC f = isSetΣ (isSetΠ sA) λ _ → isProp→isSet (isPropΠ (λ _ → sC _ _))

to×pℕ : {A : ℕ → Type}{C : Type} (f : ∀ n → A n → C) 
  → Pfin (×pℕ {A}{C} f) → ×pℕ {Pfin ∘ A}{Pfin C} (mapPfin ∘ f)
to×pℕ f s =
  (λ n → mapPfin (λ x → x .fst n) s) ,
  λ n →
     mapPfinComp s
     ∙ cong (λ z → mapPfin z s) (λ i x → x .snd n i)
     ∙ sym (mapPfinComp s)

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


Eq×pℕ : {A : ℕ → Type} {C : Type} → isSet C
  → (f : ∀ n → A n → C)
  → {a a' : ∀ n → A n} → (∀ n → a n ≡ a' n)
  → {eq : ∀ n → f (suc n) (a (suc n)) ≡ f 0 (a 0)}
  → {eq' : ∀ n → f (suc n) (a' (suc n)) ≡ f 0 (a' 0)}
  → _≡_ {A = ×pℕ f} (a , eq) (a' , eq')
Eq×pℕ setC f p =
  Σ≡Prop (λ a → isPropΠ (λ _ → setC _ _))
    λ i n → p n i

∈Pfin×pℕ : {A : ℕ → Type} {C : Type} → isSet C 
  → (f : ∀ n → A n → C)
  → (∀ n (x y : A (suc n)) → f (suc n) x ≡ f (suc n) y → x ≡ y)
  → {a : ∀ n → A n} (eq : ∀ n → f (suc n) (a (suc n)) ≡ f 0 (a 0)) (s : Pfin (×pℕ f))
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
  

{-
  module _ {A : ℕ → Type} {C : Type}
          (sA : ∀ n → isSet (A (suc n))) (sC : isSet C)
          (f0 : A 0 → C)
          (f : ∀ n → A (suc n) → C)
          (injf : ∀ n (x y : A (suc n)) → f n x ≡ f n y → x ≡ y) where

    from×pℕ :
         (a0 : Pfin (A 0))
      → (as : ∀ n → Pfin (A (suc n)))
      → (eq : ∀ n → mapPfin (f n) (as n) ≡ mapPfin f0 a0)
      → Pfin (×pℕ {A} (funs f0 f)) 
    from×pℕ a0 as eq = fst (fst (to×pℕEquiv sA sC f0 f injf a0 as eq))

    from×pℕ-ø :
         (as : ∀ n → Pfin (A (suc n)))
      → (eq : ∀ n → mapPfin (f n) (as n) ≡ ø)
      → from×pℕ ø as eq ≡ ø
    from×pℕ-ø as eq = refl

    from×pℕ-η : (a : A 0)
         (as : ∀ n → Pfin (A (suc n)))
      → (eq : ∀ n → mapPfin (f n) (as n) ≡ η (f0 a))
      → from×pℕ (η a) as eq ≡ η ((λ { zero → a ; (suc n) → mapPfinη (sA n) (f n) (injf n) (as n) (f0 a) (eq n) .fst }) , {!!})
    from×pℕ-η a as eq = cong η (Σ≡Prop {!!} (funExt (λ { zero → refl ; (suc n) → refl} )))      

    from×pℕ-∪ :
         (a0 b0 : Pfin (A 0))
      → (as : ∀ n → Pfin (A (suc n)))
      → (eq : ∀ n → mapPfin (f n) (as n) ≡ (mapPfin f0 a0 ∪ mapPfin f0 b0))
      → from×pℕ (a0 ∪ b0) as eq ≡ {!from×pℕ (a0 ∪ b0) as eq!}
-}
{-
  from×pℕ : {A : ℕ → Type}{C : Type} 
    → (setA : ∀ n → isSet (A (suc n))) (setC : isSet C)
    → (f : ∀ n → A n → C) 
    → (injf : ∀ n (x y : A (suc n)) → f (suc n) x ≡ f (suc n) y → x ≡ y)
    → ×pℕ {Pfin ∘ A}{Pfin C} (mapPfin ∘ f) → Pfin (×pℕ {A}{C} f)
  from×pℕ sA sC f injf x = {!equivFun (invEquiv (Pfin×pℕ sA sC f injf)) x!}
-}

{-
-- A simple counterexample showing that Pfin does not preserve
-- pullbacks.

module _ where

  data X : Type where
    a b c : X

  data Y : Type where
    a b : Y

  data Z : Type where
    a : Z

  f : X → Z
  f _ = a

  g : Y → Z
  g _ = a

  H : X × Y → f ×p g
  H (x , y) = x , y , refl

  mapH : Pfin (X × Y) → Pfin (f ×p g)
  mapH = mapPfin H

-- mapH is an isomorphism, but to×p is not surjective

  G : (x : mapPfin f ×p mapPfin g) → x .fst ≡ η a → x .snd .fst ≡ ø →  ⊥
  G x p q = ødisjη absurd
    where
      absurd : η a ≡ ø
      absurd =
        cong (mapPfin f) (sym p)
        ∙ x .snd .snd
        ∙ cong (mapPfin g) q
-}
