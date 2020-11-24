{-# OPTIONS --cubical --no-import-sorts #-}

module FinalPfinAsSetQuot where

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
open import Cubical.Relation.Binary
open import Preliminaries
open import Trees
open import PfinAsQuot
open import FinalPfinAsSetoid

νPfinQ : Type
νPfinQ = Tree ∞ / ExtEq ∞

SameEls→RelatorExtEq : {xs ys : List (Tree ∞)}
  → SameEls xs ys → Relator (ExtEq ∞) xs ys
SameEls→RelatorExtEq (p , q) =
  (λ x mx →
    ∥map∥ (λ {(y , my , eq) → y , my , subst (ExtEq ∞ x) eq (reflExtEq ∞ x) }) (p x mx)) ,
  (λ x mx →
    ∥map∥ (λ {(y , my , eq) → y , my , subst (ExtEq ∞ x) eq (reflExtEq ∞ x) }) (q x mx))


ξRel : ∀ ts ts' → DRelator (ExtEq ∞) ts ts'
  → DRelator _≡_ (mapList {B = νPfinQ} [_] ts) (mapList [_] ts')
ξRel ts ts' p c mc with pre∈mapList mc
... | (t , mt , eq) =
  ∥map∥ (λ { (u , mu , r) → _ , ∈mapList mu , sym eq ∙ eq/ _ _ r}) (p t mt)

ξ : νPfinQ → PfinQ νPfinQ
ξ = recQ squash/ (λ t → [ mapList [_] (force t) ])
  λ t t' p → eq/ _ _ (ξRel _ _ (forceExt p .fst) , ξRel _ _ (forceExt p .snd))

PW : {X A B : Type} (R : A → B → Type) → (X → A) → (X → B) → Type
PW R f g = ∀ x → R (f x) (g x)

[_⇒_]/_ : (A B : Type) (R : B → B → Type) → Type
[ A ⇒ B ]/ R = (A → B) / PW R

[_⇒PfinQ_] : (A B : Type) → Type
[ A ⇒PfinQ B ] = [ A ⇒ (List B) ]/ SameEls

[_⇒νPfinQ] : (A : Type) → Type
[ A ⇒νPfinQ] = [ A ⇒ Tree ∞ ]/ ExtEq ∞

anaTreeRelCoalg : ∀{X}(c c' : X → List X)
  → (∀ x → SameEls (c x) (c' x)) → (j : Size) (x : X)
  → ExtEq j (anaTree c ∞ x) (anaTree c' ∞ x)
anaTreeRelCoalg' : ∀{X}(c c' : X → List X)
  → (∀ x → SameEls (c x) (c' x)) → (j : Size) (x : X)
  → DRelator (ExtEq j) (mapList (anaTree c ∞) (c x))
                        (mapList (anaTree c' ∞) (c' x))

forceExt (anaTreeRelCoalg c c' rc j x) {k} =
  anaTreeRelCoalg' c c' rc k x ,
  anaTreeRelCoalg' c' c (λ z → symRelator (rc z)) k x

anaTreeRelCoalg' c c' rc j x t mt with pre∈mapList mt
... | y , my , eq = 
  ∥map∥
    (λ { (z , mz , eqz) →
      _ , ∈mapList mz ,
      subst (λ a → ExtEq j a (anaTree c' ∞ z)) eq
        (subst (λ a → ExtEq j (anaTree c ∞ y) (anaTree c' ∞ a)) eqz
          (anaTreeRelCoalg c c' rc j y)) } )
    (rc x .fst y my)

anaPfinQ' : {X : Type} (c : [ X ⇒PfinQ X ])
  → X → νPfinQ
anaPfinQ' =
  recQ (isSetΠ (λ _ → squash/)) (λ c x → [ anaTree c ∞ x ])
    λ c c' rc → funExt (λ x → eq/ _ _ (anaTreeRelCoalg c c' rc ∞ x)) 

θ : ∀ A {B} (R : B → B → Type) → [ A ⇒ B ]/ R → A → B / R
θ A R = recQ (isSetΠ (λ _ → squash/)) (λ c x → [ c x ])
  λ c c' r → funExt (λ x → eq/ _ _ (r x))

-- we assume that θ is an isomorphism, which is equivalent to full
-- axiom of choice

module _ (ac : ∀ A {B} (R : B → B → Type) → isIso (θ A R)) where

  θ1 : ∀{X} → [ X ⇒PfinQ X ] → X → PfinQ X
  θ1 = θ _ _

  θ1Inv : ∀ {X} → (X → PfinQ X) → [ X ⇒PfinQ X ]
  θ1Inv = ac _ _ .fst

  θ1θ1Inv : ∀{X} (f : X → PfinQ X) → θ1 (θ1Inv f) ≡ f
  θ1θ1Inv = ac _ _ .snd .fst

  θ1Invθ1 : ∀{X} (f : [ X ⇒PfinQ X ]) → θ1Inv (θ1 f) ≡ f
  θ1Invθ1 = ac _ _ .snd .snd

  θ2 : ∀{X} → [ X ⇒νPfinQ] → X → νPfinQ
  θ2 = θ _ _

  θ2Inv : ∀ {X} → (X → νPfinQ) → [ X ⇒νPfinQ]
  θ2Inv = ac _ _ .fst

  θ2θ2Inv : ∀{X} (f : X → νPfinQ) → θ2 (θ2Inv f) ≡ f
  θ2θ2Inv = ac _ _ .snd .fst

  θ2Invθ2 : ∀{X} (f : [ X ⇒νPfinQ]) → θ2Inv (θ2 f) ≡ f
  θ2Invθ2 = ac _ _ .snd .snd

  anaPfinQ : {X : Type} (c : X → PfinQ X)
    → X → νPfinQ
  anaPfinQ c = anaPfinQ' (θ1Inv c)

  anaPfinQEq' : {X : Type} (c : [ X ⇒PfinQ X ])
    → ∀ x → ξ (anaPfinQ' c x) ≡ mapPfinQ (anaPfinQ' c) (θ1 c x)
  anaPfinQEq' =
    elimProp (λ _ → isPropΠ (λ _ → squash/ _ _))
      (λ c x → cong [_] (mapListComp (c x)))

  anaPfinQEq : {X : Type} (c : X → PfinQ X)
    → ∀ x → ξ (anaPfinQ c x) ≡ mapPfinQ (anaPfinQ c) (c x)
  anaPfinQEq c x =
    anaPfinQEq' (θ1Inv c) x ∙ cong (λ f → mapPfinQ (anaPfinQ c) (f x)) (θ1θ1Inv c)

  anaPfinQUniq'' : {X : Type} (Xset : isSet X) (c : X → List X)
    → (f : [ X ⇒νPfinQ]) (feq : ∀ x → ξ (θ2 f x) ≡ mapPfinQ (θ2 f) [ c x ])
    → ∀ x → θ2 f x ≡ anaPfinQ' [ c ] x
  anaPfinQUniq'' Xset c =
    elimProp {!!}
      (λ f feq x → eq/ _ _
        (anaPfinUniq' (Set→Setoid (_ , Xset))
                      (c , λ eq → subst (λ z → Relator _≡_ (c _) (c z)) eq (reflRelator (λ _ → refl) _))
                      (f , λ eq → subst (λ z → ExtEq ∞ (f _) (f z)) eq (reflExtEq ∞ _))
                      (λ y →
                        (λ t mt →
                          ∥rec∥ propTruncIsProp (uncurry (elimProp (λ _ → isPropΠ λ _ → propTruncIsProp)
                              λ { t' (mt' , eq') → ∣ _ , ∈mapList (pre∈mapList mt' .snd .fst) ,
                                  transExtEq ∞ (effective isPropExtEq isEquivRelExtEq _ _ eq')
                                               (symExtEq ∞ (effective isPropExtEq isEquivRelExtEq _ _ (pre∈mapList mt' .snd .snd))) ∣ } ))
                            (effective {!isPropSameEls!} {!!} _ _ (feq y) .fst [ t ] (∈mapList mt))) ,
                        (λ t mt → {!!}))
                      ∞
                      x))


  anaPfinQUniq' : {X : Type} (c : [ X ⇒PfinQ X ])
    → (f : X → νPfinQ) (feq : ∀ x → ξ (f x) ≡ mapPfinQ f (θ1 c x))
    → ∀ x → f x ≡ anaPfinQ' c x
  anaPfinQUniq' =
    elimProp
      (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → squash/ _ _))))
      (λ c → {!!})
      
  anaPfinQUniq : {X : Type} (c : X → PfinQ X)
    → (f : X → νPfinQ) (feq : ∀ x → ξ (f x) ≡ mapPfinQ f (c x))
    → ∀ x → f x ≡ anaPfinQ c x
  anaPfinQUniq c = {!!}

  