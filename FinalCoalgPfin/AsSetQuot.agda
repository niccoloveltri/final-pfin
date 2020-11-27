{-# OPTIONS --cubical --no-import-sorts #-}

module FinalCoalgPfin.AsSetQuot where

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
open import ListRelations
open import Trees
open import Pfin.AsSetQuot
open import FinalCoalgPfin.AsSetoid
open BinaryRelation

-- the final coalgebra of PfinQ as quotient of trees
νPfinQ : Type
νPfinQ = Tree ∞ / ExtEq ∞

-- νPfinQ is a coalgebra for the functor PfinQ
ξRel : ∀ ts ts' → DRelator (ExtEq ∞) ts ts'
  → DRelator _≡_ (mapList {B = νPfinQ} [_] ts) (mapList [_] ts')
ξRel ts ts' p c mc with pre∈mapList mc
... | (t , mt , eq) =
  ∥map∥ (λ { (u , mu , r) → _ , ∈mapList mu , sym eq ∙ eq/ _ _ r}) (p t mt)

ξ : νPfinQ → PfinQ νPfinQ
ξ = recQ squash/ (λ t → [ mapList [_] (force t) ])
  λ t t' p → eq/ _ _ (ξRel _ _ (forceExt p .fst) , ξRel _ _ (forceExt p .snd))

-- two quotients of function spaces
[_⇒PfinQ_] : (A B : Type) → Type
[ A ⇒PfinQ B ] = [ A ⇒ (List B) ]/ SameEls

[_⇒νPfinQ] : (A : Type) → Type
[ A ⇒νPfinQ] = [ A ⇒ Tree ∞ ]/ ExtEq ∞

-- towards the construction of the anamorphism: there exists a map
-- from X to νPfinQ, provided that X comes with a "coalgebra"
-- c : [ X ⇒PfinQ X ]

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

-- the construction of the anamorphism;
-- for this to work, we assume that θ has a section, i.e. it is a
-- split epimorphism; this is equivalent to full axiom of choice (the
-- equivalence is proved in the end of the file Preliminaries.agda)

module _ (θInv : ∀ A {B} (R : B → B → Type) → (A → B / R) → [ A ⇒ B ]/ R)
         (sectionθ : ∀ A {B} (R : B → B → Type) → section (θ A R) (θInv A R)) where

  θ1 : ∀{X} → [ X ⇒PfinQ X ] → X → PfinQ X
  θ1 = θ _ _

  θ1Inv : ∀ {X} → (X → PfinQ X) → [ X ⇒PfinQ X ]
  θ1Inv = θInv _ _

  sectionθ1 : ∀{X} (f : X → PfinQ X) → θ1 (θ1Inv f) ≡ f
  sectionθ1 = sectionθ _ _

  θ2 : ∀{X} → [ X ⇒νPfinQ] → X → νPfinQ
  θ2 = θ _ _

  θ2Inv : ∀ {X} → (X → νPfinQ) → [ X ⇒νPfinQ]
  θ2Inv = θInv _ _ 

  sectionθ2 : ∀{X} (f : X → νPfinQ) → θ2 (θ2Inv f) ≡ f
  sectionθ2 = sectionθ _ _

  anaPfinQ : {X : Type} (c : X → PfinQ X)
    → X → νPfinQ
  anaPfinQ c = anaPfinQ' (θ1Inv c)


-- the anamorphism is a coalgebra morphism
  anaPfinQEq' : {X : Type} (c : [ X ⇒PfinQ X ])
    → ∀ x → ξ (anaPfinQ' c x) ≡ mapPfinQ (anaPfinQ' c) (θ1 c x)
  anaPfinQEq' =
    elimProp (λ _ → isPropΠ (λ _ → squash/ _ _))
      (λ c x → cong [_] (mapListComp (c x)))

  anaPfinQEq : {X : Type} (c : X → PfinQ X)
    → ∀ x → ξ (anaPfinQ c x) ≡ mapPfinQ (anaPfinQ c) (c x)
  anaPfinQEq c x =
    anaPfinQEq' (θ1Inv c) x ∙ cong (λ f → mapPfinQ (anaPfinQ c) (f x)) (sectionθ1 c)

-- uniqueness
  anaPfinQUniq'' : {X : Type} (Xset : isSet X) (c : X → List X)
    → (f : [ X ⇒νPfinQ]) (feq : ∀ x → ξ (θ2 f x) ≡ mapPfinQ (θ2 f) [ c x ])
    → ∀ x → θ2 f x ≡ anaPfinQ' [ c ] x
  anaPfinQUniq'' Xset c =
    elimProp (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → squash/ _ _)))
      (λ f feq x → eq/ _ _
        (anaPfinUniq' (Set→Setoid (_ , Xset))
                      (c , λ eq → subst (λ z → Relator _≡_ (c _) (c z)) eq (reflRelator (λ _ → refl) _))
                      (f , λ eq → subst (λ z → ExtEq ∞ (f _) (f z)) eq (reflExtEq ∞ _))
                      (λ y →
                        (λ t mt →
                          ∥rec∥ propTruncIsProp (uncurry (elimProp (λ _ → isPropΠ λ _ → propTruncIsProp)
                              λ { t' (mt' , eq') → ∣ _ , ∈mapList (pre∈mapList mt' .snd .fst) ,
                                  effective isPropExtEq isEquivRelExtEq _ _ (eq' ∙ sym (pre∈mapList mt' .snd .snd)) ∣ } ))
                            (effective isPropSameEls isEquivRelSameEls _ _ (feq y) .fst [ t ] (∈mapList mt))) ,
                        (λ t mt → ∥rec∥ propTruncIsProp (uncurry (elimProp (λ _ → isPropΠ λ _ → propTruncIsProp)
                              λ {t' (mt' , eq') → ∣ _ , pre∈mapList mt' .snd .fst ,
                                  effective isPropExtEq isEquivRelExtEq  _ _ (eq' ∙ sym (pre∈mapList mt' .snd .snd)) ∣ }))
                          (effective isPropSameEls isEquivRelSameEls _ _ (feq y) .snd [ t ] (subst ([ t ] ∈_) (mapListComp (c y)) (∈mapList mt)))))
                      ∞
                      x))


  anaPfinQUniq' : {X : Type} (Xset : isSet X) (c : [ X ⇒PfinQ X ])
    → (f : X → νPfinQ) (feq : ∀ x → ξ (f x) ≡ mapPfinQ f (θ1 c x))
    → ∀ x → f x ≡ anaPfinQ' c x
  anaPfinQUniq' Xset =
    elimProp
      (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → squash/ _ _))))
      (λ c f feq x → (λ i → sym (sectionθ2 f) i x)
                      ∙ anaPfinQUniq'' Xset c (θ2Inv f)
                          (λ y → (λ i → ξ (sectionθ2 f i y) )
                                  ∙ feq y
                                  ∙ cong (λ g → [ mapList g (c y) ]) (sym (sectionθ2 f)))
                          x)
      
  anaPfinQUniq : {X : Type} (Xset : isSet X) (c : X → PfinQ X)
    → (f : X → νPfinQ) (feq : ∀ x → ξ (f x) ≡ mapPfinQ f (c x))
    → ∀ x → f x ≡ anaPfinQ c x
  anaPfinQUniq Xset c f feq x =
    anaPfinQUniq' Xset (θ1Inv c) f
      (λ y → feq y ∙ λ i → mapPfinQ f (sectionθ1 c (~ i) y))
      x
    

  
