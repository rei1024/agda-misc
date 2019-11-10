{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Logic.Constructive where

-- agda-stdlib
open import Data.Empty
open import Data.Sum as Sum
open import Data.Product as Prod
open import Function.Base
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Relation.Unary as U
open import Relation.Binary.PropositionalEquality

-- agda-misc
open import Math.Logic.NonConstructiveAxiom

---------------------------------------------------------------------------
-- Combinators
---------------------------------------------------------------------------

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where
  →-distrib-⊎-× : ((A ⊎ B) → C) → (A → C) × (B → C)
  →-distrib-⊎-× f = f ∘ inj₁ , f ∘ inj₂

  →-undistrib-⊎-× : (A → C) × (B → C) → (A ⊎ B) → C
  →-undistrib-⊎-× (f , g) (inj₁ x) = f x
  →-undistrib-⊎-× (f , g) (inj₂ y) = g y

  →-undistrib-⊎-×-flip : (A ⊎ B) → (A → C) × (B → C) → C
  →-undistrib-⊎-×-flip = flip →-undistrib-⊎-×

  →-undistrib-×-⊎ : (A → C) ⊎ (B → C) → (A × B) → C
  →-undistrib-×-⊎ (inj₁ f) (x , y) = f x
  →-undistrib-×-⊎ (inj₂ g) (x , y) = g y

  →-undistrib-×-⊎-flip : (A × B) → (A → C) ⊎ (B → C) → C
  →-undistrib-×-⊎-flip = flip →-undistrib-×-⊎

-- sum and product
module _ {a b} {A : Set a} {B : Set b} where
  A⊎B→¬A→B : A ⊎ B → ¬ A → B
  A⊎B→¬A→B (inj₁ x) ¬A = ⊥-elim $ ¬A x
  A⊎B→¬A→B (inj₂ y) ¬A = y

  A⊎B→¬B→A : A ⊎ B → ¬ B → A
  A⊎B→¬B→A (inj₁ x) ¬B = x
  A⊎B→¬B→A (inj₂ y) ¬B = ⊥-elim $ ¬B y

  ¬A⊎B→A→B : ¬ A ⊎ B → A → B
  ¬A⊎B→A→B (inj₁ x) z = ⊥-elim (x z)
  ¬A⊎B→A→B (inj₂ y) z = y

  [A→B]→¬[A×¬B] : (A → B) → ¬ (A × ¬ B)
  [A→B]→¬[A×¬B] f (x , y) = y (f x)

  A×B→¬[A→¬B] : A × B → ¬ (A → ¬ B)
  A×B→¬[A→¬B] (x , y) f = f x y

  -- De Morgan's laws
  ¬[A⊎B]→¬A×¬B : ¬ (A ⊎ B) → ¬ A × ¬ B
  ¬[A⊎B]→¬A×¬B = →-distrib-⊎-×

  ¬A×¬B→¬[A⊎B] : ¬ A × ¬ B → ¬ (A ⊎ B)
  ¬A×¬B→¬[A⊎B] = →-undistrib-⊎-×

  A⊎B→¬[¬A×¬B] : A ⊎ B → ¬ (¬ A × ¬ B)
  A⊎B→¬[¬A×¬B] = →-undistrib-⊎-×-flip

  ¬A⊎¬B→¬[A×B] : ¬ A ⊎ ¬ B → ¬ (A × B)
  ¬A⊎¬B→¬[A×B] = →-undistrib-×-⊎

  A×B→¬[¬A⊎¬B] : A × B → ¬ (¬ A ⊎ ¬ B)
  A×B→¬[¬A⊎¬B] = →-undistrib-×-⊎-flip

  -- Double negated DEM₃
  ¬[A×B]→¬¬[¬A⊎¬B] : ¬ (A × B) → ¬ ¬ (¬ A ⊎ ¬ B)
  ¬[A×B]→¬¬[¬A⊎¬B] ¬[A×B] ¬[¬A⊎¬B] =
    ¬[¬A⊎¬B] (inj₁ λ x → ⊥-elim $ ¬[¬A⊎¬B] (inj₂ (λ y → ¬[A×B] (x , y))))

  em-i⇒¬[A×B]→¬A⊎¬B : EM-i A → EM-i B → ¬ (A × B) → ¬ A ⊎ ¬ B
  em-i⇒¬[A×B]→¬A⊎¬B (inj₁ x)  (inj₁ y)  ¬[A×B] = ⊥-elim $ ¬[A×B] (x , y)
  em-i⇒¬[A×B]→¬A⊎¬B (inj₁ x)  (inj₂ ¬y) ¬[A×B] = inj₂ ¬y
  em-i⇒¬[A×B]→¬A⊎¬B (inj₂ ¬x) emB       ¬[A×B] = inj₁ ¬x

  join : (A → A → B) → A → B
  join f x = f x x

module _ {a} {A : Set a} where
  [A→¬A]→¬A : (A → ¬ A) → ¬ A
  [A→¬A]→¬A = join

  -- Law of noncontradiction (LNC)
  ¬[A×¬A] : ¬ (A × ¬ A)
  ¬[A×¬A] = uncurry (flip _$_)

-- properties of negation
module _ {a b} {A : Set a} {B : Set b} where
  contraposition : (A → B) → ¬ B → ¬ A
  contraposition = flip _∘′_

  -- variant of contraposition
  [A→¬¬B]→¬B→¬A : (A → ¬ ¬ B) → ¬ B → ¬ A
  [A→¬¬B]→¬B→¬A f ¬B x = (f x) ¬B

  [A→¬B]→¬¬A→¬B : (A → ¬ B) → ¬ ¬ A → ¬ B
  [A→¬B]→¬¬A→¬B A→¬B ¬¬A y = ¬¬A λ x → A→¬B x y

module _ {a} {A : Set a} where
  -- introduction for double negation
  DN-intro : A → ¬ ¬ A
  DN-intro = flip _$_

  -- triple negation to negation
  TN-to-N : ¬ ¬ ¬ A → ¬ A
  TN-to-N = contraposition DN-intro

  -- Double negation of excluded middle
  DN-EM-i : ¬ ¬ EM-i A
  DN-EM-i = λ f → (f ∘ inj₂) (f ∘ inj₁)

-- eliminator for ⊥
⊥-stable : ¬ ¬ ⊥ → ⊥
⊥-stable f = f id

-- Double negation is monad
module _ {a} {A : Set a} where
  DN-join : ¬ ¬ ¬ ¬ A → ¬ ¬ A
  DN-join = TN-to-N

module _ {a b} {A : Set a} {B : Set b} where
  DN-map : (A → B) → ¬ ¬ A → ¬ ¬ B
  DN-map = contraposition ∘′ contraposition

module _ {a b} {A : Set a} {B : Set b} where
  DN-bind : (A → ¬ ¬ B) → ¬ ¬ A → ¬ ¬ B
  DN-bind f = DN-join ∘′ DN-map f

  DN-bind⁻¹ : (¬ ¬ A → ¬ ¬ B) → A → ¬ ¬ B
  DN-bind⁻¹ f = f ∘′ DN-intro

module _ {a b} {A : Set a} {B : Set b} where
  DN-ap : ¬ ¬ (A → B) → ¬ ¬ A → ¬ ¬ B
  DN-ap ff fx = DN-bind (λ f → DN-map f fx) ff

  DN-ap⁻¹ : (¬ ¬ A → ¬ ¬ B) → ¬ ¬ (A → B)
  DN-ap⁻¹ f ¬[A→B] = ¬[A→B] λ x → ⊥-elim $ f (DN-intro x) λ y → ¬[A→B] (const y)

  DN-distrib-× : ¬ ¬ (A × B) → ¬ ¬ A × ¬ ¬ B
  DN-distrib-× ¬¬A×B = DN-map proj₁ ¬¬A×B , DN-map proj₂ ¬¬A×B

  DN-undistrib-× : ¬ ¬ A × ¬ ¬ B → ¬ ¬ (A × B)
  DN-undistrib-× = [A→¬¬B]→¬B→¬A ¬[A×B]→¬¬[¬A⊎¬B] ∘′ ¬A×¬B→¬[A⊎B]

  DN-undistrib-⊎ : ¬ ¬ A ⊎ ¬ ¬ B → ¬ ¬ (A ⊎ B)
  DN-undistrib-⊎ (inj₁ ¬¬A) = DN-map inj₁ ¬¬A
  DN-undistrib-⊎ (inj₂ ¬¬B) = DN-map inj₂ ¬¬B

  stable-undistrib-× : Stable A × Stable B → Stable (A × B)
  stable-undistrib-× (A-stable , B-stable) ¬¬[A×B] =
    Prod.map A-stable B-stable $ DN-distrib-× ¬¬[A×B]

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where
  ip-⊎-DN : (A → (B ⊎ C)) → ¬ ¬ ((A → B) ⊎ (A → C))
  ip-⊎-DN f =
    DN-map Sum.[ (Sum.map const const ∘ f) , (λ ¬A → inj₁ λ x → ⊥-elim (¬A x)) ]
          DN-EM-i

DN-ip : ∀ {p q r} {P : Set p} {Q : Set q} {R : Q → Set r} →
        Q → (P → Σ Q R) → ¬ ¬ (Σ Q λ x → (P → R x))
DN-ip q f =
  DN-map Sum.[ (λ x → Prod.map₂ const (f x)) ,
               (λ ¬P → q , λ P → ⊥-elim $ ¬P P) ] DN-EM-i

-- Properties of EM-i
module _ {a} {A : Set a} where
  em-i⇒dec : EM-i A → Dec A
  em-i⇒dec (inj₁ x) = yes x
  em-i⇒dec (inj₂ y) = no y

  dec⇒em-i : Dec A → EM-i A
  dec⇒em-i (yes p) = inj₁ p
  dec⇒em-i (no ¬p) = inj₂ ¬p

  ¬-em-i : EM-i A → EM-i (¬ A)
  ¬-em-i (inj₁ x) = inj₂ (DN-intro x)
  ¬-em-i (inj₂ y) = inj₁ y

module _ {a b} {A : Set a} {B : Set b} where
  em-i-map : (A → B) → (B → A) → EM-i A → EM-i B
  em-i-map f g em-i = Sum.map f (contraposition g) em-i

  em-i-⊎ : EM-i A → EM-i B → EM-i (A ⊎ B)
  em-i-⊎ (inj₁ x)  _         = inj₁ (inj₁ x)
  em-i-⊎ (inj₂ ¬x) (inj₁ y)  = inj₁ (inj₂ y)
  em-i-⊎ (inj₂ ¬x) (inj₂ ¬y) = inj₂ (¬A×¬B→¬[A⊎B] (¬x , ¬y))

  em-i-× : EM-i A → EM-i B → EM-i (A × B)
  em-i-× (inj₁ x) (inj₁ y)  = inj₁ (x , y)
  em-i-× (inj₁ x) (inj₂ ¬y) = inj₂ (¬y ∘ proj₂)
  em-i-× (inj₂ ¬x) _        = inj₂ (¬x ∘ proj₁)

-- Properties of Stable
module _ {a} {A : Set a} where
  dec⇒stable : Dec A → Stable A
  dec⇒stable (yes p) ¬¬A = p
  dec⇒stable (no ¬p) ¬¬A = ⊥-elim (¬¬A ¬p)

  ¬-stable : Stable (¬ A)
  ¬-stable = TN-to-N

  em-i⇒stable : EM-i A → Stable A
  em-i⇒stable em-i = dec⇒stable (em-i⇒dec em-i)

module _ {a p} {A : Set a} {P : A → Set p} where
  DecU⇒stable : DecU P → ∀ x → Stable (P x)
  DecU⇒stable P? x = em-i⇒stable (P? x)

  -- Properties of DecU
  ¬-DecU : DecU P → DecU (λ x → ¬ (P x))
  ¬-DecU P? x = ¬-em-i (P? x)

  DecU⇒decidable : DecU P → U.Decidable P
  DecU⇒decidable P? x = em-i⇒dec (P? x)

  decidable⇒DecU : U.Decidable P → DecU P
  decidable⇒DecU P? x = dec⇒em-i (P? x)

DecU-map : ∀ {a b p} {A : Set a} {B : Set b} {P : A → Set p} →
  (f : B → A) → DecU P → DecU (λ x → P (f x))
DecU-map f P? x = em-i-map id id (P? (f x))

module _ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} where
  DecU-⊎ : DecU P → DecU Q → DecU (λ x → P x ⊎ Q x)
  DecU-⊎ P? Q? x = em-i-⊎ (P? x) (Q? x)

  DecU-× : DecU P → DecU Q → DecU (λ x → P x × Q x)
  DecU-× P? Q? x = em-i-× (P? x) (Q? x)

-- Quantifications
module _ {a p} {A : Set a} {P : A → Set p} where
  ∃P→¬∀¬P : ∃ P → ¬ (∀ x → ¬ (P x))
  ∃P→¬∀¬P = flip uncurry

  ∀P→¬∃¬P : (∀ x → P x) → ¬ ∃ λ x → ¬ (P x)
  ∀P→¬∃¬P f (x , ¬Px) = ¬Px (f x)

  ¬∃P→∀¬P : ¬ ∃ P → ∀ x → ¬ (P x)
  ¬∃P→∀¬P = curry

  ∀¬P→¬∃P : (∀ x → ¬ (P x)) → ¬ ∃ P
  ∀¬P→¬∃P = uncurry

  ∃¬P→¬∀P : ∃ (λ x → ¬ (P x)) → ¬ (∀ x → P x)
  ∃¬P→¬∀P (x , ¬Px) ∀P = ¬Px (∀P x)

  ¬∀¬P→¬¬∃P : ¬ (∀ x → ¬ P x) → ¬ ¬ ∃ P
  ¬∀¬P→¬¬∃P ¬∀¬P = contraposition ¬∃P→∀¬P ¬∀¬P

  ¬¬∃P→¬∀¬P : ¬ ¬ ∃ P → ¬ (∀ x → ¬ P x)
  ¬¬∃P→¬∀¬P ¬¬∃P = contraposition ∀¬P→¬∃P ¬¬∃P

  ¬¬∀P→¬∃¬P : ¬ ¬ (∀ x → P x) → ¬ ∃ λ x → ¬ (P x)
  ¬¬∀P→¬∃¬P ¬¬∀P = contraposition ∃¬P→¬∀P ¬¬∀P

  ¬¬∃P<=>¬∀¬P : ¬ ¬ ∃ P <=> ¬ (∀ x → ¬ P x)
  ¬¬∃P<=>¬∀¬P = mk<=> ¬¬∃P→¬∀¬P ¬∀¬P→¬¬∃P

  ∀¬¬P→¬∃¬P : (∀ x → ¬ ¬ P x) → ¬ ∃ λ x → ¬ (P x)
  ∀¬¬P→¬∃¬P = uncurry

  -- converse of DNS
  ¬¬∀P→∀¬¬P : ¬ ¬ (∀ x → P x) → ∀ x → ¬ ¬ P x
  ¬¬∀P→∀¬¬P f x = DN-map (λ ∀P → ∀P x) f

  ∃¬¬P→¬¬∃P  : (∃ λ x → ¬ ¬ P x) → ¬ ¬ ∃ λ x → P x
  ∃¬¬P→¬¬∃P (x , ¬¬Px) = DN-map (λ Px → x , Px) ¬¬Px

  ¬¬∃¬P→¬∀P : ¬ ¬ ∃ (λ x → ¬ (P x)) → ¬ (∀ x → P x)
  ¬¬∃¬P→¬∀P = contraposition ∀P→¬∃¬P

  ¬∃¬P→∀¬¬P : ¬ ∃ (λ x → ¬ P x) → ∀ x → ¬ ¬ P x
  ¬∃¬P→∀¬¬P = curry

  ∀P→∀¬¬P : (∀ x → P x) → ∀ x → ¬ ¬ P x
  ∀P→∀¬¬P ∀P x = DN-intro (∀P x)

module _ {a p} {A : Set a} {P : A → Set p} where
  P-stable⇒∃¬¬P→∃P : (∀ x → Stable (P x)) → ∃ (λ x → ¬ ¬ P x) → ∃ P
  P-stable⇒∃¬¬P→∃P P-stable (x , ¬¬Px) = x , P-stable x ¬¬Px

  P-stable⇒∀¬¬P→∀P : (∀ x → Stable (P x)) → (∀ x → ¬ ¬ P x) → ∀ x → P x
  P-stable⇒∀¬¬P→∀P P-stable ∀¬¬P x = P-stable x (∀¬¬P x)

  P-stable⇒¬¬∀P→∀P : (∀ x → Stable (P x)) → ¬ ¬ (∀ x → P x) → ∀ x → P x
  P-stable⇒¬¬∀P→∀P P-stable = P-stable⇒∀¬¬P→∀P P-stable ∘′ ¬¬∀P→∀¬¬P

  P-stable⇒¬∃¬P→∀P : (∀ x → Stable (P x)) → ¬ ∃ (λ x → ¬ P x) → ∀ x → P x
  P-stable⇒¬∃¬P→∀P P-stable ¬∃¬P = P-stable⇒∀¬¬P→∀P P-stable (¬∃¬P→∀¬¬P ¬∃¬P)

  P-stable⇒¬∀P→¬¬∃¬P : (∀ x → Stable (P x)) → ¬ (∀ x → P x) → ¬ ¬ ∃ (λ x → ¬ (P x))
  P-stable⇒¬∀P→¬¬∃¬P P-stable ¬∀P = contraposition (P-stable⇒¬∃¬P→∀P P-stable) ¬∀P

  -- decidable predicate
  P?⇒∃¬¬P→∃P : DecU P → ∃ (λ x → ¬ ¬ P x) → ∃ P
  P?⇒∃¬¬P→∃P P? = P-stable⇒∃¬¬P→∃P (DecU⇒stable P?)

  P?⇒∀¬¬P→∀P : DecU P → (∀ x → ¬ ¬ P x) → ∀ x → P x
  P?⇒∀¬¬P→∀P P? = P-stable⇒∀¬¬P→∀P (DecU⇒stable P?)

  P?⇒¬¬∀P→∀P : DecU P → ¬ ¬ (∀ x → P x) → ∀ x → P x
  P?⇒¬¬∀P→∀P P? = P-stable⇒¬¬∀P→∀P (DecU⇒stable P?)

  P?⇒¬∃¬P→∀P : DecU P → ¬ ∃ (λ x → ¬ P x) → ∀ x → P x
  P?⇒¬∃¬P→∀P P? = P-stable⇒¬∃¬P→∀P (DecU⇒stable P?)

  P?⇒¬∀P→¬¬∃¬P : DecU P → ¬ (∀ x → P x) → ¬ ¬ ∃ (λ x → ¬ P x)
  P?⇒¬∀P→¬¬∃¬P P? = P-stable⇒¬∀P→¬¬∃¬P (DecU⇒stable P?)

module _ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} where
  ∃-undistrib-⊎ : ∃ P ⊎ ∃ Q → ∃ (λ x → P x ⊎ Q x)
  ∃-undistrib-⊎ (inj₁ (x , Px)) = x , inj₁ Px
  ∃-undistrib-⊎ (inj₂ (x , Qx)) = x , inj₂ Qx

  ∃-distrib-⊎ : ∃ (λ x → P x ⊎ Q x) → ∃ P ⊎ ∃ Q
  ∃-distrib-⊎ (x , inj₁ Px) = inj₁ (x , Px)
  ∃-distrib-⊎ (x , inj₂ Qx) = inj₂ (x , Qx)

  ∃-distrib-× : ∃ (λ x → P x × Q x) → ∃ P × ∃ Q
  ∃-distrib-× (x , Px , Qx) = (x , Px) , (x , Qx)

  ∀-undistrib-× : (∀ x → P x) × (∀ x → Q x) → ∀ x → P x × Q x
  ∀-undistrib-× (∀P , ∀Q) x = ∀P x , ∀Q x

  ∀-distrib-× : (∀ x → P x × Q x) → (∀ x → P x) × (∀ x → Q x)
  ∀-distrib-× ∀x→Px×Qx = proj₁ ∘ ∀x→Px×Qx , proj₂ ∘ ∀x→Px×Qx

  ∀-undistrib-⊎ : (∀ x → P x) ⊎ (∀ x → Q x) → ∀ x → P x ⊎ Q x
  ∀-undistrib-⊎ (inj₁ ∀P) x = inj₁ (∀P x)
  ∀-undistrib-⊎ (inj₂ ∀Q) x = inj₂ (∀Q x)

  ¬[¬∃P×¬∃Q]→¬¬∃x→Px⊎Qx : ¬ (¬ ∃ P × ¬ ∃ Q) → ¬ ¬ ∃ λ x → P x ⊎ Q x
  ¬[¬∃P×¬∃Q]→¬¬∃x→Px⊎Qx = DN-map ∃-undistrib-⊎ ∘′ contraposition ¬[A⊎B]→¬A×¬B

  [¬¬∃x→Px⊎Qx]→¬[¬∃P×¬∃Q] : (¬ ¬ ∃ λ x → P x ⊎ Q x) → ¬ (¬ ∃ P × ¬ ∃ Q)
  [¬¬∃x→Px⊎Qx]→¬[¬∃P×¬∃Q] = contraposition ¬A×¬B→¬[A⊎B] ∘′ DN-map ∃-distrib-⊎

  ¬∀¬P×¬∀¬Q→¬¬[∃P×∃Q] : ¬ (∀ x → ¬ P x) × ¬ (∀ x → ¬ Q x) → ¬ ¬ (∃ P × ∃ Q)
  ¬∀¬P×¬∀¬Q→¬¬[∃P×∃Q] = DN-undistrib-× ∘′ Prod.map ¬∀¬P→¬¬∃P ¬∀¬P→¬¬∃P

  ¬¬[∃P×∃Q]→¬∀¬P×¬∀¬Q : ¬ ¬ (∃ P × ∃ Q) → ¬ (∀ x → ¬ P x) × ¬ (∀ x → ¬ Q x)
  ¬¬[∃P×∃Q]→¬∀¬P×¬∀¬Q = Prod.map ¬¬∃P→¬∀¬P ¬¬∃P→¬∀¬P ∘′ DN-distrib-×

  [∀x→Px→Qx]→∀P→∀Q : (∀ x → P x → Q x) → (∀ x → P x) → ∀ x → Q x
  [∀x→Px→Qx]→∀P→∀Q f g x = f x (g x)
