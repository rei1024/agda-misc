{-# OPTIONS --without-K --safe #-}

module Math.FormalLanguage where

-- agda-stdlib
import Algebra.FunctionProperties as FP
import Algebra.Structures as Structures
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List as L using (List; []; _++_)
import Data.List.Properties as Lₚ
open import Data.Nat hiding (_⊔_; _^_)
open import Data.Empty
open import Data.Product using (proj₁; proj₂; _,_; _×_; ∃₂; ∃)
open import Function using (_$_)
import Function as F
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Unary hiding (∅; ｛_｝)
import Relation.Unary as U
import Relation.Unary.Properties as Uₚ

-- Equivalence of predicate
infix 4 _≡ᴾ_
_≡ᴾ_ : ∀ {a l} {A : Set a} → Rel (Pred A l) (a ⊔ l)
_≡ᴾ_ P Q = (P ⊆ Q) × (Q ⊆ P)

≡ᴾ-refl : ∀ {a l} {A : Set a} → Reflexive {A = Pred A l} _≡ᴾ_
≡ᴾ-refl = F.id , F.id

≡ᴾ-sym : ∀ {a l} {A : Set a} → Symmetric {A = Pred A l} _≡ᴾ_
≡ᴾ-sym = Data.Product.swap

≡ᴾ-trans : ∀ {a l} {A : Set a} → Transitive {A = Pred A l} _≡ᴾ_
≡ᴾ-trans P≡Q Q≡R = proj₁ Q≡R F.∘ proj₁ P≡Q , proj₂ P≡Q F.∘ proj₂ Q≡R

≡ᴾ-isEquivalence : ∀ {a l} {A : Set a} → IsEquivalence {A = Pred A l} _≡ᴾ_
≡ᴾ-isEquivalence = record
  { refl  = ≡ᴾ-refl
  ; sym   = ≡ᴾ-sym
  ; trans = ≡ᴾ-trans
  }

≡ᴾ-setoid : ∀ {a l} {A : Set a} → Setoid _ _
≡ᴾ-setoid {a} {l} {A} = record
  { Carrier       = Pred A l
  ; _≈_           = _≡ᴾ_
  ; isEquivalence = ≡ᴾ-isEquivalence
  }

∅ : ∀ {a l} {A : Set a} → Pred A l
∅ {l = l} = λ _ → Lift l ⊥

｛_｝ : ∀ {a l} {A : Set a} → A → Pred A (a ⊔ l)
｛_｝{l = l} x = λ y → Lift l (y ≡ x)

Lang : ∀ {s} → Set s → (l : Level) → Set _
Lang Σ l = Pred (List Σ) l

-- TODO Move Math.FormalLanguage.Construct.EmptyLang
data EmptyLang {a l} {A : Set a} : Lang A (a ⊔ l) where
  mkEmptyLang : EmptyLang []

-- TODO Move Math.FormalLanguage.Construct.Concat
-- TODO Hetero
-- Lang A l → Lang B l → Lang (A ⊎ B) l
-- map inj₁ xs ++ map inj₂ ys
-- concatenation of formal language
data _<>_ {a l} {A : Set a} (L₁ L₂ : Lang A l) : Lang A (a ⊔ l) where
  mk<> : ∀ {xs ys} → L₁ xs → L₂ ys → (L₁ <> L₂) (xs ++ ys)

-- TODO Move Math.FormalLanguage.Construct.Concat.Properties
module _ {s l} {Σ : Set s} where
  open FP {A = Lang Σ (s ⊔ l)} _≡ᴾ_

  <>-identityˡ : LeftIdentity (EmptyLang {l = l}) _<>_
  <>-identityˡ L = to , from
    where
    to : EmptyLang <> L ⊆ L
    to (mk<> mkEmptyLang x₁) = x₁
    from : L ⊆ EmptyLang <> L
    from Lx = mk<> mkEmptyLang Lx

  <>-identityʳ  : RightIdentity (EmptyLang {l = l}) _<>_
  <>-identityʳ L = to , from
    where
    to : L <> EmptyLang ⊆ L
    to (mk<> Lx mkEmptyLang) = subst L (sym $ Lₚ.++-identityʳ _) Lx
    from : L ⊆ L <> EmptyLang
    from {xs} x = subst (L <> EmptyLang) (Lₚ.++-identityʳ xs) $
      mk<> {xs = xs} {ys = []} x mkEmptyLang

{- TODO move contents of agda-combinatorics to agda-misc
  <>-dec : ∀ {L₁ L₂ : Lang Σ l} →
    U.Decidable L₁ → U.Decidable L₂ → U.Decidable (L₁ <> L₂)
  <>-dec L₁? L₂? zs with L.filter (L₁? Uₚ.×? L₂?) (splits₂ zs)
  ... | x = ?
-}
