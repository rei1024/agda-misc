{-# OPTIONS --without-K --safe #-}

module Experiment.ListRelationProperties where

open import Level

open import Data.Bool hiding (_≤_; _≤?_; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
import Data.List.Properties as Listₚ
import      Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product hiding (swap)

import      Data.List.Relation.Binary.Equality.Setoid as ListSetoidEquality
import Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
import Data.List.Relation.Binary.Permutation.Setoid.Properties
  as PermutationSetoidProperties
open import Data.List.Relation.Unary.All as All
import      Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Linked
import      Data.List.Relation.Unary.Linked.Properties as Linkedₚ
open import Data.List.Relation.Unary.AllPairs as AllPairs
import      Data.List.Relation.Unary.AllPairs.Properties as AllPairsₚ
open import Data.List.Membership.Propositional

open import Function.Base using (_∘_; _$_; flip)

open import Relation.Binary as B
import      Relation.Binary.Properties.DecTotalOrder as DecTotalOrderProperties
open import Relation.Binary.PropositionalEquality using (_≡_)
import      Relation.Binary.PropositionalEquality as ≡ hiding ([_])
import      Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary
open import Relation.Unary as U hiding (_∈_)

-- stdlib
foldr-preservesʳ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} {f : A → B → B}
  → (∀ x {y} → P y → P (f x y))
  → ∀ {e} → P e → ∀ xs → P (foldr f e xs)
foldr-preservesʳ pres Pe []       = Pe
foldr-preservesʳ pres Pe (x ∷ xs) = pres _ (foldr-preservesʳ pres Pe xs)

-- stdlib
module _ {a p q} {A : Set a} {P : U.Pred A p} {Q : U.Pred A q} where
  All-mapWith∈ : ∀ {xs : List A} → (∀ {x} → x ∈ xs → P x → Q x) → All P xs → All Q xs
  All-mapWith∈          f []         = []
  All-mapWith∈ {x ∷ xs} f (px ∷ pxs) =
    f (here ≡.refl) px ∷ All-mapWith∈ (λ x∈xs Px → f (there x∈xs) Px) pxs

module _ {a p} {A : Set a} {P : U.Pred A p} where
  All-singleton⁺ : ∀ {x} → P x → All P [ x ]
  All-singleton⁺ px = px ∷ []

  All-reverse⁺ : ∀ {xs} → All P xs → All P (reverse xs)
  All-reverse⁺ {[]}     []         = []
  All-reverse⁺ {x ∷ xs} (px ∷ pxs) =
    ≡.subst (All P) (≡.sym $ Listₚ.unfold-reverse x xs)
            (Allₚ.++⁺ (All-reverse⁺ pxs) (All-singleton⁺ px))

module _ {a r} {A : Set a} {R : Rel A r} where

  -- AllPairs-map⁻
  -- AllPairs-mapMaybe⁺ : (∀ x y → R x y → R (f x) (f y)) → AllPairs R xs → AllPairs R (mapMaybe f xs)
  -- AllPairs mapMaybe⁻

  AllPairs-singleton⁺ : ∀ x → AllPairs R [ x ]
  AllPairs-singleton⁺ x = [] ∷ []

  AllPairs-pair : ∀ {x y} → R x y → AllPairs R (x ∷ y ∷ [])
  AllPairs-pair Rxy = All-singleton⁺ Rxy ∷ AllPairs-singleton⁺ _

  AllPairs-++⁻ʳ : ∀ xs {ys} → AllPairs R (xs ++ ys) → AllPairs R ys
  AllPairs-++⁻ʳ []       rxs        = rxs
  AllPairs-++⁻ʳ (x ∷ xs) (rx ∷ rxs) = AllPairs-++⁻ʳ xs rxs

  AllPairs-++⁻ˡ : ∀ xs {ys} → AllPairs R (xs ++ ys) → AllPairs R xs
  AllPairs-++⁻ˡ []       rxs        = []
  AllPairs-++⁻ˡ (x ∷ xs) (rx ∷ rxs) = Allₚ.++⁻ˡ xs rx ∷ AllPairs-++⁻ˡ xs rxs

  AllPairs-++⁻-AllAll : ∀ xs {ys} →
    AllPairs R (xs ++ ys) → All (λ x → All (R x) ys) xs
  AllPairs-++⁻-AllAll []       rxs        = []
  AllPairs-++⁻-AllAll (x ∷ xs) (rx ∷ rxs) = Allₚ.++⁻ʳ _ rx ∷ AllPairs-++⁻-AllAll xs rxs

  AllPairs-++⁻ : ∀ xs {ys} → AllPairs R (xs ++ ys) →
                 AllPairs R xs × AllPairs R ys × All (λ x → All (R x) ys) xs
  AllPairs-++⁻ xs rxs = AllPairs-++⁻ˡ xs rxs , AllPairs-++⁻ʳ xs rxs , AllPairs-++⁻-AllAll xs rxs

  AllPairs-∷ʳ⁺ : ∀ {x xs} → AllPairs R xs → All (flip R x) xs → AllPairs R (xs ∷ʳ x)
  AllPairs-∷ʳ⁺ {x} {xs} rxs px =
    AllPairsₚ.++⁺ rxs (AllPairs-singleton⁺ x) (All.map All-singleton⁺ px)

  AllPairs-∷ʳ⁻ : ∀ {x xs} → AllPairs R (xs ∷ʳ x) → AllPairs R xs × All (flip R x) xs
  AllPairs-∷ʳ⁻ {x} {xs} rxs with AllPairs-++⁻ xs rxs
  ... | rxs′ , _ , pxs = rxs′ , All.map Allₚ.singleton⁻ pxs

  AllPairs-reverse⁺ : ∀ {xs} → AllPairs (flip R) xs → AllPairs R (reverse xs)
  AllPairs-reverse⁺ {[]}     []         = []
  AllPairs-reverse⁺ {x ∷ xs} (rx ∷ rxs) =
    ≡.subst (AllPairs R) (≡.sym $ Listₚ.unfold-reverse x xs)
            (AllPairs-∷ʳ⁺ (AllPairs-reverse⁺ rxs) (All-reverse⁺ rx))

module _ {a r} {A : Set a} {R : Rel A r} where
  AllPairs-sym-reverse⁺ : Symmetric R → ∀ {xs} → AllPairs R xs → AllPairs R (reverse xs)
  AllPairs-sym-reverse⁺ sym = AllPairs.map sym ∘ AllPairs-reverse⁺

AllAll : ∀ {a b r} {A : Set a} {B : Set b} → REL A B r → List A → List B → Set _
AllAll R xs ys = All (λ x → All (R x) ys) xs

module _ {a r} {A : Set a} {R : Rel A r} where
  AllPairs-reverse⁻ : ∀ {xs} → AllPairs R (reverse xs) → AllPairs (flip R) xs
  AllPairs-reverse⁻ {xs} rxs =
    ≡.subst (AllPairs (flip R)) (Listₚ.reverse-involutive xs)
            (AllPairs-reverse⁺ rxs)

  -- concat⁻
{-
  AllPairs-concat⁺ : ∀ {xss} → AllAll (AllAll R) xss xss →
                     All (AllPairs R) xss → AllPairs R (concat xss)
  AllPairs-concat⁺ {[]}       rxss         pxss         = []
  AllPairs-concat⁺ {xs ∷ xss} (rxs ∷ rxss) (pxs ∷ pxss) =
    AllPairsₚ.++⁺ {xs = xs} pxs (AllPairs-concat⁺ {! proj₂ (unconsʳ rxs)  !} pxss) {!   !}
-}
  AllPairs-universal : B.Universal R → U.Universal (AllPairs R)
  AllPairs-universal u []       = []
  AllPairs-universal u (x ∷ xs) = All.universal (u _) _ ∷ AllPairs-universal u xs

  AllPairs-replicate⁺ : ∀ n {x} → R x x → AllPairs R (replicate n x)
  AllPairs-replicate⁺ ℕ.zero    Rxx = []
  AllPairs-replicate⁺ (ℕ.suc n) Rxx = Allₚ.replicate⁺ n Rxx ∷ AllPairs-replicate⁺ n Rxx

  AllPairs-replicate⁻ : ∀ {n x} → AllPairs R (replicate (ℕ.suc (ℕ.suc n)) x) → R x x
  AllPairs-replicate⁻ (pxs ∷ rxs) = Allₚ.replicate⁻ pxs


  -- AllPairs-drop⁺

  -- AllPairs-zipWith⁺ :

module _ {c e} (S : Setoid c e) where
  open Setoid S
  open ListSetoidEquality S
  Linked-resp-≋ : ∀ {r} {R : Rel Carrier r} →
                  R Respects₂ _≈_ → (Linked R) Respects _≋_
  Linked-resp-≋ resp [] [] = []
  Linked-resp-≋ resp (_ ∷ []) [-] = [-]
  Linked-resp-≋ resp (e₁ ∷ e₂ ∷ xs≋ys) (x ∷ l) =
   (proj₂ resp e₁ $ proj₁ resp e₂ x) ∷ Linked-resp-≋ resp (e₂ ∷ xs≋ys) l

module _ {a r} {A : Set a} {R : Rel A r} where

-- Linked-pair : R x y →

  Linked-++⁻ʳ : ∀ xs {ys} → Linked R (xs ++ ys) → Linked R ys
  Linked-++⁻ʳ []               rxs       = rxs
  Linked-++⁻ʳ (x ∷ []) {[]}    rxs       = []
  Linked-++⁻ʳ (x ∷ []) {_ ∷ _} (y ∷ rxs) = rxs
  Linked-++⁻ʳ (x ∷ y ∷ xs)     (_ ∷ rxs) = Linked-++⁻ʳ (y ∷ xs) rxs

  Linked-++⁻ˡ : ∀ xs {ys} → Linked R (xs ++ ys) → Linked R xs
  Linked-++⁻ˡ []           rxs        = []
  Linked-++⁻ˡ (x ∷ [])     rxs        = [-]
  Linked-++⁻ˡ (x ∷ y ∷ xs) (rx ∷ rxs) = rx ∷ Linked-++⁻ˡ (y ∷ xs) rxs

  Linked-∷⁻ʳ : ∀ {x xs} → Linked R (x ∷ xs) → Linked R xs
  Linked-∷⁻ʳ {x = x} = Linked-++⁻ʳ [ x ]

  Linked-∷ʳ⁻ˡ : ∀ {xs x} → Linked R (xs ∷ʳ x) → Linked R xs
  Linked-∷ʳ⁻ˡ {xs = xs} = Linked-++⁻ˡ xs
{-
  Linked-∷ʳ₂⁺ : ∀ {xs x y} → Linked R (xs ∷ʳ x) → R x y → Linked R (xs ∷ʳ x ∷ʳ y)
  Linked-∷ʳ₂⁺ {[]} {x} {y} [-] Rxy = Rxy ∷ [-]
  Linked-∷ʳ₂⁺ {x′ ∷ xs} {x} {y} l Rxy = {!   !}

  Linked-reverse⁺ : ∀ {xs} → Linked (flip R) xs → Linked R (reverse xs)
  Linked-reverse⁺ {[]} l = []
  Linked-reverse⁺ {x ∷ []} l = [-]
  Linked-reverse⁺ {x ∷ y ∷ xs} (Rxy ∷ l) = {! Rxy ∷   !}
-}

  -- Linked-inits⁺
  -- respects

  -- Linked-++⁻-middle : ∀ xs {ys} → Linked R (xs ++ ys) → Last (λ x → First (R x) ys) xs

  Linked-universal : B.Universal R → U.Universal (Linked R)
  Linked-universal u [] = []
  Linked-universal u (x ∷ []) = [-]
  Linked-universal u (x ∷ x₁ ∷ xs) = u x x₁ ∷ Linked-universal u (x₁ ∷ xs)

  module _ (R-trans : Transitive R) where
    private
      L⇒A : ∀ {xs} → Linked R xs → AllPairs R xs
      L⇒A = Linkedₚ.Linked⇒AllPairs R-trans
    Linked-trans-∷ : ∀ {x xs} → All (R x) xs → Linked R xs → Linked R (x ∷ xs)
    Linked-trans-∷ a l = Linkedₚ.AllPairs⇒Linked (a ∷ L⇒A l)

    Linked-trans-head : ∀ {x xs} → Linked R (x ∷ xs) → All (R x) xs
    Linked-trans-head = AllPairs.head ∘ L⇒A

{-
Linked-++⁺ : Linked R xs → Linked R ys → Frist (λ x → Last (λ y → R xy) ys) xs → Linked R (xs ++ ys)
-}

-- stdlib?
AllPairs-trans-∷₂ : ∀ {a r} {A : Set a} {R : Rel A r} {x y ys} →
  Transitive R →
  R x y → AllPairs R (y ∷ ys) → AllPairs R (x ∷ y ∷ ys)
AllPairs-trans-∷₂ R-trans Rxy rxs@(px ∷ _) =
  (Rxy ∷ All.map (λ {z} Ryz → R-trans Rxy Ryz) px) ∷ rxs
  -- Transitive R → AllPairs R (xs ∷ʳ v) → AllPairs R (v ∷ ys)
  -- AllPairs R (xs ++ [ v ] ++ ys)

  -- Transitive R → length ys ≥ 1 → AllPairs R (xs ++ ys) → AllPairs R (ys ++ zs) →
  -- AllPairs (xs ++ ys ++ zs)
