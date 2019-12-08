-- Solver for cartesian category

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian

module Experiment.Categories.Category.Cartesian.Solver
  {o ℓ e} {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) where

open import Level
open import Relation.Binary using (Rel)

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open Cartesian cartesian
open HomReasoning
open MR 𝒞

private
  variable
    A B C D E F : Obj

infixr 9 _:∘_
infixr 7 _:×_
infix 11 :⟨_,_⟩

data Sig : Set o where
  ∥_∥  : Obj → Sig
  :⊤   : Sig
  _:×_ : Sig → Sig → Sig

⟦_⟧Sig : Sig → Obj
⟦ ∥ A ∥    ⟧Sig = A
⟦ :⊤       ⟧Sig = ⊤
⟦ S₁ :× S₂ ⟧Sig = ⟦ S₁ ⟧Sig × ⟦ S₂ ⟧Sig

private
  variable
    S T U V : Sig

-- Expression for cartesian category
data Expr : Rel Sig (o ⊔ ℓ) where
  :id    : Expr S S
  _:∘_   : Expr T U → Expr S T → Expr S U
  :π₁    : Expr (S :× T) S
  :π₂    : Expr (S :× T) T
  :⟨_,_⟩ : Expr U S → Expr U T → Expr U (S :× T)
  ∥_∥    : A ⇒ B → Expr ∥ A ∥ ∥ B ∥
  ∥_!∥   : A ⇒ ⊤ → Expr ∥ A ∥ :⊤

-- Atomized expression
data AExpr : Rel Sig (o ⊔ ℓ) where
  :id   : AExpr ∥ A ∥ ∥ A ∥
  :π₁   : AExpr (S :× T) S
  :π₂   : AExpr (S :× T) T
  :π₁∘_ : AExpr S (T :× U) → AExpr S T
  :π₂∘_ : AExpr S (T :× U) → AExpr S U

-- Normalized expression
data NExpr : Rel Sig (o ⊔ ℓ) where
  :!-N   : NExpr S :⊤
  ⟪_⟫    : AExpr S T → NExpr S T
  :⟨_,_⟩ : NExpr U S → NExpr U T → NExpr U (S :× T)
  ∥_∥∘_  : B ⇒ C → NExpr S ∥ B ∥ → NExpr S ∥ C ∥

-- Semantics
⟦_⟧ : Expr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧ = id
⟦ e₁ :∘ e₂     ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ :π₁          ⟧ = π₁
⟦ :π₂          ⟧ = π₂
⟦ :⟨ e₁ , e₂ ⟩ ⟧ = ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
⟦ ∥ f ∥        ⟧ = f
⟦ ∥ g !∥       ⟧ = g

⟦_⟧A : AExpr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id      ⟧A = id
⟦ :π₁      ⟧A = π₁
⟦ :π₂      ⟧A = π₂
⟦ :π₁∘ e   ⟧A = π₁ ∘ ⟦ e ⟧A
⟦ :π₂∘ e   ⟧A = π₂ ∘ ⟦ e ⟧A

⟦_⟧N : NExpr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :!-N         ⟧N = !
⟦ ⟪ e ⟫        ⟧N = ⟦ e ⟧A
⟦ :⟨ e₁ , e₂ ⟩ ⟧N = ⟨ ⟦ e₁ ⟧N , ⟦ e₂ ⟧N ⟩
⟦ ∥ f ∥∘ e     ⟧N = f ∘ ⟦ e ⟧N

:π₁∘-N : NExpr S (T :× U) → NExpr S T
:π₁∘-N ⟪ e ⟫        = ⟪ :π₁∘ e ⟫
:π₁∘-N :⟨ e₁ , e₂ ⟩ = e₁

:π₂∘-N : NExpr S (T :× U) → NExpr S U
:π₂∘-N ⟪ e ⟫        = ⟪ :π₂∘ e ⟫
:π₂∘-N :⟨ e₁ , e₂ ⟩ = e₂

_∘AN_ : AExpr T U → NExpr S T → NExpr S U
:id       ∘AN e₂ = e₂
:π₁       ∘AN e₂ = :π₁∘-N e₂
:π₂       ∘AN e₂ = :π₂∘-N e₂
(:π₁∘ e₁) ∘AN e₂ = :π₁∘-N (e₁ ∘AN e₂)
(:π₂∘ e₁) ∘AN e₂ = :π₂∘-N (e₁ ∘AN e₂)

_∘N_ : NExpr T U → NExpr S T → NExpr S U
:!-N         ∘N e₂ = :!-N
⟪ e₁ ⟫       ∘N e₂ = e₁ ∘AN e₂
:⟨ e₁ , e₂ ⟩ ∘N e₃ = :⟨ e₁ ∘N e₃ , e₂ ∘N e₃ ⟩
(∥ f ∥∘ e₁)  ∘N e₂ = ∥ f ∥∘ (e₁ ∘N e₂)

:π₁-N : ∀ S T → NExpr (S :× T) S
:π₂-N : ∀ S T → NExpr (S :× T) T
:π₁-N ∥ A ∥      T = ⟪ :π₁ ⟫
:π₁-N :⊤         T = ⟪ :π₁ ⟫
:π₁-N (S₁ :× S₂) T = :⟨ :π₁-N _ _ ∘N ⟪ :π₁ ⟫ , :π₂-N _ _ ∘N ⟪ :π₁ ⟫ ⟩
:π₂-N S ∥ A ∥      = ⟪ :π₂ ⟫
:π₂-N S :⊤         = ⟪ :π₂ ⟫
:π₂-N S (T₁ :× T₂) = :⟨ :π₁-N _ _ ∘N ⟪ :π₂ ⟫ , :π₂-N _ _ ∘N ⟪ :π₂ ⟫ ⟩

:id-N : ∀ S → NExpr S S
:id-N ∥ A ∥    = ⟪ :id ⟫
:id-N :⊤       = :!-N
:id-N (S :× T) = :⟨ :π₁-N S T , :π₂-N S T ⟩

-- expand id, π₁ and π₂
toNExpr : Expr S T → NExpr S T
toNExpr :id          = :id-N _
toNExpr (e₁ :∘ e₂)   = toNExpr e₁ ∘N toNExpr e₂
toNExpr :π₁          = :π₁-N _ _
toNExpr :π₂          = :π₂-N _ _
toNExpr :⟨ e₁ , e₂ ⟩ = :⟨ toNExpr e₁ , toNExpr e₂ ⟩
toNExpr ∥ f ∥        = ∥ f ∥∘ ⟪ :id ⟫
toNExpr ∥ g !∥       = :!-N

:π₁∘-N-correct : (e : NExpr S (T :× U)) → ⟦ :π₁∘-N e ⟧N ≈ π₁ ∘ ⟦ e ⟧N
:π₁∘-N-correct ⟪ e ⟫        = refl
:π₁∘-N-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₁

:π₂∘-N-correct : (e : NExpr S (T :× U)) → ⟦ :π₂∘-N e ⟧N ≈ π₂ ∘ ⟦ e ⟧N
:π₂∘-N-correct ⟪ e ⟫        = refl
:π₂∘-N-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₂

∘AN-homo : (e₁ : AExpr T U) (e₂ : NExpr S T) → ⟦ e₁ ∘AN e₂ ⟧N ≈ ⟦ e₁ ⟧A ∘ ⟦ e₂ ⟧N
∘AN-homo :id       e₂ = ⟺ identityˡ
∘AN-homo :π₁       e₂ = :π₁∘-N-correct e₂
∘AN-homo :π₂       e₂ = :π₂∘-N-correct e₂
∘AN-homo (:π₁∘ e₁) e₂ = begin
  ⟦ :π₁∘-N (e₁ ∘AN e₂) ⟧N  ≈⟨ :π₁∘-N-correct (e₁ ∘AN e₂) ⟩
  π₁ ∘ ⟦ e₁ ∘AN e₂ ⟧N      ≈⟨ pushʳ (∘AN-homo e₁ e₂) ⟩
  (π₁ ∘ ⟦ e₁ ⟧A) ∘ ⟦ e₂ ⟧N ∎
∘AN-homo (:π₂∘ e₁) e₂ = begin
  ⟦ (:π₂∘ e₁) ∘AN e₂ ⟧N    ≈⟨ :π₂∘-N-correct (e₁ ∘AN e₂) ⟩
  π₂ ∘ ⟦ e₁ ∘AN e₂ ⟧N      ≈⟨ pushʳ (∘AN-homo e₁ e₂) ⟩
  (π₂ ∘ ⟦ e₁ ⟧A) ∘ ⟦ e₂ ⟧N ∎

∘N-homo : (e₁ : NExpr T U) (e₂ : NExpr S T) → ⟦ e₁ ∘N e₂ ⟧N ≈ ⟦ e₁ ⟧N ∘ ⟦ e₂ ⟧N
∘N-homo :!-N         e₂ = !-unique _
∘N-homo ⟪ e₁ ⟫       e₂ = ∘AN-homo e₁ e₂
∘N-homo :⟨ e₁ , e₂ ⟩ e₃ = ⟨⟩-cong₂ (∘N-homo e₁ e₃) (∘N-homo e₂ e₃) ○ ⟺ ⟨⟩∘
∘N-homo (∥ f ∥∘ e₁)  e₂ = pushʳ (∘N-homo e₁ e₂)

private
  :π₁′ : ∀ S T → NExpr (S :× T) S
  :π₁′ S T = ⟪ :π₁ ⟫
  :π₂′ : ∀ S T → NExpr (S :× T) T
  :π₂′ S T = ⟪ :π₂ ⟫

:π₁-N-correct : ∀ S T → ⟦ :π₁-N S T ⟧N ≈ π₁
:π₂-N-correct : ∀ S T → ⟦ :π₂-N S T ⟧N ≈ π₂
:π₁-N-correct ∥ A ∥      T = refl
:π₁-N-correct :⊤         T = refl
:π₁-N-correct (S₁ :× S₂) T = begin
  ⟨ ⟦ :π₁-N S₁ S₂ ∘N :π₁′ (S₁ :× S₂) T ⟧N ,
    ⟦ :π₂-N S₁ S₂ ∘N :π₁′ (S₁ :× S₂) T ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘N-homo (:π₁-N S₁ S₂) (:π₁′ _ T))
                (∘N-homo (:π₂-N S₁ S₂) (:π₁′ _ T)) ⟩
  ⟨ ⟦ :π₁-N S₁ S₂ ⟧N ∘ ⟦ :π₁′ (S₁ :× S₂) T ⟧N ,
    ⟦ :π₂-N S₁ S₂ ⟧N ∘ ⟦ :π₁′ (S₁ :× S₂) T ⟧N ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-N S₁ S₂ ⟧N , ⟦ :π₂-N S₁ S₂ ⟧N ⟩ ∘ ⟦ :π₁′ (S₁ :× S₂) T ⟧N
    ≈⟨ ⟨⟩-cong₂ (:π₁-N-correct S₁ S₂) (:π₂-N-correct S₁ S₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₁
    ≈⟨ elimˡ η ⟩
  π₁
    ∎
:π₂-N-correct S ∥ A ∥      = refl
:π₂-N-correct S :⊤         = refl
:π₂-N-correct S (T₁ :× T₂) = begin
  ⟨ ⟦ :π₁-N T₁ T₂ ∘N :π₂′ S (T₁ :× T₂) ⟧N ,
    ⟦ :π₂-N T₁ T₂ ∘N :π₂′ S (T₁ :× T₂) ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘N-homo (:π₁-N T₁ T₂) (:π₂′ S _))
                (∘N-homo (:π₂-N T₁ T₂) (:π₂′ S _)) ⟩
  ⟨ ⟦ :π₁-N T₁ T₂ ⟧N ∘ ⟦ :π₂′ S (T₁ :× T₂) ⟧N ,
    ⟦ :π₂-N T₁ T₂ ⟧N ∘ ⟦ :π₂′ S (T₁ :× T₂) ⟧N ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-N T₁ T₂ ⟧N , ⟦ :π₂-N T₁ T₂ ⟧N ⟩ ∘ ⟦ :π₂′ S (T₁ :× T₂) ⟧N
    ≈⟨ ⟨⟩-cong₂ (:π₁-N-correct T₁ T₂) (:π₂-N-correct T₁ T₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₂
    ≈⟨ elimˡ η ⟩
  π₂
    ∎

:id-N-correct : ∀ S → ⟦ :id-N S ⟧N ≈ id
:id-N-correct ∥ A ∥      = refl
:id-N-correct :⊤         = !-unique id
:id-N-correct (S₁ :× S₂) =
  ⟨⟩-cong₂ (:π₁-N-correct S₁ S₂) (:π₂-N-correct S₁ S₂) ○ η

toNExpr-correct : ∀ (e : Expr S T) → ⟦ toNExpr e ⟧N ≈ ⟦ e ⟧
toNExpr-correct {S} :id          = :id-N-correct S
toNExpr-correct (e₁ :∘ e₂)       = begin
  ⟦ toNExpr e₁ ∘N toNExpr e₂ ⟧N     ≈⟨ ∘N-homo (toNExpr e₁) (toNExpr e₂) ⟩
  ⟦ toNExpr e₁ ⟧N ∘ ⟦ toNExpr e₂ ⟧N ≈⟨ toNExpr-correct e₁ ⟩∘⟨ toNExpr-correct e₂ ⟩
  ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧                   ∎
toNExpr-correct {S :× T} {S} :π₁ = :π₁-N-correct S T
toNExpr-correct {S :× T} {T} :π₂ = :π₂-N-correct S T
toNExpr-correct :⟨ e₁ , e₂ ⟩     = ⟨⟩-cong₂ (toNExpr-correct e₁) (toNExpr-correct e₂)
toNExpr-correct ∥ f ∥            = identityʳ
toNExpr-correct ∥ g !∥           = !-unique g

solve : (e₁ e₂ : Expr S T) → ⟦ toNExpr e₁ ⟧N ≈ ⟦ toNExpr e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧          ≈˘⟨ toNExpr-correct e₁ ⟩
  ⟦ toNExpr e₁ ⟧N ≈⟨ eq ⟩
  ⟦ toNExpr e₂ ⟧N ≈⟨ toNExpr-correct e₂ ⟩
  ⟦ e₂ ⟧          ∎

-- Combinators
:! : Expr ∥ A ∥ :⊤
:! = ∥ ! !∥

:swap : Expr (S :× T) (T :× S)
:swap = :⟨ :π₂ , :π₁ ⟩

:assocˡ : Expr ((S :× T) :× U) (S :× T :× U)
:assocˡ = :⟨ :π₁ :∘ :π₁ , :⟨ :π₂ :∘ :π₁ , :π₂ ⟩ ⟩

:assocʳ : Expr (S :× T :× U) ((S :× T) :× U)
:assocʳ = :⟨ :⟨ :π₁ , :π₁ :∘ :π₂ ⟩ , :π₂ :∘ :π₂ ⟩

infixr 8 _:⁂_

_:⁂_ : Expr S T → Expr U V → Expr (S :× U) (T :× V)
e₁ :⁂ e₂ = :⟨ e₁ :∘ :π₁ , e₂ :∘ :π₂ ⟩

:first : Expr S T → Expr (S :× U) (T :× U)
:first e = e :⁂ :id

:second : Expr T U → Expr (S :× T) (S :× U)
:second e = :id :⁂ e

-- Example
private
  module _ {A B C D E} {f : D ⇒ E} {g : C ⇒ D} {h : B ⇒ C} {i : A ⇒ B} where
    _ : (f ∘ g) ∘ id ∘ h ∘ i ≈ f ∘ (g ∘ h) ∘ i
    _ = solve ((∥ f ∥ :∘ ∥ g ∥) :∘ :id :∘ ∥ h ∥ :∘ ∥ i ∥)
              (∥ f ∥ :∘ (∥ g ∥ :∘ ∥ h ∥) :∘ ∥ i ∥)
              refl

  swap∘swap≈id : ∀ {A B} → swap {A}{B} ∘ swap {B}{A} ≈ id
  swap∘swap≈id {A} {B} = solve (:swap {∥ A ∥} {∥ B ∥} :∘ :swap) :id refl

  assocʳ∘assocˡ≈id : ∀ {A B C} → assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
  assocʳ∘assocˡ≈id {A} {B} {C} =
    solve (:assocʳ {∥ A ∥} {∥ B ∥} {∥ C ∥} :∘ :assocˡ) :id refl

  module _ {f : B ⇒ C} (f′ : A ⇒ B) {g : E ⇒ F} {g′ : D ⇒ E} where
    ⁂-∘ : (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
    ⁂-∘ = solve lhs rhs refl where
      lhs = (∥ f ∥ :⁂ ∥ g ∥) :∘ (∥ f′ ∥ :⁂ ∥ g′ ∥)
      rhs = (∥ f ∥ :∘ ∥ f′ ∥) :⁂ (∥ g ∥ :∘ ∥ g′ ∥)

  module _ {A B C D} where
    pentagon′ : (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈
                assocˡ ∘ assocˡ {A × B} {C} {D}
    pentagon′ = solve lhs rhs refl where
      lhs = (:id :⁂ :assocˡ) :∘ :assocˡ :∘ (:assocˡ :⁂ :id)
      rhs = :assocˡ :∘ :assocˡ {∥ A ∥ :× ∥ B ∥} {∥ C ∥} {∥ D ∥}

  module _ {A B} {f : A ⇒ B} where
    commute : ⟨ ! , id ⟩ ∘ f ≈ ⟨ id ∘ π₁ , f ∘ π₂ ⟩ ∘ ⟨ ! , id ⟩
    commute = solve (:⟨ :! , :id ⟩ :∘ ∥ f ∥)
                    (:⟨ :id :∘ :π₁ , ∥ f ∥ :∘ :π₂ ⟩ :∘ :⟨ :! , :id ⟩)
                    refl
