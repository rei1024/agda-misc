-- Solver for cartesian category
-- Normalisation is based on https://arxiv.org/abs/math/9911059

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian

module Experiment.Categories.Category.Cartesian.Solver
  {o ℓ e} {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) where

open import Level
open import Relation.Binary using (Rel; REL)

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

-- Atomised expression
data AExpr : REL Sig Obj (o ⊔ ℓ) where
  :π₁   : AExpr (∥ A ∥ :× T) A
  :π₂   : AExpr (S :× ∥ B ∥) B
  _∘:π₁ : AExpr S A → AExpr (S :× T) A
  _∘:π₂ : AExpr T A → AExpr (S :× T) A

-- Normalised expression
data NExpr : Rel Sig (o ⊔ ℓ) where
  :id    : NExpr ∥ A ∥ ∥ A ∥
  :!-N   : NExpr S :⊤
  ⟪_⟫    : AExpr S A → NExpr S ∥ A ∥
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

⟦_⟧A : AExpr S B → ⟦ S ⟧Sig ⇒ B
⟦ :π₁      ⟧A = π₁
⟦ :π₂      ⟧A = π₂
⟦ e ∘:π₁   ⟧A = ⟦ e ⟧A ∘ π₁
⟦ e ∘:π₂   ⟧A = ⟦ e ⟧A ∘ π₂

⟦_⟧N : NExpr S T → ⟦ S ⟧Sig ⇒ ⟦ T ⟧Sig
⟦ :id          ⟧N = id
⟦ :!-N         ⟧N = !
⟦ ⟪ e ⟫        ⟧N = ⟦ e ⟧A
⟦ :⟨ e₁ , e₂ ⟩ ⟧N = ⟨ ⟦ e₁ ⟧N , ⟦ e₂ ⟧N ⟩
⟦ ∥ f ∥∘ e     ⟧N = f ∘ ⟦ e ⟧N

:π₁∘-N : NExpr S (T :× U) → NExpr S T
:π₁∘-N :⟨ e₁ , e₂ ⟩ = e₁

:π₂∘-N : NExpr S (T :× U) → NExpr S U
:π₂∘-N :⟨ e₁ , e₂ ⟩ = e₂

_∘AN_ : AExpr T A → NExpr S T → NExpr S ∥ A ∥
:π₁       ∘AN e₂ = :π₁∘-N e₂
:π₂       ∘AN e₂ = :π₂∘-N e₂
(e₁ ∘:π₁) ∘AN e₂ = e₁ ∘AN :π₁∘-N e₂
(e₁ ∘:π₂) ∘AN e₂ = e₁ ∘AN :π₂∘-N e₂

_∘:π₁-N : NExpr S U → NExpr (S :× T) U
:id          ∘:π₁-N = ⟪ :π₁ ⟫
:!-N         ∘:π₁-N = :!-N
⟪ e ⟫        ∘:π₁-N = ⟪ e ∘:π₁ ⟫
:⟨ e₁ , e₂ ⟩ ∘:π₁-N = :⟨ e₁ ∘:π₁-N , e₂ ∘:π₁-N ⟩
(∥ f ∥∘ e)   ∘:π₁-N = ∥ f ∥∘ (e ∘:π₁-N)

_∘:π₂-N : NExpr T U → NExpr (S :× T) U
:id          ∘:π₂-N = ⟪ :π₂ ⟫
:!-N         ∘:π₂-N = :!-N
⟪ e ⟫        ∘:π₂-N = ⟪ e ∘:π₂ ⟫
:⟨ e₁ , e₂ ⟩ ∘:π₂-N = :⟨ e₁ ∘:π₂-N , e₂ ∘:π₂-N ⟩
(∥ f ∥∘ e)   ∘:π₂-N = ∥ f ∥∘ (e ∘:π₂-N)

_∘N_ : NExpr T U → NExpr S T → NExpr S U
:id          ∘N e₂ = e₂
:!-N         ∘N e₂ = :!-N
⟪ e₁ ⟫       ∘N e₂ = e₁ ∘AN e₂
:⟨ e₁ , e₂ ⟩ ∘N e₃ = :⟨ e₁ ∘N e₃ , e₂ ∘N e₃ ⟩
(∥ f ∥∘ e₁)  ∘N e₂ = ∥ f ∥∘ (e₁ ∘N e₂)

:π₁-N : ∀ S T → NExpr (S :× T) S
:π₂-N : ∀ S T → NExpr (S :× T) T
:π₁-N ∥ _ ∥      T = ⟪ :π₁ ⟫
:π₁-N :⊤         T = :!-N
:π₁-N (S₁ :× S₂) T = :⟨ (:π₁-N S₁ S₂) ∘:π₁-N , (:π₂-N S₁ S₂) ∘:π₁-N ⟩
:π₂-N S ∥ _ ∥      = ⟪ :π₂ ⟫
:π₂-N S :⊤         = :!-N
:π₂-N S (T₁ :× T₂) = :⟨ (:π₁-N T₁ T₂) ∘:π₂-N , (:π₂-N T₁ T₂) ∘:π₂-N ⟩

:id-N : ∀ S → NExpr S S
:id-N ∥ _ ∥    = :id
:id-N :⊤       = :!-N
:id-N (S :× T) = :⟨ :π₁-N S T , :π₂-N S T ⟩

-- expand id, π₁ and π₂
normalise : Expr S T → NExpr S T
normalise :id          = :id-N _
normalise (e₁ :∘ e₂)   = normalise e₁ ∘N normalise e₂
normalise :π₁          = :π₁-N _ _
normalise :π₂          = :π₂-N _ _
normalise :⟨ e₁ , e₂ ⟩ = :⟨ normalise e₁ , normalise e₂ ⟩
normalise ∥ f ∥        = ∥ f ∥∘ :id
normalise ∥ g !∥       = :!-N

:π₁∘-N-correct : (e : NExpr S (T :× U)) → ⟦ :π₁∘-N e ⟧N ≈ π₁ ∘ ⟦ e ⟧N
:π₁∘-N-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₁

:π₂∘-N-correct : (e : NExpr S (T :× U)) → ⟦ :π₂∘-N e ⟧N ≈ π₂ ∘ ⟦ e ⟧N
:π₂∘-N-correct :⟨ e₁ , e₂ ⟩ = ⟺ project₂

∘AN-homo : (e₁ : AExpr T A) (e₂ : NExpr S T) → ⟦ e₁ ∘AN e₂ ⟧N ≈ ⟦ e₁ ⟧A ∘ ⟦ e₂ ⟧N
∘AN-homo :π₁       e₂ = :π₁∘-N-correct e₂
∘AN-homo :π₂       e₂ = :π₂∘-N-correct e₂
∘AN-homo (e₁ ∘:π₁) e₂ = begin
  ⟦ e₁ ∘AN :π₁∘-N e₂ ⟧N    ≈⟨ ∘AN-homo e₁ (:π₁∘-N e₂) ⟩
  ⟦ e₁ ⟧A ∘ ⟦ :π₁∘-N e₂ ⟧N ≈⟨ pushʳ (:π₁∘-N-correct e₂) ⟩
  (⟦ e₁ ⟧A ∘ π₁) ∘ ⟦ e₂ ⟧N ∎
∘AN-homo (e₁ ∘:π₂) e₂ = begin
  ⟦ e₁ ∘AN :π₂∘-N e₂ ⟧N    ≈⟨ ∘AN-homo e₁ (:π₂∘-N e₂) ⟩
  ⟦ e₁ ⟧A ∘ ⟦ :π₂∘-N e₂ ⟧N ≈⟨ pushʳ (:π₂∘-N-correct e₂) ⟩
  (⟦ e₁ ⟧A ∘ π₂) ∘ ⟦ e₂ ⟧N ∎

∘N-homo : (e₁ : NExpr T U) (e₂ : NExpr S T) → ⟦ e₁ ∘N e₂ ⟧N ≈ ⟦ e₁ ⟧N ∘ ⟦ e₂ ⟧N
∘N-homo :id          e₂ = ⟺ identityˡ
∘N-homo :!-N         e₂ = !-unique _
∘N-homo ⟪ e₁ ⟫       e₂ = ∘AN-homo e₁ e₂
∘N-homo :⟨ e₁ , e₂ ⟩ e₃ = ⟨⟩-cong₂ (∘N-homo e₁ e₃) (∘N-homo e₂ e₃) ○ ⟺ ⟨⟩∘
∘N-homo (∥ f ∥∘ e₁)  e₂ = pushʳ (∘N-homo e₁ e₂)

∘:π₁-N-correct : ∀ (e : NExpr S U) → ⟦ (_∘:π₁-N {T = T}) e ⟧N ≈ ⟦ e ⟧N ∘ π₁
∘:π₁-N-correct :id          = ⟺ identityˡ
∘:π₁-N-correct :!-N         = !-unique _
∘:π₁-N-correct ⟪ e ⟫        = refl
∘:π₁-N-correct :⟨ e₁ , e₂ ⟩ =
  ⟨⟩-cong₂ (∘:π₁-N-correct e₁) (∘:π₁-N-correct e₂) ○ ⟺ ⟨⟩∘
∘:π₁-N-correct (∥ f ∥∘ e)   = pushʳ (∘:π₁-N-correct e)

∘:π₂-N-correct : ∀ (e : NExpr T U) → ⟦ (_∘:π₂-N {S = S}) e ⟧N ≈ ⟦ e ⟧N ∘ π₂
∘:π₂-N-correct :id          = ⟺ identityˡ
∘:π₂-N-correct :!-N         = !-unique _
∘:π₂-N-correct ⟪ e ⟫        = refl
∘:π₂-N-correct :⟨ e₁ , e₂ ⟩ =
  ⟨⟩-cong₂ (∘:π₂-N-correct e₁) (∘:π₂-N-correct e₂) ○ ⟺ ⟨⟩∘
∘:π₂-N-correct (∥ f ∥∘ e)   = pushʳ (∘:π₂-N-correct e)

private
  ∘:π₁-N′ : ∀ S T → NExpr S U → NExpr (S :× T) U
  ∘:π₁-N′ _ _ = _∘:π₁-N
  ∘:π₂-N′ : ∀ S T → NExpr T U → NExpr (S :× T) U
  ∘:π₂-N′ _ _ = _∘:π₂-N

:π₁-N-correct : ∀ S T → ⟦ :π₁-N S T ⟧N ≈ π₁
:π₂-N-correct : ∀ S T → ⟦ :π₂-N S T ⟧N ≈ π₂
:π₁-N-correct ∥ A ∥      T = refl
:π₁-N-correct :⊤         T = !-unique _
:π₁-N-correct (S₁ :× S₂) T = begin
  ⟨ ⟦ ∘:π₁-N′ (S₁ :× S₂) T (:π₁-N S₁ S₂) ⟧N ,
    ⟦ ∘:π₁-N′ (S₁ :× S₂) T (:π₂-N S₁ S₂) ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘:π₁-N-correct (:π₁-N S₁ S₂))
                (∘:π₁-N-correct (:π₂-N S₁ S₂)) ⟩
  ⟨ ⟦ :π₁-N S₁ S₂ ⟧N ∘ π₁ , ⟦ :π₂-N S₁ S₂ ⟧N ∘ π₁ ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-N S₁ S₂ ⟧N , ⟦ :π₂-N S₁ S₂ ⟧N ⟩ ∘ π₁
    ≈⟨ ⟨⟩-cong₂ (:π₁-N-correct S₁ S₂) (:π₂-N-correct S₁ S₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₁
    ≈⟨ elimˡ η ⟩
  π₁
    ∎
:π₂-N-correct S ∥ A ∥      = refl
:π₂-N-correct S :⊤         = !-unique _
:π₂-N-correct S (T₁ :× T₂) = begin
  ⟨ ⟦ ∘:π₂-N′ S (T₁ :× T₂) (:π₁-N T₁ T₂) ⟧N ,
    ⟦ ∘:π₂-N′ S (T₁ :× T₂) (:π₂-N T₁ T₂) ⟧N ⟩
    ≈⟨ ⟨⟩-cong₂ (∘:π₂-N-correct (:π₁-N T₁ T₂))
                (∘:π₂-N-correct (:π₂-N T₁ T₂)) ⟩
  ⟨ ⟦ :π₁-N T₁ T₂ ⟧N ∘ π₂ , ⟦ :π₂-N T₁ T₂ ⟧N ∘ π₂ ⟩
    ≈˘⟨ ⟨⟩∘ ⟩
  ⟨ ⟦ :π₁-N T₁ T₂ ⟧N , ⟦ :π₂-N T₁ T₂ ⟧N ⟩ ∘ π₂
    ≈⟨ ⟨⟩-cong₂ (:π₁-N-correct T₁ T₂) (:π₂-N-correct T₁ T₂) ⟩∘⟨refl ⟩
  ⟨ π₁ , π₂ ⟩ ∘ π₂
    ≈⟨ elimˡ η ⟩
  π₂
    ∎

:id-N-correct : ∀ S → ⟦ :id-N S ⟧N ≈ id
:id-N-correct ∥ _ ∥      = refl
:id-N-correct :⊤         = !-unique id
:id-N-correct (S₁ :× S₂) =
  ⟨⟩-cong₂ (:π₁-N-correct S₁ S₂) (:π₂-N-correct S₁ S₂) ○ η

correct : ∀ (e : Expr S T) → ⟦ normalise e ⟧N ≈ ⟦ e ⟧
correct {S} :id          = :id-N-correct S
correct (e₁ :∘ e₂)       = begin
  ⟦ normalise e₁ ∘N normalise e₂ ⟧N     ≈⟨ ∘N-homo (normalise e₁) (normalise e₂) ⟩
  ⟦ normalise e₁ ⟧N ∘ ⟦ normalise e₂ ⟧N ≈⟨ correct e₁ ⟩∘⟨ correct e₂ ⟩
  ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧                       ∎
correct {S :× T} {S} :π₁ = :π₁-N-correct S T
correct {S :× T} {T} :π₂ = :π₂-N-correct S T
correct :⟨ e₁ , e₂ ⟩     = ⟨⟩-cong₂ (correct e₁) (correct e₂)
correct ∥ f ∥            = identityʳ
correct ∥ g !∥           = !-unique g

solve : (e₁ e₂ : Expr S T) →
        ⟦ normalise e₁ ⟧N ≈ ⟦ normalise e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧          ≈˘⟨ correct e₁ ⟩
  ⟦ normalise e₁ ⟧N ≈⟨ eq ⟩
  ⟦ normalise e₂ ⟧N ≈⟨ correct e₂ ⟩
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
  module _ {f : D ⇒ E} {g : C ⇒ D} {h : B ⇒ C} {i : A ⇒ B} where
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

  module _ {A B C} where
    hexagon₁′ : (id ⁂ swap) ∘ assocˡ ∘ (swap ⁂ id) ≈
                assocˡ ∘ swap ∘ assocˡ {A}{B}{C}
    hexagon₁′ = solve lhs rhs refl where
      lhs = (:id :⁂ :swap) :∘ :assocˡ :∘ (:swap :⁂ :id)
      rhs = :assocˡ :∘ :swap :∘ :assocˡ {∥ A ∥}{∥ B ∥}{∥ C ∥}

  module _ {f : A ⇒ B} where
    commute : ⟨ ! , id ⟩ ∘ f ≈ ⟨ id ∘ π₁ , f ∘ π₂ ⟩ ∘ ⟨ ! , id ⟩
    commute = solve (:⟨ :! , :id ⟩ :∘ ∥ f ∥)
                    (:⟨ :id :∘ :π₁ , ∥ f ∥ :∘ :π₂ ⟩ :∘ :⟨ :! , :id ⟩)
                    refl

  _ : id {⊤} ≈ !
  _ = solve (∥ id !∥) :! refl

  _ : π₁ {⊤} {⊤} ≈ π₂
  _ = solve (:π₁ {:⊤} {:⊤}) :π₂ refl

  module _ {f : A ⇒ B} {g : C ⇒ D} where
    first↔second′ : first f ∘ second g ≈ second g ∘ first f
    first↔second′ = solve (:first ∥ f ∥ :∘ :second ∥ g ∥)
                          (:second ∥ g ∥ :∘ :first ∥ f ∥)
                          refl
