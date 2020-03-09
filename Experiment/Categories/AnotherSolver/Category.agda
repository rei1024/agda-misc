-- Solver for Category

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Experiment.Categories.AnotherSolver.Category
  {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Relation.Binary using (Rel)
import Function.Base as Fun

open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
import Categories.Morphism.Reasoning as MR
import Categories.Category.Equivalence as Eq

open Category 𝒞
open HomReasoning
open MR 𝒞

private
  variable
    A B C D E : Obj

infixr 9 _:∘_

data Expr : Rel Obj (o ⊔ ℓ) where
  :id  : Expr A A
  _:∘_ : Expr B C → Expr A B → Expr A C
  ∥_∥  : A ⇒ B → Expr A B

data NExpr : Rel Obj (o ⊔ ℓ) where
  :id  : NExpr A A
  _:∘_ : B ⇒ C → NExpr A B → NExpr A C

-- Semantics
⟦_⟧ : Expr A B → A ⇒ B
⟦ :id      ⟧ = id
⟦ e₁ :∘ e₂ ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ ∥ f ∥    ⟧ = f

⟦_⟧N : NExpr A B → A ⇒ B
⟦ :id    ⟧N = id
⟦ f :∘ e ⟧N = f ∘ ⟦ e ⟧N

_∘N_ : NExpr B C → NExpr A B → NExpr A C
:id       ∘N e₂ = e₂
(f :∘ e₁) ∘N e₂ = f :∘ (e₁ ∘N e₂)

linear : NExpr A B → Expr A B
linear :id      = :id
linear (f :∘ e) = ∥ f ∥ :∘ linear e

normalise : Expr A B → NExpr A B
normalise :id        = :id
normalise (e₁ :∘ e₂) = normalise e₁ ∘N normalise e₂
normalise ∥ f ∥      = f :∘ :id

∘N-homo : (e₁ : NExpr B C) (e₂ : NExpr A B) → ⟦ e₁ ∘N e₂ ⟧N ≈ ⟦ e₁ ⟧N ∘ ⟦ e₂ ⟧N
∘N-homo :id       e₂ = sym identityˡ
∘N-homo (f :∘ e₁) e₂ = pushʳ (∘N-homo e₁ e₂)

NExpr-assoc : {f : NExpr A B} {g : NExpr B C} {h : NExpr C D} →
              ⟦ (h ∘N g) ∘N f ⟧N ≈ ⟦ h ∘N (g ∘N f) ⟧N
NExpr-assoc {f = f} {g} {:id}    = refl
NExpr-assoc {f = f} {g} {x :∘ h} = ∘-resp-≈ʳ (NExpr-assoc {f = f} {g} {h})

NExpr-identityʳ : {f : NExpr A B} → ⟦ f ∘N :id ⟧N ≈ ⟦ f ⟧N
NExpr-identityʳ {f = :id}    = refl
NExpr-identityʳ {f = x :∘ f} = ∘-resp-≈ʳ (NExpr-identityʳ {f = f})

normalise-correct : (e : Expr A B) → ⟦ normalise e ⟧N ≈ ⟦ e ⟧
normalise-correct :id        = refl
normalise-correct (e₁ :∘ e₂) = begin
  ⟦ normalise e₁ ∘N normalise e₂ ⟧N     ≈⟨ ∘N-homo (normalise e₁) (normalise e₂) ⟩
  ⟦ normalise e₁ ⟧N ∘ ⟦ normalise e₂ ⟧N ≈⟨ normalise-correct e₁ ⟩∘⟨ normalise-correct e₂ ⟩
  ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧                       ∎
normalise-correct ∥ f ∥      = identityʳ

normalise-cong : (e₁ e₂ : Expr A B) →
                 ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧ → ⟦ normalise e₁ ⟧N ≈ ⟦ normalise e₂ ⟧N
normalise-cong e₁ e₂ eq = trans (normalise-correct e₁) (trans eq (sym (normalise-correct e₂)))

normalise-inj : (e₁ e₂ : Expr A B) →
                ⟦ normalise e₁ ⟧N ≈ ⟦ normalise e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
normalise-inj e₁ e₂ eq = trans (sym (normalise-correct e₁)) (trans eq (normalise-correct e₂))

linear-correct : (e : NExpr A B) → ⟦ linear e ⟧ ≈ ⟦ e ⟧N
linear-correct :id      = refl
linear-correct (f :∘ e) = ∘-resp-≈ʳ (linear-correct e)

Expr-category : Category o (o ⊔ ℓ) e
Expr-category = categoryHelper record
  { Obj       = Obj
  ; _⇒_       = Expr
  ; _≈_       = λ e₁ e₂ → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
  ; id        = :id
  ; _∘_       = _:∘_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

NExpr-category : Category o (o ⊔ ℓ) e
NExpr-category = categoryHelper record
  { Obj       = Obj
  ; _⇒_       = NExpr
  ; _≈_       = λ e₁ e₂ → ⟦ e₁ ⟧N ≈ ⟦ e₂ ⟧N
  ; id        = :id
  ; _∘_       = _∘N_
  ; assoc     = λ {_} {_} {_} {_} {f = f} {g} {h} → NExpr-assoc {f = f} {g} {h}
  ; identityˡ = refl
  ; identityʳ = λ {_} {_} {f = f} → NExpr-identityʳ {f = f}
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = λ {_} {_} {_} {f} {h} {g} {i} f≈h g≈i →
    trans (∘N-homo f g) (trans (∘-resp-≈ f≈h g≈i) (sym (∘N-homo h i)))
  }

⟦⟧-functor : Functor Expr-category 𝒞
⟦⟧-functor = record
  { F₀           = Fun.id
  ; F₁           = ⟦_⟧
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = Fun.id
  }

⟦⟧N-functor : Functor NExpr-category 𝒞
⟦⟧N-functor = record
  { F₀           = Fun.id
  ; F₁           = ⟦_⟧N
  ; identity     = refl
  ; homomorphism = λ {_} {_} {_} {f} {g} → ∘N-homo g f
  ; F-resp-≈     = Fun.id
  }

normalise-functor : Functor Expr-category NExpr-category
normalise-functor = record
  { F₀           = Fun.id
  ; F₁           = normalise
  ; identity     = refl
  ; homomorphism = λ {_} {_} {_} {f = f} {g} → refl
  ; F-resp-≈     = λ {_} {_} {f} {g} f≈g → normalise-cong f g f≈g
  }

linear-functor : Functor NExpr-category Expr-category
linear-functor = record
  { F₀           = Fun.id
  ; F₁           = linear
  ; identity     = refl
  ; homomorphism = λ {_} {_} {_} {f} {g} → begin
    ⟦ linear (g ∘N f) ⟧         ≈⟨ linear-correct (g ∘N f) ⟩
    ⟦ g ∘N f ⟧N                 ≈⟨ ∘N-homo g f ⟩
    ⟦ g ⟧N ∘ ⟦ f ⟧N             ≈⟨ sym (linear-correct g) ⟩∘⟨ sym (linear-correct f) ⟩
    ⟦ linear g ⟧ ∘ ⟦ linear f ⟧ ∎
  ; F-resp-≈     = λ {_} {_} {f} {g} eq → begin
    ⟦ linear f ⟧ ≈⟨ linear-correct f ⟩
    ⟦ f ⟧N       ≈⟨ eq ⟩
    ⟦ g ⟧N       ≈⟨ sym (linear-correct g) ⟩
    ⟦ linear g ⟧ ∎
  }

normalise-functor-Faithful : Faithful normalise-functor
normalise-functor-Faithful = normalise-inj

linear-functor-Faithful : Faithful linear-functor
linear-functor-Faithful = λ f g x → trans (sym (linear-correct f)) (trans x (linear-correct g))

⟦⟧n-functor : Functor Expr-category 𝒞
⟦⟧n-functor = ⟦⟧N-functor ∘F normalise-functor

⟦⟧l-functor : Functor NExpr-category 𝒞
⟦⟧l-functor = ⟦⟧-functor ∘F linear-functor

normalise-natural : NaturalTransformation ⟦⟧n-functor ⟦⟧-functor
normalise-natural = ntHelper record
    { η       = λ X → id
    ; commute = λ e → begin
      id ∘ ⟦ normalise e ⟧N ≈⟨ identityˡ ⟩
      ⟦ normalise e ⟧N      ≈⟨ normalise-correct e ⟩
      ⟦ e ⟧                 ≈⟨ sym identityʳ ⟩
      ⟦ e ⟧ ∘ id           ∎
    }

linear-natural : NaturalTransformation ⟦⟧l-functor ⟦⟧N-functor
linear-natural = ntHelper record
  { η       = λ X → id
  ; commute = λ e → trans identityˡ (trans (linear-correct e) (sym identityʳ))
  }

embedExpr : Functor 𝒞 Expr-category
embedExpr = record
  { F₀           = Fun.id
  ; F₁           = ∥_∥
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = Fun.id
  }

embedNExpr : Functor 𝒞 NExpr-category
embedNExpr = record
  { F₀           = Fun.id
  ; F₁           = λ e → e :∘ :id
  ; identity     = identity²
  ; homomorphism = λ {_} {_} {_} {f} {g} → assoc
  ; F-resp-≈     = λ f≈g → trans identityʳ (trans f≈g (sym identityʳ))
  }

{-
solve : (e₁ e₂ : Expr A B) → ⟦ e₁ ⟧N ≈ ⟦ e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧  ≈˘⟨ ⟦e⟧N≈⟦e⟧ e₁ ⟩
  ⟦ e₁ ⟧N ≈⟨ eq ⟩
  ⟦ e₂ ⟧N ≈⟨ ⟦e⟧N≈⟦e⟧ e₂ ⟩
  ⟦ e₂ ⟧  ∎

∥-∥ : ∀ {f : A ⇒ B} → Expr A B
∥-∥ {f = f} = ∥ f ∥
-}
