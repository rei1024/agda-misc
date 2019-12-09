-- This code is based on https://github.com/agda/agda-stdlib/pull/800/files

{-# OPTIONS --without-K --safe #-}

module Experiment.Categories.Solver.Category.Reflection where

open import Data.Nat
open import Data.List
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Product
open import Data.Bool
open import Function using (_⟨_⟩_)
open import Agda.Builtin.Reflection as Builtin

open import Categories.Category

open import Experiment.Categories.Solver.Category hiding (solve)

_==_ = Builtin.primQNameEquality
{-# INLINE _==_ #-}

_>>=_ = bindTC
{-# INLINE _>>=_ #-}

infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs = arg (arg-info visible relevant) x ∷ xs
pattern _⟅∷⟆_ x xs = arg (arg-info hidden  relevant) x ∷ xs

infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_ : ℕ → List (Arg Term) → List (Arg Term)
zero  ⋯⟅∷⟆ xs = xs
suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆ i ⋯⟅∷⟆ xs
{-# INLINE _⋯⟅∷⟆_ #-}

getName : Term → Maybe Name
getName (con c args) = just c
getName (def f args) = just f
getName _            = nothing

getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (x ⟨∷⟩ y ⟨∷⟩ []) = just (x , y)
  go (x ∷ xs)         = go xs
  go _                = nothing
getArgs _ = nothing

record CategoryNames : Set where
  field
    is-∘  : Name → Bool
    is-id : Name → Bool

findCategoryNames : Term → TC CategoryNames
findCategoryNames cat = do
  ∘-name ← normalise (quote Category._∘_ ⟨ def ⟩ 2 ⋯⟅∷⟆ cat ⟨∷⟩ [])
  id-name ← normalise (quote Category.id ⟨ def ⟩ 2 ⋯⟅∷⟆ cat ⟨∷⟩ [])
  returnTC record
    { is-∘  = buildMatcher (quote Category._∘_) (getName ∘-name)
    ; is-id = buildMatcher (quote Category.id) (getName id-name)
    }
  where
    buildMatcher : Name → Maybe Name → Name → Bool
    buildMatcher n = maybe (λ m x → n == x ∨ m == x) (n ==_)

:id′ : Term
:id′ = quote :id ⟨ con ⟩ []

∥_∥′ : Term → Term
∥_∥′ t = quote ∥_∥ ⟨ con ⟩ (t ⟨∷⟩ [])

module _ (names : CategoryNames) where
  open CategoryNames names

  :∘′ : List (Arg Term) → Term
  E′ : Term → Term

  :∘′ (x ⟨∷⟩ y ⟨∷⟩ []) = quote _:∘_ ⟨ con ⟩ E′ x ⟨∷⟩ E′ y ⟨∷⟩ []
  :∘′ (x ∷ xs)          = :∘′ xs
  :∘′ _                 = unknown

  E′ t@(def n xs) = if is-∘ n
    then :∘′ xs
    else if is-id n
      then :id′
      else ∥ t ∥′
  E′ t@(con n xs) = if is-∘ n
    then :∘′ xs
    else if is-id n
     then :id′
     else ∥ t ∥′
  E′ t = ∥ t ∥′

constructSoln : Term → CategoryNames → Term → Term → Term
constructSoln cat names lhs rhs =
  quote Category.Equiv.trans ⟨ def ⟩ 2 ⋯⟅∷⟆ cat ⟨∷⟩
  (quote Category.Equiv.sym ⟨ def ⟩ 2 ⋯⟅∷⟆ cat ⟨∷⟩
     (quote ⟦e⟧N≈⟦e⟧ ⟨ def ⟩ 2 ⋯⟅∷⟆ cat ⟨∷⟩ E′ names lhs ⟨∷⟩ []) ⟨∷⟩ [])
  ⟨∷⟩
  (quote ⟦e⟧N≈⟦e⟧ ⟨ def ⟩ 2 ⋯⟅∷⟆ cat ⟨∷⟩ E′ names rhs ⟨∷⟩ []) ⟨∷⟩
  []

macro
  solve : Term → Term → TC _
  solve cat = λ hole → do
    hole′ ← inferType hole >>= normalise
    names ← findCategoryNames cat
    just (lhs , rhs) ← returnTC (getArgs hole′)
      where nothing → typeError (termErr hole′ ∷ [])
    let soln = constructSoln cat names lhs rhs
    unify hole soln

-- Example
module _ {o l e} (C : Category o l e) where
  open Category C
  _ : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      (h ∘ id ∘ g) ∘ f ≈ id ∘ h ∘ (g ∘ f ∘ id)
  _ = solve C

  _ : ∀ {A} {f g h i j : A ⇒ A} →
      id ∘ (f ∘ id ∘ g) ∘ id ∘ (h ∘ id ∘ i) ∘ id ∘ j ≈ f ∘ (g ∘ h) ∘ (i ∘ j)
  _ = solve C
