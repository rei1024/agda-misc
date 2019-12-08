module Experiment.Expr.Expr where

open import Data.Fin
open import Data.Empty
open import Level
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.List as List hiding (or; and)

data Expr {v} (V : Set v) : Set v where
  var : V -> Expr V
  or and : Expr V -> Expr V -> Expr V
  neg : Expr V -> Expr V

foldExpr : ∀ {a v} {V : Set v} {A : Set a} →
           (V → A) → (A → A → A) → (A → A → A) → (A → A) →
           Expr V → A
foldExpr v o a n (var v′)    = v v′
foldExpr v o a n (or e₁ e₂)  = o (foldExpr v o a n e₁) (foldExpr v o a n e₂)
foldExpr v o a n (and e₁ e₂) = a (foldExpr v o a n e₁) (foldExpr v o a n e₂)
foldExpr v o a n (neg e)     = n (foldExpr v o a n e)

evalExpr : ∀ {v} {V : Set v} → (V → Bool) → Expr V → Bool
evalExpr v = foldExpr v _∨_ _∧_ not

data Sign : Set where
  pos : Sign
  neg : Sign

Literal : ∀ {a} → Set a → Set a
Literal V = Sign × V

data NNF {v} (V : Set v) : Set v where
  lit : Literal V → NNF V
  and or : NNF V → NNF V → NNF V


data GExpr {v t₁ t₂ tₙ} (T₁ : Set t₁) (T₂ : Set t₂) (Tₙ : Set tₙ) (V : Set v)
  : Set (v ⊔ t₁ ⊔ t₂ ⊔ tₙ) where
  var : (v : V) → GExpr T₁ T₂ Tₙ V
  op₁ : T₁ → (e : GExpr T₁ T₂ Tₙ V) → GExpr T₁ T₂ Tₙ V
  op₂ : T₂ → (e₁ e₂ :  GExpr T₁ T₂ Tₙ V) → GExpr T₁ T₂ Tₙ V
  opₙ : Tₙ → (es : List (GExpr T₁ T₂ Tₙ V)) → GExpr T₁ T₂ Tₙ V

data AndOr : Set where
  and : AndOr
  or : AndOr

data Neg : Set where
  neg : Neg

ExprAndOrNeg : ℕ → Set
ExprAndOrNeg n = GExpr AndOr Neg ⊥ (Fin n)

evalAndOr : AndOr → Bool → Bool → Bool
evalAndOr and = _∧_
evalAndOr or  = _∨_

module _ {v t₁ t₂ tₙ a} {V : Set v} {T₁ : Set t₁}
         {T₂ : Set t₂} {Tₙ : Set tₙ} {A : Set a}
         (var* : V → A) (op₁* : T₁ → A → A) (op₂* : T₂ → A → A → A)
         (opₙ* : Tₙ → List A → A) where
  foldGExpr : GExpr T₁ T₂ Tₙ V → A
  foldGExpr (var v) = var* v
  foldGExpr (op₁ t₁ e) = op₁* t₁ (foldGExpr e)
  foldGExpr (op₂ t₂ e₁ e₂) = op₂* t₂ (foldGExpr e₁) (foldGExpr e₂)
  foldGExpr (opₙ tₙ es) = opₙ* tₙ (List.map foldGExpr es)
