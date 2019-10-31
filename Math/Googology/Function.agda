{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Googology.Function where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.GeneralisedArithmetic
open import Function

-- Ackermann function.
-- ack m n = Ack(m, n)
ack : ℕ → ℕ → ℕ
ack 0       n       = 1 + n
ack (suc m) zero    = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

-- Hyperoperation.
-- H n a b ≡ Hₙ(a, b)
H : ℕ → ℕ → ℕ → ℕ
H 0                     a b       = 1 + b
H 1                     a 0       = a
H 1                     a (suc b) = H 0 a (H 1 a b)
H 2                     a 0       = 0
H 2                     a (suc b) = H 1 a (H 2 a b)
H (suc (suc (suc _)))   a 0       = 1
H (suc n@(suc (suc _))) a (suc b) = H n a (H (suc n) a b)

-- Knuth's up-arrow notation.
-- a ↑[ n ] b =`a ↑ⁿ b`
_↑[_]_ : ℕ → ℕ → ℕ → ℕ
a ↑[ n ] b = H (2 + n) a b

infixr 8 _↑_ _↑↑_ _↑↑↑_ _↑↑↑↑_

-- Exponentiation.
_↑_ : ℕ → ℕ → ℕ
_↑_ a b = a ↑[ 1 ] b

-- Tetration.
_↑↑_ : ℕ → ℕ → ℕ
_↑↑_ a b = a ↑[ 2 ] b

-- Pentation.
_↑↑↑_ : ℕ → ℕ → ℕ
_↑↑↑_ a b = a ↑[ 3 ] b

-- Hexation.
_↑↑↑↑_ : ℕ → ℕ → ℕ
_↑↑↑↑_ a b = a ↑[ 4 ] b

-- Heptation.
_↑↑↑↑↑_ : ℕ → ℕ → ℕ
_↑↑↑↑↑_ a b = a ↑[ 5 ] b

-- Graham's number.
graham's-number : ℕ
graham's-number = go 64 where
  go : ℕ → ℕ
  go 0       = 4
  go (suc n) = 3 ↑[ go n ] 3

-- FGH
FGHℕ[_][_] : ℕ → ℕ → ℕ
FGHℕ[ zero  ][ x ] = suc x
FGHℕ[ suc n ][ x ] = fold x FGHℕ[ n ][_] x

FGHω : ℕ → ℕ
FGHω n = FGHℕ[ n ][ n ]
