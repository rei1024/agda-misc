------------------------------------------------------------------------
-- agda-misc
-- All modules
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module AgdaMiscEverything where

------------------------------------------------------------------------
-- Algorithms

-- Insertion sort
import Algorithms.List.Sort.Insertion

import Algorithms.List.Sort.Insertion.Properties

-- Quicksort
import Algorithms.List.Sort.Quick

------------------------------------------------------------------------
-- Logic

-- Constructive mathematics
import Math.Logic.NonConstructiveAxiom

import Math.Logic.Constructive

import Math.Logic.NonConstructiveAxiom.Properties

-- Natural number
import Math.Logic.Nat.Operations

import Math.Logic.Nat.Properties

import Math.Logic.Nat.Instance

------------------------------------------------------------------------
-- Formal language

import Math.FormalLanguage

------------------------------------------------------------------------
-- Number theory

-- Fibonacci number
import Math.NumberTheory.Fibonacci.Generic

-- DEPRECATED
import Math.NumberTheory.Fibonacci.Generic.Propositional

import Math.NumberTheory.Fibonacci.Nat

import Math.NumberTheory.Fibonacci.Nat.Properties

-- Summation
import Math.NumberTheory.Summation.Generic

import Math.NumberTheory.Summation.Generic.Properties

import Math.NumberTheory.Summation.Nat

import Math.NumberTheory.Summation.Nat.Properties

-- Product
import Math.NumberTheory.Product.Generic

import Math.NumberTheory.Product.Generic.Properties

import Math.NumberTheory.Product.Nat

import Math.NumberTheory.Product.Nat.Properties

------------------------------------------------------------------------
-- Googology

import Math.Googology.Function

import Math.Googology.Function.Properties
