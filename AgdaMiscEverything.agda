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

import Algorithms.List.Sort.Quick.Properties

------------------------------------------------------------------------
-- Constructive mathematics

-- Definitions of Axioms that are nonconstructive
import Constructive.Axiom

import Constructive.Axiom.Properties

import Constructive.Axiom.Properties.Base

import Constructive.Axiom.Properties.Bool

import Constructive.Axiom.Properties.Transport

-- Combinators for reasoning
import Constructive.Combinators

import Constructive.Common

-- Searchable set
import Constructive.Searchable

------------------------------------------------------------------------
-- Type theory

-- Natural number
import TypeTheory.Nat.Operations

import TypeTheory.Nat.Properties

import TypeTheory.Nat.Instance

-- Homotopy Type Theory
import TypeTheory.HoTT.Base

import TypeTheory.HoTT.Data.Empty.Properties

import TypeTheory.HoTT.Data.Sum.Properties

import TypeTheory.HoTT.Function.Properties

import TypeTheory.HoTT.Relation.Nullary.Negation.Properties

------------------------------------------------------------------------
-- Formal language

import Math.FormalLanguage

------------------------------------------------------------------------
-- Number theory

-- Fibonacci number
import Math.NumberTheory.Fibonacci.Generic

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
