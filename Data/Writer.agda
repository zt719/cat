module Data.Writer where

open Agda.Primitive
open import Data.Sigma
open import Data.List
open import Category.Monoid

private variable i j : Level

open Category.Monoid.Monoid
data Writer {B : Set i} {M : List B} (A : Set j) : Set (i ⊔ j) where
  writer : A × B → Writer A

