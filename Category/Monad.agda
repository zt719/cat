module Category.Monad where

open import Agda.Primitive
open import Category.Category
open import Category.Functor
open import Category.Natural-Transformation

private variable i j : Level

-- TODO : Add commutative diagrams
record Monad (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  field
    T : Endofunctor ℂ
    η : (identity-functor ℂ) ~ T
    μ : (T ⇐∘= T) ~ T
open Monad    
