module Monad where

open import Base
open import Category
open import Functor
open import Natural-Transformation

-- TODO : Add commutative diagrams
record Monad (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  field
    T : Endofunctor ℂ
    η : (identity-functor ℂ) ~ T
    μ : (T ⇐∘= T) ~ T
open Monad    
