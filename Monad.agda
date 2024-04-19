{-# OPTIONS --allow-unsolved-metas #-}

module Monad where

open import Base
open import Category
open import Functor
open import Natural-Transformation

private variable i j : Level

record Monad (𝓒 : Category {i} {j}) : UU (i ⊔ j) where
  field
    T : Endofunctor 𝓒
    η : NT (identity-functor 𝓒) T
    μ : NT (T ⇐ T) T
    rule1 : μ ~ (μ ~hl T) ≡ μ ~ {!T ~hr μ!}
    rule2 : μ ~ (T ~hr η) ≡ {!identity-nt T!}
    rule3 : μ ~ (η ~hl T) ≡ {!identity-nt T!}
open Monad    
    
