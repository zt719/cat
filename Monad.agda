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
    rule1 : μ <~∘ (μ <~∘⇐ T) ≡ μ <~∘ {!T ⇐∘<~ μ!}
    rule2 : μ <~∘ (T ⇐∘<~ η) ≡ {!identity-nt T!}
    rule3 : μ <~∘ (η <~∘⇐ T) ≡ {!identity-nt T!}
open Monad    
    
