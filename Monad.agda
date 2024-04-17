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
    μ : NT (func-trans T T) T
open Monad    
    
