module Category.Monad where

open import Agda.Primitive
open import Data.Equality
open import Category.Category
open import Category.Functor
open import Category.Natural-Transformation

private variable i j k l : Level

-- TODO : Add commutative diagrams
record Monad (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category.Category ℂ using (obj)
  field
    T : Endofunctor ℂ
    η : id-functor ℂ ~ T
    μ : (T ⇒∘ T) ~ T

--    rule1 : (μ ~∘ (μ ~hl T)) ≡ (μ ~∘ {!T!})
open Monad    
