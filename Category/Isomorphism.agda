module Category.Isomorphism where

open import Agda.Primitive
open import Data.Equality
open import Category.Category

private variable i j : Level

record Isomorphism {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    to : hom a b
    from : hom b a
    from∘to : from ∘ to ≡ id {a}
    to∘from : id {b} ≡ to ∘ from
open Isomorphism
