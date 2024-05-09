module Category.Coproduct where

open import Agda.Primitive
open import Category.Category
open import Data.Sum

private variable i j : Level

record Coproduct {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    coproduct : obj
    injˡ : hom a coproduct
    injʳ : hom b coproduct
open Coproduct

+-as-coproduct-SET : (A B : Category.obj SET) → Coproduct {ℂ = SET} A B
+-as-coproduct-SET A B
  = record { coproduct = A + B ; injˡ = inj₁ ; injʳ = inj₂ }
