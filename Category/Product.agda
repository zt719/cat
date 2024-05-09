module Category.Product where

open import Agda.Primitive
open import Data.Sigma
open import Category.Category

private variable i j : Level

record Product {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    product : obj
    prjˡ : hom product a
    prjʳ : hom product b
open Product

×-as-product-SET : (A B : Category.obj SET) → Product {ℂ = SET} A B
×-as-product-SET A B
  = record { product = A × B ; prjˡ = fst ; prjʳ = snd }
