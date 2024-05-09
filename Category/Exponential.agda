module Category.Exponential where

open import Agda.Primitive
open import Data.Sigma
open import Category.Category
open import Category.Product

private variable i j : Level

record Exponential {ℂ : Category {i} {j}} (a b : Category.obj ℂ) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    exponential : obj
    _×Y : (x : obj) → Product {ℂ = ℂ} x b
    eval : (x : obj) → hom (Product.product (x ×Y)) x
open Exponential

→-as-exponential-SET : (A B : Category.obj SET) → Exponential {ℂ = SET} A B
→-as-exponential-SET A B
  = record
  { exponential = A → B
  ; _×Y = λ X → ×-as-product-SET X B
  ; eval = λ X X×B → fst X×B
  }
