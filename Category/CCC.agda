module Category.CCC where

open import Agda.Primitive
open import Category.Category
open import Category.Terminal
open import Category.Product
open import Category.Exponential

private variable i j : Level

record _isCCC (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category.Category
  field
    terminal : Terminal ℂ
    products : (a b : obj ℂ) → Product {ℂ = ℂ} a b
    exponentials : (a b : obj ℂ) → Exponential {ℂ = ℂ} a b
open _isCCC

SET-is-CCC : SET isCCC
SET-is-CCC
  = record
  { terminal = ⊤-as-terminal-SET
  ; products = ×-as-product-SET
  ; exponentials = →-as-exponential-SET
  }
