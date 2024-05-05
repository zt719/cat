module Category.Hom-Functor where

open import Agda.Primitive
open import Data.Equality
open import Data.Sigma
open import Category.Category
open import Category.Functor
open import Category.Product-Category

private variable i j : Level

hom-functor : (ℂ : Category {i} {lzero}) → Functor (PRODUCT ℂ (ℂ op)) SET
hom-functor
  record { obj = obj ; hom = hom ; id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id ; assoc = assoc }
  = record
  { map₀ = λ{ (a , b) → hom a b }
  ; map₁ = {!!}
  ; map-id = {!!}
  ; map-∘ = {!!}
  }
