module Equilizer where

open import Base
open import Category
open Category.Category

record Equilizer {i j} {ℂ : Category {i} {j}} {a b : obj ℂ} (f g : hom ℂ a b) : Set (i ⊔ j) where
  field
    eq : obj ℂ
    e  : hom ℂ eq a
    commute : (_∘_) ℂ f e  ≡ (_∘_) ℂ g e
open Equilizer
    
