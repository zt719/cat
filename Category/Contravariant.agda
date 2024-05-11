module Category.Contravariant where

open import Agda.Primitive
open import Data.Equality
open import Category.Category

private variable i j k l : Level

record Contravariant (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category.Category ℂ renaming (_∘_ to _∘ℂ_)
  open Category.Category.Category 𝔻 renaming (_∘_ to _∘𝔻_)
  field
    map₀ : obj ℂ → obj 𝔻
    map₁ : {a b : obj ℂ} → hom ℂ a b → hom 𝔻 (map₀ b) (map₀ a)
    
    map-id : {a : obj ℂ} → map₁ (id ℂ {a}) ≡ id 𝔻 {map₀ a}
    map-∘  : {a b c : obj ℂ} {f : hom ℂ b c} {g : hom ℂ a b}
      → map₁ (f ∘ℂ g) ≡ map₁ g ∘𝔻 map₁ f
open Contravariant
