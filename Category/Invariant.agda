module Category.Invariant where

open import Agda.Primitive
open import Data.Equality
open import Category.Category

private variable i j k l : Level

record Invariant (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category.Category ℂ renaming (_∘_ to _∘ℂ_)
  open Category.Category.Category 𝔻 renaming (_∘_ to _∘𝔻_)
  field
    map₀ : obj ℂ → obj 𝔻
    map₁ : {a b : obj ℂ} → hom ℂ a b → hom ℂ b a → hom 𝔻 (map₀ a) (map₀ b)
    
    map-id : {a : obj ℂ} → map₁ (id ℂ {a}) (id ℂ {a}) ≡ id 𝔻 {map₀ a}
    map-∘  : {a b c : obj ℂ} {f1 : hom ℂ b c} {f2 : hom ℂ c b} {g1 : hom ℂ a b} {g2 : hom ℂ b a}
      → map₁ (f1 ∘ℂ g1) (g2 ∘ℂ f2) ≡ map₁ f1 f2 ∘𝔻 map₁ g1 g2
open Invariant
