module Category.Bifunctor where

open import Agda.Primitive
open import Data.Equality
open import Category.Category

private variable i j k l m n : Level

record Bifunctor (ℂ : Category {i} {j}) (𝔻 : Category {k} {l})
  (𝔼 : Category {m} {n}) : Set (i ⊔ j ⊔ k ⊔ l ⊔ m ⊔ n) where
  open Category.Category.Category using (obj; hom; id)
  open Category.Category.Category ℂ renaming (_∘_ to _∘ℂ_)
  open Category.Category.Category 𝔻 renaming (_∘_ to _∘𝔻_)
  open Category.Category.Category 𝔼 renaming (_∘_ to _∘𝔼_)  
  field
    bimap₀ : obj ℂ → obj 𝔻 → obj 𝔼
    bimap₁ : {a b : obj ℂ} {c d : obj 𝔻}
      → (f : hom ℂ a b) (g : hom 𝔻 c d)
      → hom 𝔼 (bimap₀ a c) (bimap₀ b d)
    bimap-id : {a : obj ℂ} {b : obj 𝔻}
      → bimap₁ (id ℂ {a}) (id 𝔻 {b}) ≡ id 𝔼 {bimap₀ a b}
    bimap-∘  : {a1 b1 c1 : obj ℂ} {a2 b2 c2 : obj 𝔻}
      → {f1 : hom ℂ b1 c1} {g1 : hom ℂ a1 b1}
      → {f2 : hom 𝔻 b2 c2} {g2 : hom 𝔻 a2 b2}
      → bimap₁ (f1 ∘ℂ g1) (f2 ∘𝔻 g2) ≡ bimap₁ f1 f2 ∘𝔼 bimap₁ g1 g2
open Bifunctor


