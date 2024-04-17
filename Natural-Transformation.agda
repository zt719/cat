module Natural-Transformation where

open import Base
open import Category
open import Functor

private variable i j k l : Level

record Natural-Transformation {𝓒 : Category {i} {j}} {𝓓 : Category {k} {l}}
  (F G : Functor 𝓒 𝓓) : UU (i ⊔ j ⊔ l ⊔ k) where
  open Category.Category
  open Functor.Functor
  field
    α : (A : obj 𝓒) → hom 𝓓 (map-obj F A) (map-obj G A)
    NTL : {A B : obj 𝓒} → (f : hom 𝓒 A B)
      → (_∘_) 𝓓 (α B) (map-morph F f) ≡ (_∘_) 𝓓 (map-morph G f) (α A)
open Natural-Transformation

head : {A : UU i}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-NT : Natural-Transformation List-as-Functor Maybe-as-Functor
head-as-NT = record
  { α = λ A → head
  ; NTL = λ f → ext (λ{ [] → refl ; (a ∷ as) → refl })
  }
