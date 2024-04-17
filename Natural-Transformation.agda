module Natural-Transformation where

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




