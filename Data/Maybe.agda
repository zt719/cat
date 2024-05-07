module Data.Maybe where

open import Agda.Primitive
open import Data.Equality
open import Data.Function
open import Agda.Builtin.Maybe public

private variable i j k : Level

maybe-map₁ : {A : Set i} {B : Set j}
  → (A → B)
  → Maybe A → Maybe B
maybe-map₁ f (just a) = just (f a)
maybe-map₁ f nothing  = nothing

maybe-map₁-id' : {A : Set i}
  → (x : Maybe A)
  → maybe-map₁ →-refl x ≡ →-refl x
maybe-map₁-id' (just x) = refl
maybe-map₁-id' nothing  = refl

maybe-map₁-∘' : {A : Set i} {B : Set j} {C : Set k}
  → {f : B → C} {g : A → B}
  → (x : Maybe A)
  → maybe-map₁ (f →∘ g) x ≡ (maybe-map₁ f →∘ maybe-map₁ g) x
maybe-map₁-∘' (just x) = refl
maybe-map₁-∘' nothing = refl
