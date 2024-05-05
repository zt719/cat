module Category.Limit where

open import Agda.Primitive
open import Data.Equality
open import Category.Category
open import Category.Functor
open import Category.Natural-Transformation

open Category.Category.Category
open Category.Functor.Functor
open Category.Natural-Transformation.Natural-Transformation

private variable i j k l : Level
private variable 𝕀 : Category {i} {j}
private variable ℂ : Category {k} {l}
private variable D : 𝕀 ⇒ ℂ

Const : obj ℂ → 𝕀 ⇒ ℂ
Const {ℂ = ℂ} x
  = record
  { map₀ = λ _ → x
  ; map₁ = λ _ → id ℂ {x}
  ; map-id = refl
  ; map-∘ = right-id ℂ (id ℂ {x})
  }

record Cone {𝕀 : Category {k} {l}} {ℂ : Category {i} {j}} {D : 𝕀 ⇒ ℂ}
  : Set (i ⊔ j ⊔ k ⊔ l) where
  field
    apex : obj ℂ
    sides : Const apex ~ D
    triangle : {a b : obj 𝕀} (f : hom 𝕀 a b)
      → (_∘_) ℂ (map₁ D f) (component sides {a}) ≡ component sides {b} 
open Cone

private variable cone1 cone2 cone3 : Cone {𝕀 = 𝕀} {ℂ} {D}

record _-Cone→_ {𝕀 : Category {i} {j}} {ℂ : Category {k} {l}}
  {D : 𝕀 ⇒ ℂ} (cone1 cone2 : Cone  {𝕀 = 𝕀} {ℂ = ℂ} {D = D}) : Set (i ⊔ j ⊔ k ⊔ l) where
  field
    -- TODO : Add Uniqueness --
    arr : hom ℂ (apex cone1) (apex cone2)
    commute : (a : obj 𝕀) → (_∘_) ℂ (component (sides cone2) {a}) arr ≡ component (sides cone1) {a}
open _-Cone→_

record Limit {𝕀 : Category {i} {j}} (ℂ : Category {k} {l}) {D : 𝕀 ⇒ ℂ}
  : Set (i ⊔ j ⊔ k ⊔ l) where
  field
    limit : Cone {𝕀 = 𝕀} {ℂ} {D}
    arr : {a : obj 𝕀} {cone : Cone {𝕀 = 𝕀} {ℂ} {D}} (arr : hom ℂ (apex cone) (apex limit))
      → (_∘_) ℂ (component (sides limit) {a}) arr ≡ component (sides cone) {a}
open Limit

terminal-form-by-limit : (ℂ : Category {i} {j}) (c : obj ℂ) {D : 𝟘 ⇒ ℂ}
  → Limit {𝕀 = 𝟘} ℂ {D} 
terminal-form-by-limit ℂ c
  = record
  { limit = record { apex = c ; sides = record { component = λ {} ; commute = λ {} } ; triangle = λ () }
  ; arr = λ {}
  }

{-
product-by-limit : (ℂ : Category {i} {j}) (c : obj ℂ) {D : FIN 2 ⇒ ℂ}
  → Limit {𝕀 = FIN 2} ℂ {D}
product-by-limit ℂ c
  = record
  { limit
    = record
    { apex = c
    ; sides = record { component = λ{ {★} → {!!} ; {𝓲 a} → {!!} } ; commute = {!!} }
    ; triangle = {!!}
    }
  ; arr = {!!}
  }
-}
