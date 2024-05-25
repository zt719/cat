module Yoneda where

open import Base
open import Category
open import Functor
open import Natural-Transformation

open Category.Category

Hom-functor : Bifunctor (SET op) SET SET
Hom-functor = record
  { bimap₀ = λ a b → a → b
  ; bimap₁ = λ f g h → g →∘ h →∘ f
  ; bimap-id = refl
  ; bimap-∘ = refl
  }

Hom[_,+] : (a : obj SET) → SET ⇒ SET
Hom[ a ,+] = record
  { map₀ = λ b → a → b
  ; map₁ = λ f g → f →∘ g
  ; map-id = refl
  ; map-∘ = refl
  }

Hom[-,_] : (b : obj SET) → (SET op) ⇒ SET
Hom[-, b ] = record
  { map₀ = λ a → a → b
  ; map₁ = λ f g → g →∘ f
  ; map-id = refl
  ; map-∘ = refl
  }

Presheaf : Set (lsuc lzero)
Presheaf = (SET op) ⇒ SET

Hom-is-Presheaf : (A : obj SET) → Presheaf
Hom-is-Presheaf A = Hom[-, A ]

{-
YE : SET ⇒ [ (SET op) , SET ]
YE = record
  { map₀ = λ A → Hom[-, A ]
  ; map₁ = λ f → record
    { component = λ g → f →∘ g
    ; commute = ext (λ x → refl)
    }
  ; map-id = {!!}
  ; map-∘ = {!!}
  }
-}
