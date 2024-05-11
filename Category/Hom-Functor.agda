module Category.Hom-Functor where

open import Agda.Primitive
open import Data.Equality
open import Data.Function
open import Data.Sigma
open import Category.Category
open import Category.Functor
open import Category.Contravariant
open import Category.Invariant
open import Category.Bifunctor

private variable i j : Level

hom[_,-] : (a : Category.obj SET) → Functor SET SET
hom[ a ,-]
  = record
  { map₀ = λ x → a → x
  ; map₁ = _→∘_
  ; map-id = refl
  ; map-∘ = refl
  }

hom[-,_] : (a : Category.obj SET) → Contravariant SET SET
hom[-, a ]
  = record
  { map₀ = λ x → x → a
  ; map₁ = λ f g → g →∘ f
  ; map-id = refl
  ; map-∘ = refl
  }

hom[-,=] : Bifunctor (SET op) SET SET
hom[-,=]
  = record
  { bimap₀ = λ x y → x → y
  ; bimap₁ = λ f g h → g →∘ (h →∘ f)
  ; bimap-id = refl
  ; bimap-∘ = refl
  }

hom[-,-] : Invariant SET SET
hom[-,-]
  = record
  { map₀ = λ x → x → x
  ; map₁ = λ ab ba aa → ab →∘ (aa →∘ ba)
  ; map-id = refl
  ; map-∘ = refl
  }
