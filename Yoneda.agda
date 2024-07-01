module Yoneda where

open import Base
open import Category
open import Functor
open import Natural-Transformation

open Category.Category
open Functor.Functor

LSC : Set (lsuc i)
LSC {i = i} = Category {i} {lzero}

private variable ℂ : LSC {i}

Hom[_,-] : (X : obj ℂ)
  → ℂ ⇒ SET
Hom[_,-] {ℂ = ℂ} X = record
  { map₀ = λ Y → hom ℂ X Y
  ; map₁ = _∘_ ℂ
  ; map-id = ext (left-id ℂ)
  ; map-∘ = λ{ {f = f} {g = g} → ext (assoc ℂ f g) }
  }


φ : {X  : obj ℂ} {G : ℂ ⇒ SET}
  → map₀ G X → Hom[ X ,-] ~ G
φ {G = G} x = record
  { component = λ f → map₁ G f x
  ; commute = ext λ{ f → {!!}}
  }


ψ : {X : obj ℂ} {G : ℂ ⇒ SET}
  → Hom[ X ,-] ~ G → map₀ G X
ψ {ℂ = ℂ} {X = X} record { component = α }
  = α {a = X} (id ℂ)

ψ∘φ : {X : obj ℂ} {G : ℂ ⇒ SET}
  → (e : map₀ G X) → ψ {X = X} (φ {X = X} {G = G} e) ≡ e
ψ∘φ e = {!!}

Hom[-,_] : (X : obj ℂ)
  → (ℂ op) ⇒ SET
Hom[-,_] {ℂ = ℂ} X = record
  { map₀ = λ Y → hom ℂ Y X
  ; map₁ = flip (_∘_ ℂ)
  ; map-id = ext (λ f → ≡-sym (right-id ℂ f))
  ; map-∘ = λ{ {f = f} {g = g} → ext (λ h → ≡-sym (assoc ℂ h g f)) }
  }

φ' : {X : obj ℂ} {G : (ℂ op) ⇒ SET}
  → map₀ G X → Hom[-, X ] ~ G
φ' {G = G} x = record
  { component = λ f → map₁ G f x
  ; commute = {!!} }

ψ' : {X : obj ℂ} {G : (ℂ op) ⇒ SET}
  → Hom[-, X ] ~ G → map₀ G X
ψ' {ℂ = ℂ} {X = X} record { component = α }
  = α {a = X} (id ℂ)
