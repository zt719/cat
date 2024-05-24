module Adjunction where

open import Base
open import Category
open import Functor
open import Natural-Transformation

record Adjunction {ℂ : Category {i} {j}} {𝔻 : Category {k} {l}}
  (L : 𝔻 ⇒ ℂ) (R : ℂ ⇒ 𝔻) : Set (i ⊔ j ⊔ k ⊔ l) where
  field
    unit : (id-functor 𝔻) ~ (R ⇒∘ L)
    counit : (L ⇒∘ R) ~ (id-functor ℂ)

_⊣_ = Adjunction

