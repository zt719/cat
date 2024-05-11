module Category.Adjunction where

open import Agda.Primitive
open import Category.Category
open import Category.Functor
open import Category.Natural-Transformation

private variable i j k l : Level

record Adjunction {ℂ : Category {i} {j}} {𝔻 : Category {k} {l}}
  (L : 𝔻 ⇒ ℂ) (R : ℂ ⇒ 𝔻) : Set (i ⊔ j ⊔ k ⊔ l) where
  field
    unit : (id-functor 𝔻) ~ (R ⇒∘ L)
    counit : (L ⇒∘ R) ~ (id-functor ℂ)
    -- rules -- 
open Adjunction

_⊣_ = Adjunction

