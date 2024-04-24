module Universal where

open import Base
open import Category

private variable i j : Level

record Initial (𝓒 : Category {i} {j}) : UU (i ⊔ j) where
  constructor initial
  open Category.Category 𝓒
  field
    initial : obj
    absurd : (a : obj) → hom initial a
open Initial

record Terminal (𝓒 : Category {i} {j}) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    terminal : obj
    unit : (a : obj) → hom a terminal
open Terminal

record Isomorphism {𝓒 : Category {i} {j}}
  (a b : Category.obj 𝓒) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    to : hom a b
    from : hom b a
    from∘to : from ∘ to ≡ id {a}
    to∘from : id {b} ≡ to ∘ from
open Isomorphism

_≅_ = Isomorphism

-- TODO : add constraints on Product and Coproduct --
record Product {𝓒 : Category {i} {j}}
  (a b : Category.obj 𝓒) : UU (i ⊔ j) where
  constructor _×_
  open Category.Category 𝓒
  field
    product : obj
    fst : hom product a
    snd : hom product b
open Product

record Coproduct {𝓒 : Category {i} {j}}
  (a b : Category.obj 𝓒) : UU (i ⊔ j) where
  constructor _∔_
  open Category.Category 𝓒
  field
    coproduct : obj
    inj₁ : hom a coproduct
    inj₂ : hom b coproduct
open Coproduct
