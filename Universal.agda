module Universal where

open import Base
open import Category

private variable i j : Level

record Initial (𝓒 : Category {i} {j}) : UU (i ⊔ j) where
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
  (A B : Category.obj 𝓒) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    to : hom A B
    from : hom B A
    from∘to : id {A} ≡ from ∘ to
    to∘from : id {B} ≡ to ∘ from
open Isomorphism

record Product {𝓒 : Category {i} {j}}
  (A B : Category.obj 𝓒) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    product : obj
    fst : hom product A
    snd : hom product B
open Product

record Coproduct {𝓒 : Category {i} {j}}
  (A B : Category.obj 𝓒) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    coproduct : obj
    inj₁ : hom A coproduct
    inj₂ : hom B coproduct
open Coproduct
    
  
  

