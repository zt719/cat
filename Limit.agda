module Limit where

open import Base
open import Category

Index-Cat : ℕ → Category
Index-Cat n
  = record
     { obj = Fin n
     ; hom = λ x x₁ → {!!}
     ; id = {!!}
     ; _∘_ = {!!}
     ; left-id = {!!}
     ; right-id = {!!}
     ; assoc = {!!}
     }

-- record Cone {i j} {𝓒 : Category {i} {j}) (F :
