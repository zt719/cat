{-# OPTIONS --allow-unsolved-metas #-}

module Functor where

open import Base  
open import Category

open import Agda.Builtin.Maybe

record Functor {i j i' j'} (𝓒 : Category {i}  {j} ) (𝓓 : Category {i'} {j'}) : UU (i ⊔ j ⊔ i' ⊔ j') where
  field
    -- Components --
    map-obj : obj 𝓒 → obj 𝓓
    map-morph : {A B : obj 𝓒} → hom 𝓒 A B → hom 𝓓 (map-obj A) (map-obj B)

    -- Functor Laws --
    preserve-id   : {A : obj 𝓒} → map-morph (id 𝓒 {A}) ≡ id 𝓓 {map-obj A}
    preserve-comp : {A B C : obj 𝓒} → (f : hom 𝓒 B C) → (g : hom 𝓒 A B)
      → map-morph ((_∘_) 𝓒 f g) ≡ (_∘_) 𝓓 (map-morph f) (map-morph g)
open Functor
