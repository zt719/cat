module Data.Sum where

open import Agda.Primitive

private variable i j k : Level

infixr 1 _+_

data _+_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inj₁ : (x : A) → A + B
  inj₂ : (y : B) → A + B



[_,_] : {A : Set i} {B : Set i} {C : A + B → Set k} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A + B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y
