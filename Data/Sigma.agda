module Data.Sigma where

open import Agda.Primitive
open import Agda.Builtin.Sigma public
open import Data.Equality

private variable i j : Level

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∶ A ] Bx

_×_ : Set i → Set j → Set (i ⊔ j)
A × B = Σ A (λ _ → B)
