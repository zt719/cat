module Category.Initial where

open import Agda.Primitive
open import Category.Category
open import Category.Functor
open import Data.Nat
open import Data.Empty

private variable i j : Level


record Initial (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    φ : obj
    absurd : (a : obj) → hom φ a
open Initial

0-as-initial-PREORDER : Initial PREORDER
0-as-initial-PREORDER
  = record { φ = zero ; absurd = λ n → z≤n }

⊥-as-initial-SET : Initial SET
⊥-as-initial-SET = record { φ = ⊥ ; absurd = λ a () }

𝟘-as-initial-CAT : Initial CAT
𝟘-as-initial-CAT
  = record { φ = 𝟘 ; absurd = λ a → mkFunctor (λ ()) (λ ()) (λ {}) (λ {}) }
