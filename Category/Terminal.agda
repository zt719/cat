module Category.Terminal where

open import Agda.Primitive
open import Data.Equality
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sigma
open import Category.Category
open import Category.Functor

private variable i j : Level

record Terminal (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    ＊ : obj
    unit : (a : obj) → hom a ＊
open Terminal

0-as-terminal-PREORDER-op : Terminal (PREORDER op)
0-as-terminal-PREORDER-op
  = record
  { ＊ = 0
  ; unit = λ n → z≤n {n}
  }

⊥-as-terminal-SET-op : Terminal (SET op)
⊥-as-terminal-SET-op = record { ＊ = ⊥ ; unit = λ a () }

⊤-as-terminal-SET : Terminal SET
⊤-as-terminal-SET = record { ＊ = ⊤ ; unit = λ a x → tt }

𝟙-as-terminal-CAT : Terminal CAT
𝟙-as-terminal-CAT
  = record
  { ＊ = 𝟙
  ; unit = λ a → mkFunctor (λ x → tt) (λ x → -tt→) refl refl
  }
