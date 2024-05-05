module Category.Universal where

open import Agda.Primitive
open import Data.Equality
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Category.Category
open import Category.Functor

private variable i j : Level

-- TODO : Add uniqueness
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

record Terminal (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    ＊ : obj
    unit : (a : obj) → hom a ＊
open Terminal

0-as-terminal-PREORDER-op : Terminal (PREORDER op)
0-as-terminal-PREORDER-op = record { ＊ = 0 ; unit = λ n → z≤n }

⊥-as-terminal-SET-op : Terminal (SET op)
⊥-as-terminal-SET-op = record { ＊ = ⊥ ; unit = λ a () }

𝟙-as-terminal-CAT : Terminal CAT
𝟙-as-terminal-CAT
  = record
  { ＊ = 𝟙
  ; unit = λ a → mkFunctor (λ x → tt) (λ x → -tt→) refl refl
  }

record Isomorphism {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  field
    to : hom a b
    from : hom b a
    from∘to : from ∘ to ≡ id {a}
    to∘from : id {b} ≡ to ∘ from
open Isomorphism

_≅_ = Isomorphism

record Product {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  constructor _ẋ_
  open Category.Category.Category ℂ
  field
    product : obj
    fst : hom product a
    snd : hom product b
open Product

record Coproduct {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  constructor _∔_
  open Category.Category.Category ℂ
  field
    coproduct : obj
    inj₁ : hom a coproduct
    inj₂ : hom b coproduct
open Coproduct
