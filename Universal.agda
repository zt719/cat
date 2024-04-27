module Universal where

open import Base
open import Category


-- TODO : Add uniqueness
record Initial (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category ℂ
  field
    φ : obj
    absurd : (a : obj) → hom φ a
open Initial

0-as-initial-preorder : Initial ℕ-≤-preorder
0-as-initial-preorder
  = record { φ = zero ; absurd = λ n → z≤n }

𝟘-as-initial-SET : Initial SET
𝟘-as-initial-SET = record { φ = ⊥ ; absurd = λ a () }

record Terminal (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  open Category.Category ℂ
  field
    ＊ : obj
    unit : (a : obj) → hom a ＊
open Terminal

0-as-terminal-preorder-op : Terminal (ℕ-≤-preorder op)
0-as-terminal-preorder-op = record { ＊ = 0 ; unit = λ n → z≤n }

𝟘-as-terminal-SET-op : Terminal (SET op)
𝟘-as-terminal-SET-op = record { ＊ = ⊥ ; unit = λ a () }

record Isomorphism {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  open Category.Category ℂ
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
  open Category.Category ℂ
  field
    product : obj
    fst : hom product a
    snd : hom product b
open Product

record Coproduct {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  constructor _∔_
  open Category.Category ℂ
  field
    coproduct : obj
    inj₁ : hom a coproduct
    inj₂ : hom b coproduct
open Coproduct
