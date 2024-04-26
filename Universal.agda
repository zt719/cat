module Universal where

open import Base
open import Category

private variable i j : Level


-- TODO : Add uniqueness
record Initial (𝓒 : Category {i} {j}) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    φ : obj
    absurd : (a : obj) → hom φ a
open Initial

0-as-initial-preorder : Initial ℕ-≤-preorder
0-as-initial-preorder
  = record { φ = zero ; absurd = λ n → z≤n }

𝟘-as-initial-SET : Initial SET
𝟘-as-initial-SET = record { φ = 𝟘 ; absurd = λ a () }

record Terminal (𝓒 : Category {i} {j}) : UU (i ⊔ j) where
  open Category.Category 𝓒
  field
    ＊ : obj
    unit : (a : obj) → hom a ＊
open Terminal

0-as-terminal-preorder-op : Terminal (ℕ-≤-preorder op)
0-as-terminal-preorder-op = record { ＊ = 0 ; unit = λ n → z≤n }

𝟘-as-terminal-SET-op : Terminal (SET op)
𝟘-as-terminal-SET-op = record { ＊ = 𝟘 ; unit = λ a () }

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

record Product {𝓒 : Category {i} {j}}
  (a b : Category.obj 𝓒) : UU (i ⊔ j) where
  constructor _ẋ_
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
