module Universal where

open import Base
open import Category
open import Functor

open Category.Category

record Isomorphism {ℂ : Category {i} {j}}
  (a b : obj ℂ) : Set (i ⊔ j) where
  private _∘ℂ_ = Category._∘_ ℂ
  field
    to : hom ℂ a b
    from : hom ℂ b a
    from∘to : from ∘ℂ to ≡ id ℂ {a}
    to∘from : id ℂ {b} ≡ to ∘ℂ from


record Initial (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  field
    φ : obj ℂ
    absurd : (a : obj ℂ) → hom ℂ φ a

0-as-initial-PREORDER : Initial PREORDER
0-as-initial-PREORDER
  = record { φ = zero ; absurd = λ n → z≤n }

⊥-as-initial-SET : Initial SET
⊥-as-initial-SET = record { φ = ⊥ ; absurd = λ a () }

𝟘-as-initial-CAT : Initial CAT
𝟘-as-initial-CAT
  = record { φ = 𝟘 ; absurd = λ a → record { map₀ = λ () ; map₁ = λ () ; map-id = λ {} ; map-∘ = λ {} }}

record Terminal (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  field
    ＊ : obj ℂ
    unit : (a : obj ℂ) → hom ℂ a ＊

0-as-terminal-PREORDER-op : Terminal (PREORDER op)
0-as-terminal-PREORDER-op
  = record
  { ＊ = 0
  ; unit = λ n → z≤n {n}
  }

⊥-as-terminal-SET-op : Terminal (SET op)
⊥-as-terminal-SET-op = record { ＊ = ⊥ ; unit = λ _ () }

⊤-as-terminal-SET : Terminal SET
⊤-as-terminal-SET = record { ＊ = ⊤ ; unit = λ _ _ → tt }

𝟙-as-terminal-CAT : Terminal CAT
𝟙-as-terminal-CAT
  = record
  { ＊ = 𝟙
  ; unit = λ a → record { map₀ = (λ x → tt); map₁ = (λ x → -tt→); map-id = refl; map-∘ = refl }
  }

record Product {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  field
    product : obj ℂ
    prjˡ : hom ℂ product a
    prjʳ : hom ℂ product b

×-as-product-SET : (A B : Category.obj SET) → Product {ℂ = SET} A B
×-as-product-SET A B
  = record { product = A × B ; prjˡ = proj₁ ; prjʳ = proj₂ }

record Coproduct {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  field
    coproduct : obj ℂ
    injˡ : hom ℂ a coproduct
    injʳ : hom ℂ b coproduct

⊎-as-coproduct-SET : (A B : Category.obj SET) → Coproduct {ℂ = SET} A B
⊎-as-coproduct-SET A B
  = record { coproduct = A ⊎ B ; injˡ = inj₁ ; injʳ = inj₂ }

record Equilizer {i j} {ℂ : Category {i} {j}} {a b : obj ℂ} (f g : hom ℂ a b) : Set (i ⊔ j) where
  private _∘ℂ_ = Category._∘_ ℂ
  field
    eq : obj ℂ
    e  : hom ℂ eq a
    commute : f ∘ℂ e ≡ g ∘ℂ e

record Exponential {ℂ : Category {i} {j}} (a b : obj ℂ) : Set (i ⊔ j) where
  open Product
  field
    exponential : obj ℂ
    _×Y : (x : obj ℂ) → Product {ℂ = ℂ} x b
    eval : (x : obj ℂ) → hom ℂ (product (x ×Y)) x

→-as-exponential-SET : (A B : obj SET) → Exponential {ℂ = SET} A B
→-as-exponential-SET A B
  = record
  { exponential = A → B
  ; _×Y = λ X → ×-as-product-SET X B
  ; eval = λ X X×B → proj₁ X×B
  }
