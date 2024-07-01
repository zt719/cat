module Universal where

open import Base
open import Category
open import Functor

open Category.Category

{-
record Isomorphism {ℂ : Category {i} {j}}
  (a b : obj ℂ) : Set (i ⊔ j) where
  private _∘ℂ_ = Category._∘_ ℂ
  field
    to : hom ℂ a b
    from : hom ℂ b a
    from∘to : from ∘ℂ to ≡ id ℂ {a}
    to∘from : id ℂ {b} ≡ to ∘ℂ from
-}

record Initial (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  field
    𝟎 : obj ℂ
    !₀ : {a : obj ℂ} → hom ℂ 𝟎 a

0-as-initial-PREORDER : Initial PREORDER
0-as-initial-PREORDER
  = record { 𝟎 = zero ; !₀ = z≤n }

⊥-as-initial-SET : Initial SET
⊥-as-initial-SET = record { 𝟎 = ⊥ ; !₀ = λ () }

𝟘-as-initial-CAT : Initial CAT
𝟘-as-initial-CAT
  = record { 𝟎 = 𝟘 ; !₀ = record { map₀ = λ () ; map₁ = λ () ; map-id = λ {} ; map-∘ = λ {} }}

record Terminal (ℂ : Category {i} {j}) : Set (i ⊔ j) where
  field
    𝟏 : obj ℂ
    !₁ : {a : obj ℂ} → hom ℂ a 𝟏

0-as-terminal-PREORDER-op : Terminal (PREORDER op)
0-as-terminal-PREORDER-op
  = record
  { 𝟏 = 0
  ; !₁ = z≤n
  }

⊥-as-terminal-SET-op : Terminal (SET op)
⊥-as-terminal-SET-op = record { 𝟏 = ⊥ ; !₁ = λ () }

⊤-as-terminal-SET : Terminal SET
⊤-as-terminal-SET = record { 𝟏 = ⊤ ; !₁ = λ _ → tt }

𝟙-as-terminal-CAT : Terminal CAT
𝟙-as-terminal-CAT
  = record
  { 𝟏 = 𝟙
  ; !₁ = record
    { map₀ = λ _ → tt
    ; map₁ = λ _ → -tt→
    ; map-id = refl
    ; map-∘ = refl
    }
  }

record Product {ℂ : Category {i} {j}}
  (a b : Category.obj ℂ) : Set (i ⊔ j) where
  field
    product : obj ℂ
    projˡ : hom ℂ product a
    projʳ : hom ℂ product b

×-as-product-SET : (A B : Category.obj SET) → Product {ℂ = SET} A B
×-as-product-SET A B
  = record { product = A × B ; projˡ = proj₁ ; projʳ = proj₂ }

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
