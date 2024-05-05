module Data.Equality where

open import Agda.Primitive
open import Agda.Builtin.Equality public

private variable i j k l m : Level

postulate
  ext : {A : Set i} {B : Set j}
    → {f g : A → B}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

  ext' : {A : Set i} {B : A → Set j}
    → {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

transport : {A : Set i} (B : A → Set j)
  → {x y : A}
  → x ≡ y
  → B x → B y
transport B refl x = x

cong : {A : Set i} {B : Set j} {x₁ x₂ : A}
  → (f : A → B)
  → x₁ ≡ x₂
  → f x₁ ≡ f x₂
cong f refl = refl

cong₂ : {A : Set i} {B : Set j} {C : Set k}
  → {x₁ x₂ : A} {y₁ y₂ : B}
  → (f : A → B → C)
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

cong₃ : {A : Set i} {B : Set j} {C : Set k} {D : Set l}
  → {x₁ x₂ : A} {y₁ y₂ : B} {z₁ z₂ : C}
  → (f : A → B → C → D)
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → z₁ ≡ z₂
  → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

cong₄ : {A : Set i} {B : Set j} {C : Set k} {D : Set l} {E : Set m}
  → {x₁ x₂ : A} {y₁ y₂ : B} {z₁ z₂ : C} {p₁ p₂ : D}
  → (f : A → B → C → D → E)
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → z₁ ≡ z₂
  → p₁ ≡ p₂
  → f x₁ y₁ z₁ p₁ ≡ f x₂ y₂ z₂ p₂
cong₄ f refl refl refl refl = refl

≡-refl : {A : Set i} {x : A}
  → x ≡ x
≡-refl = refl

≡-sym : {A : Set i} {x y : A}
  → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {A : Set i} {x y z : A}
  → y ≡ z → x ≡ y → x ≡ z
≡-trans refl refl = refl

infixl 5 _∙_
_∙_ = ≡-trans

≡-left-id : {A : Set i} {x y : A}
  → (p : x ≡ y)
  → ≡-refl ∙ p ≡ p
≡-left-id refl = refl

≡-right-id : {A : Set i} {x y : A}
  → (p : x ≡ y)
  → p ≡ p ∙ ≡-refl
≡-right-id refl = refl

≡-assoc : {A : Set i} {x y z h : A}
  → (p : z ≡ h) (q : y ≡ z) (r : x ≡ y)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
≡-assoc refl refl refl = refl

