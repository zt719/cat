module Data.Heterogeneous-Equality where

open import Agda.Primitive
open import Data.Equality
open import Data.Nat

private variable i j k l : Level

infix 4 _≅_

data _≅_ {A : Set i} (x : A) : {B : Set j} → B → Set i where
   refl : x ≅ x

≅-to-≡ : {x y : Set i} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

≡-to-≅ : {x y : Set i} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

≅-cong₂ : ∀ {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set k} {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
≅-cong₂ f refl refl = refl

postulate P : ℕ → Set

record Silly : Set (lsuc lzero) where
 constructor _#_#_
 field
  n : ℕ
  pn : P n
  f : Set → ℕ

open Silly

SillyEq : ∀ s t → n s ≡ n t → pn s ≅ pn t → f s ≡ f t → s ≡ t
SillyEq (n₁ # pn₁ # f₁) (.n₁ # .pn₁ # .f₁) refl refl refl = refl
