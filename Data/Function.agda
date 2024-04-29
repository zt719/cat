module Data.Function where

open import Agda.Primitive
open import Data.Equality

private variable i j k l : Level

→-refl : {A : Set i} → A → A
→-refl a = a

→-trans : {A : Set i} {B : Set j} {C : Set k}
  → (B → C) → (A → B) → (A → C)
→-trans f g x = f (g x)

_→∘_ = →-trans

→-left-id : {A : Set i} {B : Set j}
  → (f : A → B)
  → →-refl →∘ f ≡ f
→-left-id f = refl

→-right-id : {A : Set i} {B : Set j}
    (f : A → B)
  → f ≡ f →∘ →-refl
→-right-id f = refl

→-assoc : {A : Set i} {B : Set j} {C : Set k} {D : Set l}
    (f : C → D) (g : B → C) (h : A → B)
  → (f →∘ g) →∘ h ≡ f →∘ (g →∘ h)
→-assoc f g h = refl
