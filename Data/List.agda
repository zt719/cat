module Data.List where

open import Agda.Primitive
open import Data.Equality
open import Data.Function
open import Agda.Builtin.List public

private variable i j k : Level

++-refl : {A : Set i}
  → List A
++-refl = []

_++_ : {A : Set i}
  → List A → List A → List A
[] ++ bs = bs
(x ∷ as) ++ bs = x ∷ (as ++ bs)

++-trans = _++_

++-left-id : {A : Set i}
  → (l : List A)
  → ++-refl ++ l ≡ l
++-left-id l = refl

++-right-id : {A : Set i}
  → (l : List A)
  → l ≡ l ++ ++-refl
++-right-id []      = refl
++-right-id (x ∷ l) = cong (x ∷_) (++-right-id l)

++-assoc : {A : Set i}
  → (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

list-map₁ : {A : Set i} {B : Set j}
  → (A → B)
  → List A → List B
list-map₁ f [] = []
list-map₁ f (a ∷ as) = f a ∷ list-map₁ f as

list-map-id' : {A : Set i}
  → (as : List A)
  → list-map₁ →-refl as ≡ →-refl as
list-map-id' [] = refl
list-map-id' (l₇ ∷ as) = cong (→-refl l₇ ∷_) (list-map-id' as)

list-map-∘' : {A : Set i} {B : Set j} {C : Set k}
  → {f : B → C} {g : A → B}
  → (as : List A)
  → list-map₁ (f →∘ g) as ≡ (list-map₁ f →∘ list-map₁ g) as
list-map-∘' [] = refl
list-map-∘' {f = f} {g = g} (a ∷ as) = cong (→-trans f g a ∷_) (list-map-∘' as)

list-map₁-++ : {A : Set i} {B : Set i}
  → (f : A → B)
  → (as bs : List A)
  → list-map₁ f (as ++ bs) ≡ list-map₁ f as ++ list-map₁ f bs
list-map₁-++ f [] bs = refl
list-map₁-++ f (x ∷ as) bs = cong (f x ∷_) (list-map₁-++ f as bs)

