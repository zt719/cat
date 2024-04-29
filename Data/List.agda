module Data.List where

open import Agda.Primitive
open import Data.Equality
open import Agda.Builtin.List public

private variable i j : Level

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
