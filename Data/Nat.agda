module Data.Nat where

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
open import Data.Equality

infix  4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}
    → zero ≤ n
  s≤s : {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n

≤-refl : {a : ℕ}
  → a ≤ a
≤-refl {zero} = z≤n
≤-refl {suc a} = s≤s ≤-refl

≤-trans : {a b c : ℕ}
  → b ≤ c → a ≤ b → a ≤ c
≤-trans _         z≤n       = z≤n
≤-trans (s≤s b≤c) (s≤s a≤b) = s≤s (≤-trans b≤c a≤b)

≤-left-id : {a b : ℕ}
  → (f : a ≤ b)
  → ≤-trans ≤-refl f ≡ f
≤-left-id z≤n = refl
≤-left-id (s≤s f) = cong s≤s (≤-left-id f)

≤-right-id : {a b : ℕ}
  → (f : a ≤ b)
  → f ≡ ≤-trans f ≤-refl
≤-right-id z≤n = refl
≤-right-id (s≤s f) = cong s≤s (≤-right-id f)

≤-assoc : {a b c d : ℕ}
  → (f : c ≤ d) (g : b ≤ c) (h : a ≤ b)
  → ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
≤-assoc _ _ z≤n = refl
≤-assoc (s≤s f) (s≤s g) (s≤s h) = cong s≤s (≤-assoc f g h)

+-refl : ℕ
+-refl = 0

+-trans : ℕ → ℕ → ℕ
+-trans = _+_

+-left-id : (a : ℕ)
  → +-refl + a ≡ a
+-left-id a = refl

+-right-id : (a : ℕ)
  → a ≡ a + +-refl
+-right-id zero    = refl
+-right-id (suc a) = cong suc (+-right-id a)

+-assoc : (a b c : ℕ)
  → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

*-refl : ℕ
*-refl = 1

*-trans : ℕ → ℕ → ℕ
*-trans = _*_

*-left-id : (a : ℕ)
  → *-refl * a ≡ a
*-left-id zero    = refl
*-left-id (suc a) = cong suc (*-left-id a)

*-right-id : (a : ℕ)
  → a ≡ a * *-refl
*-right-id zero    = refl
*-right-id (suc a) = cong suc (*-right-id a)

*-assoc :
    (a b c : ℕ)
  → (a * b) * c ≡ a * (b * c)
*-assoc zero    b c = refl
*-assoc (suc a) b c = cong (b * c +_) (*-assoc a b c)
  ∙ *-+-dist b (a * b) c
  where
  *-+-dist :
    (a b c : ℕ)
    → (a + b) * c ≡ a * c + b * c
  *-+-dist zero    b c = refl
  *-+-dist (suc a) b c = ≡-sym (+-assoc c (a * c) (b * c))
    ∙ cong (c +_) (*-+-dist a b c)



