module Data.Fin where

open import Data.Equality
open import Data.Nat

data Fin : ℕ → Set where
  ★ : {k : ℕ} → Fin (suc k)
  𝓲 : {k : ℕ} → Fin k → Fin (suc k)

data Fin⇒ : (k : ℕ) (a b : Fin k) → Set where
  id⇒ : (k : ℕ) {a : Fin k} → Fin⇒ k a a

Fin⇒-refl : (k : ℕ) {a : Fin k}
  → Fin⇒ k a a
Fin⇒-refl k = id⇒ k

Fin⇒-trans : (k : ℕ) {a b c : Fin k}
  → Fin⇒ k b c → Fin⇒ k a b → Fin⇒ k a c
Fin⇒-trans k (id⇒ .k) (id⇒ .k) = id⇒ k

Fin⇒-left-id : (k : ℕ) {a b : Fin k}
  → (f : Fin⇒ k a b)
  → Fin⇒-trans k (Fin⇒-refl k) f ≡ f
Fin⇒-left-id k (id⇒ .k) = refl

Fin⇒-right-id : (k : ℕ) {a b : Fin k}
  → (f : Fin⇒ k a b)
  → f ≡ Fin⇒-trans k f (Fin⇒-refl k)
Fin⇒-right-id k (id⇒ .k) = refl

Fin⇒-assoc : (k : ℕ) {a b c d : Fin k}
  → (f : Fin⇒ k c d)
  → (g : Fin⇒ k b c)
  → (h : Fin⇒ k a b)
  → Fin⇒-trans k (Fin⇒-trans k f g) h ≡ Fin⇒-trans k f (Fin⇒-trans k g h)
Fin⇒-assoc k (id⇒ .k) (id⇒ .k) (id⇒ .k) = refl
