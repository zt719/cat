module Base where

open import Agda.Primitive public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Char public
open import Agda.Builtin.Unit public

variable i j k l m n p q : Level

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ x ∶ A , Bx

_×_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A (λ _ → B)

-- Extensionality --
postulate
  ext : {l₁ l₂ : Level} {A : Set l₁} {B : Set l₂}
    → {f g : A → B}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

  ext' : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

transport : ∀ {i j} {X : Set i} (A : X → Set j) {x y : X}
          → x ≡ y → A x → A y
transport A refl x = x

data ⊥ : Set where

data _-⊥→_ (a b : ⊥) : Set where

cong : ∀ {i j} {A : Set i} {B : Set j} {x₁ x₂ : A}
  → (f : A → B)
  → x₁ ≡ x₂
  → f x₁ ≡ f x₂
cong f refl = refl

infix  4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat}
    → zero  ≤ n
  s≤s : {m n : Nat}
    → m ≤ n
    → suc m ≤ suc n

≡-refl : ∀ {i} {A : Set i} {x : A}
  → x ≡ x
≡-refl = refl

≡-sym : ∀ {i} {A : Set i} {x y : A}
  → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : ∀ {i} {A : Set i} {x y z : A}
  → y ≡ z → x ≡ y → x ≡ z
≡-trans refl refl = refl

infixl 5 _∙_
_∙_ = ≡-trans

≡-left-id : ∀ {i} {A : Set i} {x y : A}
  → (p : x ≡ y)
  → ≡-refl ∙ p ≡ p
≡-left-id refl = refl

≡-right-id : ∀ {i} {A : Set i} {x y : A}
  → (p : x ≡ y)
  → p ≡ p ∙ ≡-refl
≡-right-id refl = refl

≡-assoc : ∀ {i} {A : Set i} {x y z h : A}
  → (p : z ≡ h) (q : y ≡ z) (r : x ≡ y)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
≡-assoc refl refl refl = refl

→-refl : ∀ {i} {A : Set i} → A → A
→-refl a = a

→-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
  → (B → C) → (A → B) → (A → C)
→-trans f g x = f (g x)

_←∘-_ = →-trans

→-left-id : ∀ {i j} {A : Set i} {B : Set j}
  → (f : A → B)
  → →-refl ←∘- f ≡ f
→-left-id f = refl

→-right-id : ∀ {i j} {A : Set i} {B : Set j}
    (f : A → B)
  → f ≡ f ←∘- →-refl
→-right-id f = refl

→-assoc : ∀ {l₁ l₂ l₃ l₄} {A : Set l₁} {B : Set l₂} {C : Set l₃} {D : Set l₄}
    (f : C → D) (g : B → C) (h : A → B)
  → (f ←∘- g) ←∘- h ≡ f ←∘- (g ←∘- h)
→-assoc f g h = refl

≤-refl : {a : Nat}
  → a ≤ a
≤-refl {zero} = z≤n
≤-refl {suc a} = s≤s ≤-refl

≤-trans : {a b c : Nat}
  → b ≤ c → a ≤ b → a ≤ c
≤-trans _         z≤n       = z≤n
≤-trans (s≤s b≤c) (s≤s a≤b) = s≤s (≤-trans b≤c a≤b)

≤-left-id : {a b : Nat}
  → (f : a ≤ b)
  → ≤-trans ≤-refl f ≡ f
≤-left-id z≤n = refl
≤-left-id (s≤s f) = cong s≤s (≤-left-id f)

≤-right-id : {a b : Nat}
  → (f : a ≤ b)
  → f ≡ ≤-trans f ≤-refl
≤-right-id z≤n = refl
≤-right-id (s≤s f) = cong s≤s (≤-right-id f)

≤-assoc : {a b c d : Nat}
  → (f : c ≤ d) (g : b ≤ c) (h : a ≤ b)
  → ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
≤-assoc _ _ z≤n = refl
≤-assoc (s≤s f) (s≤s g) (s≤s h) = cong s≤s (≤-assoc f g h)

+-refl : Nat
+-refl = 0

+-trans : Nat → Nat → Nat
+-trans = _+_

+-left-id : (a : Nat)
  → +-refl + a ≡ a
+-left-id a = refl

+-right-id : (a : Nat)
  → a ≡ a + +-refl
+-right-id zero    = refl
+-right-id (suc a) = cong suc (+-right-id a)

+-assoc : (a b c : Nat)
  → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

*-refl : Nat
*-refl = 1

*-trans : Nat → Nat → Nat
*-trans = _*_

*-left-id : (a : Nat)
  → *-refl * a ≡ a
*-left-id zero    = refl
*-left-id (suc a) = cong suc (*-left-id a)

*-right-id : (a : Nat)
  → a ≡ a * *-refl
*-right-id zero    = refl
*-right-id (suc a) = cong suc (*-right-id a)

*-assoc :
    (a b c : Nat)
  → (a * b) * c ≡ a * (b * c)
*-assoc zero    b c = refl
*-assoc (suc a) b c = cong (b * c +_) (*-assoc a b c)
  ∙ *-+-dist b (a * b) c
  where
  *-+-dist :
    (a b c : Nat)
    → (a + b) * c ≡ a * c + b * c
  *-+-dist zero    b c = refl
  *-+-dist (suc a) b c = ≡-sym (+-assoc c (a * c) (b * c))
    ∙ cong (c +_) (*-+-dist a b c)

++-refl : ∀ {i} {A : Set i}
  → List A
++-refl = []

_++_ : ∀ {i} {A : Set i}
  → List A → List A → List A
[] ++ bs = bs
(x ∷ as) ++ bs = x ∷ (as ++ bs)

++-trans = _++_

++-left-id : ∀ {i} {A : Set i}
  → (l : List A)
  → ++-refl ++ l ≡ l
++-left-id l = refl

++-right-id : ∀ {i} {A : Set i}
  → (l : List A)
  → l ≡ l ++ ++-refl
++-right-id []      = refl
++-right-id (x ∷ l) = cong (x ∷_) (++-right-id l)

++-assoc : ∀ {i} {A : Set i}
  → (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

{-
data Fin : Nat → Set where
  ★ : (k : Nat) → Fin (suc k)
  i : (k : Nat) → Fin k → Fin (suc k)
-}
