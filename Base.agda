module Base where

open import Agda.Primitive public
  renaming (Set to UU)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Char public

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ x ∶ A , Bx

_×_ : {i j : Level} → UU i → UU j → UU (i ⊔ j)
A × B = Σ A (λ _ → B)

-- Extensionality --
postulate
  ext : {l₁ l₂ : Level} {A : UU l₁} {B : UU l₂}
    → {f g : A → B}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

  ext' : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

transport : ∀ {i j} {X : UU i} (A : X → UU j) {x y : X}
          → x ≡ y → A x → A y
transport A refl x = x

data 𝟘 : UU where

data 𝟘⇒ (a b : 𝟘) : UU where

data 𝟙 : UU where
  tt : 𝟙


{-
-- Heterogenous Equality
infix 4 _≅_

data _≅_ {ℓ} {A : UU ℓ} (x : A) : {B : UU ℓ} → B → UU ℓ where
   refl : x ≅ x

≅-to-≡ : ∀ {a} {A : UU a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

≡-to-≅ : ∀ {a} {A : UU a} {x y : A} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

cong-h : ∀ {a b} {A : UU a} {B : A → UU b} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong-h f refl = refl

cong₂-h : ∀ {a b c} {A : UU a} {B : A → UU b} {C : ∀ x → B x → UU c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂-h f refl refl = refl

cong₃-h : ∀ {l₁ l₂ l₃ l₄} {A : UU l₁} {B : A → UU l₂} {C : (x : A) → B x → UU l₃}
          {D : (x : A) (y : B x) (z : C x y) → UU l₄}
          {x x' y y' z z'}
          (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ x' → y ≅ y' → z ≅ z' → f x y z ≅ f x' y' z'
cong₃-h f refl refl refl = refl

cong₄-h : ∀ {l₁ l₂ l₃ l₄ l₅}
          {A : UU l₁} {B : A → UU l₂} {C : (x : A) (y : B x) → UU l₃}
          {D : (x : A) (y : B x) (z : C x y) → UU l₄}
          {E : (x : A) (y : B x) (z : C x y) (m : D x y z) → UU l₅}
          {x x' y y' z z' m m'}
          (f : (x : A) (y : B x) (z : C x y) (m : D x y z) → E x y z m)
          → x ≅ x' → y ≅ y' → z ≅ z' → m ≅ m'
          → f x y z m ≅ f x' y' z' m'
cong₄-h f refl refl refl refl = refl
-}

cong : ∀ {i j} {A : UU i} {B : UU j} {x₁ x₂ : A}
  → (f : A → B)
  → x₁ ≡ x₂
  → f x₁ ≡ f x₂
cong f refl = refl

infix  4 _≤_
data _≤_ : ℕ → ℕ → UU where
  z≤n : {n : ℕ}
    → zero  ≤ n
  s≤s : {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n

≡-refl : ∀ {i} {A : UU i} {x : A}
  → x ≡ x
≡-refl = refl

≡-sym : ∀ {i} {A : UU i} {x y : A}
  → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : ∀ {i} {A : UU i} {x y z : A}
  → y ≡ z → x ≡ y → x ≡ z
≡-trans refl refl = refl

infixl 5 _≡∘_
_≡∘_ = ≡-trans

≡-left-id : ∀ {i} {A : UU i} {x y : A}
  → (p : x ≡ y)
  → ≡-refl ≡∘ p ≡ p
≡-left-id refl = refl

≡-right-id : ∀ {i} {A : UU i} {x y : A}
  → (p : x ≡ y)
  → p ≡ p ≡∘ ≡-refl
≡-right-id refl = refl

≡-assoc : ∀ {i} {A : UU i} {x y z h : A}
  → (p : z ≡ h) (q : y ≡ z) (r : x ≡ y)
  → (p ≡∘ q) ≡∘ r ≡ p ≡∘ (q ≡∘ r)
≡-assoc refl refl refl = refl

→-refl : ∀ {i} {A : UU i} → A → A
→-refl a = a

→-trans : ∀ {i j k} {A : UU i} {B : UU j} {C : UU k}
  → (B → C) → (A → B) → (A → C)
→-trans f g x = f (g x)

_←_ = →-trans

→-left-id : ∀ {i j} {A : UU i} {B : UU j}
  → (f : A → B)
  → →-refl ← f ≡ f
→-left-id f = refl

→-right-id : ∀ {i j} {A : UU i} {B : UU j}
    (f : A → B)
  → f ≡ f ← →-refl
→-right-id f = refl

→-assoc : ∀ {l₁ l₂ l₃ l₄} {A : UU l₁} {B : UU l₂} {C : UU l₃} {D : UU l₄}
    (f : C → D) (g : B → C) (h : A → B)
  → (f ← g) ← h ≡ f ← (g ← h)
→-assoc f g h = refl

≤-refl : {a : ℕ}
  → a ≤ a
≤-refl {zero} = z≤n
≤-refl {suc a} = s≤s ≤-refl

≤-trans : {a b c : ℕ}
  → b ≤ c → a ≤ b → a ≤ c
≤-trans _         z≤n       = z≤n
≤-trans (s≤s b≤c) (s≤s a≤b) = s≤s (≤-trans b≤c a≤b)

_∘≤_ = ≤-trans

≤-left-id : {a b : ℕ}
  → (f : a ≤ b)
  → ≤-refl ∘≤ f ≡ f
≤-left-id z≤n = refl
≤-left-id (s≤s f) = cong s≤s (≤-left-id f)

≤-right-id : {a b : ℕ}
  → (f : a ≤ b)
  → f ≡ f ∘≤ ≤-refl
≤-right-id z≤n = refl
≤-right-id (s≤s f) = cong s≤s (≤-right-id f)

≤-assoc : {a b c d : ℕ}
  → (f : c ≤ d) (g : b ≤ c) (h : a ≤ b)
  → (f ∘≤ g) ∘≤ h ≡ f ∘≤ (g ∘≤ h)
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
  ≡∘ *-+-dist b (a * b) c
  where
  *-+-dist :
    (a b c : ℕ)
    → (a + b) * c ≡ a * c + b * c
  *-+-dist zero    b c = refl
  *-+-dist (suc a) b c = ≡-sym (+-assoc c (a * c) (b * c))
    ≡∘ cong (c +_) (*-+-dist a b c)

++-refl : ∀ {i} {A : UU i}
  → List A
++-refl = []

_++_ : ∀ {i} {A : UU i}
  → List A → List A → List A
[] ++ bs = bs
(x ∷ as) ++ bs = x ∷ (as ++ bs)

++-trans = _++_

++-left-id : ∀ {i} {A : UU i}
  → (l : List A)
  → ++-refl ++ l ≡ l
++-left-id l = refl

++-right-id : ∀ {i} {A : UU i}
  → (l : List A)
  → l ≡ l ++ ++-refl
++-right-id []      = refl
++-right-id (x ∷ l) = cong (x ∷_) (++-right-id l)

++-assoc : ∀ {i} {A : UU i}
  → (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
