module Base where

open import Agda.Primitive public
  renaming (Set to UU)
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Unit public
  renaming (⊤ to 𝟙; tt to ＊)

private variable i j k l : Level
private variable A : UU i
private variable B : UU j
private variable C : UU k
private variable D : UU l

-- Extensionality --
postulate
  ext : {f g : A → B}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

infix 4 _≅_

data _≅_ {ℓ} {A : UU ℓ} (x : A) : {B : UU ℓ} → B → UU ℓ where
   refl : x ≅ x

------------------------------------------------------------------------
-- Conversion

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

≡-to-≅ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

cong-h : ∀ {a b} {A : UU a} {B : A → UU b} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong-h f refl = refl

cong₂-h : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂-h f refl refl = refl

cong : {A : UU i} {B : UU j} {x₁ x₂ : A}
  → (f : A → B)
  → x₁ ≡ x₂
  → f x₁ ≡ f x₂
cong f refl = refl

cong₂ : {A : UU i} 
  → (f : A → B → C) {x₁ y₁ : A} {x₂ y₂ : B}
  → x₁ ≡ y₁
  → x₂ ≡ y₂
  → f x₁ x₂ ≡ f y₁ y₂
cong₂ f refl refl = refl

infix  4 _≤_
data _≤_ : ℕ → ℕ → UU where
  z≤n : {n : ℕ}
    → zero  ≤ n
  s≤s : {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n

≡-refl : {x : A}
  → x ≡ x
≡-refl = refl

≡-sym : {x y : A}
  → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {x y z : A}
  → y ≡ z → x ≡ y → x ≡ z
≡-trans refl refl = refl

infixl 5 _≡∘_
_≡∘_ = ≡-trans

≡-left-id : {x y : A}
  → (p : x ≡ y)
  → ≡-refl ≡∘ p ≡ p
≡-left-id refl = refl

≡-right-id : {x y : A}
  → (p : x ≡ y)
  → p ≡∘ ≡-refl ≡ p
≡-right-id refl = refl

≡-assoc : {x y z h : A}
  → (p : z ≡ h) (q : y ≡ z) (r : x ≡ y)
  → (p ≡∘ q) ≡∘ r ≡ p ≡∘ (q ≡∘ r)
≡-assoc refl refl refl = refl


→-refl : A → A
→-refl a = a

→-trans : (B → C) → (A → B) → (A → C)
→-trans f g x = f (g x)

_←_ = →-trans

→-left-id :
    (f : A → B)
  → →-refl ← f ≡ f
→-left-id f = refl

→-right-id :
    (f : A → B)
  → f ← →-refl ≡ f
→-right-id f = refl

→-assoc :
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
  → f ∘≤ ≤-refl ≡ f
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
  → a + +-refl ≡ a
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
  → a * *-refl ≡ a
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

++-refl : List A
++-refl = []

_++_ : List A → List A → List A
[] ++ bs = bs
(x ∷ as) ++ bs = x ∷ (as ++ bs)

++-trans = _++_

++-left-id :
    (l : List A)
  → ++-refl ++ l ≡ l
++-left-id l = refl

++-right-id :
    (l : List A)
  → l ++ ++-refl ≡ l
++-right-id []      = refl
++-right-id (x ∷ l) = cong (x ∷_) (++-right-id l)

++-assoc :
    (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
