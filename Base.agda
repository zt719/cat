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

private variable i j : Level
private variable A : UU i
private variable B : UU j

-- Extensionality --
postulate
  ext : {f g : A → B}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

cong : (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl

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

≡-left-id : {x y : A}
  → (p : x ≡ y)
  → ≡-trans ≡-refl p ≡ p
≡-left-id refl = refl

≡-right-id : {x y : A}
  → (p : x ≡ y)
  → ≡-trans p ≡-refl ≡ p
≡-right-id refl = refl

≡-assoc : {x y z h : A}
  → (p : z ≡ h) → (q : y ≡ z) → (r : x ≡ y)
  → ≡-trans (≡-trans p q) r ≡ ≡-trans p (≡-trans q r)
≡-assoc refl refl refl = refl


→-refl : A → A
→-refl a = a

→-trans : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  → (B → C) → (A → B) → (A → C)
→-trans f g x = f (g x)

→-left-id : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B)
  → →-trans →-refl f ≡ f
→-left-id f = refl

→-right-id : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B)
  → →-trans f →-refl ≡ f
→-right-id f = refl

→-assoc : {i j k l : Level}
  {A : UU i} {B : UU j}
  {C : UU k} {D : UU l}
  → (f : C → D)
  → (g : B → C)
  → (h : A → B)
  → →-trans (→-trans f g) h ≡ →-trans f (→-trans g h)
→-assoc f g h = refl

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
  → ≤-trans f ≤-refl ≡ f
≤-right-id z≤n = refl
≤-right-id (s≤s f) = cong s≤s (≤-right-id f)

≤-assoc : {a b c d : ℕ}
  → (f : c ≤ d) (g : b ≤ c) (h : a ≤ b)
  → ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
≤-assoc _ _ z≤n = refl
≤-assoc (s≤s f) (s≤s g) (s≤s h) = cong s≤s (≤-assoc f g h)

reflexive : {A : UU i}
  → (R : A → A → UU j)
  → UU (i ⊔ j)
reflexive R = {x : _} → R x x

symmetric : {A : UU i}
  (R : A → A → UU j)
  → UU (i ⊔ j)
symmetric R = {x y : _} → R x y → R y x

transitive : {A : UU i}
  → (R : A → A → UU j)
  → UU (i ⊔ j)
transitive R = {x y z : _} → R y z → R x y → R x z

postulate
  R-left-id : {x y : A}
    → (R : A → A → UU j)
    → (f : R x y)
    → (r : reflexive R)
    → (t : transitive R)
    → t r f ≡ f

  R-right-id : {x y : A}
    → (R : A → A → UU j)
    → (f : R x y)
    → (r : reflexive R)
    → (t : transitive R)
    → t f r ≡ f

  R-assoc : {a b c d : A}
    → (R : A → A → UU j)
    → (f : R c d)
    → (g : R b c)
    → (h : R a b)
    → (t : transitive R)
    → t (t f g) h ≡ t f (t g h)

+-left-id : (a : ℕ)
  → (zero + a) ≡ a
+-left-id a = refl

+-right-id : (a : ℕ)
  → (a + zero) ≡ a
+-right-id zero    = refl
+-right-id (suc a) = cong suc (+-right-id a)

+-assoc : (a b c : ℕ)
  → ((a + b) + c) ≡ (a + (b + c))
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

*-left-id : (a : ℕ)
  → (1 * a) ≡ a
*-left-id zero    = refl
*-left-id (suc a) = cong suc (*-left-id a)

*-right-id : (a : ℕ)
  → (a * 1) ≡ a
*-right-id zero    = refl
*-right-id (suc a) = cong suc (*-right-id a)

*-+-dist : (a b c : ℕ)
  → (a + b) * c ≡ a * c + b * c
*-+-dist zero    b c = refl
*-+-dist (suc a) b c
  rewrite (+-assoc c (a * c) (b * c))
  = cong (c +_) (*-+-dist a b c)

*-assoc : (a b c : ℕ)
  → ((a * b) * c) ≡ (a * (b * c))
*-assoc zero    b c = refl
*-assoc (suc a) b c
  rewrite (*-+-dist b (a * b) c)
  = cong (b * c +_) (*-assoc a b c)

_++_ :
  List A → List A → List A
[] ++ bs = bs
(x ∷ as) ++ bs = x ∷ (as ++ bs)

++-left-id :
  (l : List A)
  → [] ++ l ≡ l
++-left-id l = refl

++-right-id :
  (l : List A)
  → l ++ [] ≡ l
++-right-id []      = refl
++-right-id (x ∷ l) = cong (x ∷_) (++-right-id l)

++-assoc :
  (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
