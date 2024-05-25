module Base where

open import Level public
  renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; cong; cong₂)
open import Data.Nat public
  hiding (_⊔_)
open import Data.Empty public
  using (⊥)
open import Data.Unit public
  using (⊤; tt)
open import Data.Product public
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum public
  using (_⊎_; inj₁; inj₂)
open import Data.Fin public
  using (Fin)
open import Data.List public
  using (List; []; _∷_; _++_; head)
  renaming (map to list-map₁)
open import Data.Maybe public
  using (Maybe; just; nothing)
  renaming (map to maybe-map₁)

variable i j k l m n p q : Level

postulate
  ext : {A : Set i} {B : Set j}
    → {f g : A → B}
    → ((x : A) → f x ≡ g x)
    → f ≡ g
    
≡-refl : {A : Set i} {x : A}
  → x ≡ x
≡-refl = refl

≡-sym : {A : Set i} {x y : A}
  → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {A : Set i} {x y z : A}
  → y ≡ z → x ≡ y → x ≡ z
≡-trans refl refl = refl

infixl 5 _∙_
_∙_ = ≡-trans

≡-left-id : {A : Set i} {x y : A}
  → (p : x ≡ y)
  → ≡-refl ∙ p ≡ p
≡-left-id refl = refl

≡-right-id : {A : Set i} {x y : A}
  → (p : x ≡ y)
  → p ≡ p ∙ ≡-refl
≡-right-id refl = refl

≡-assoc : {A : Set i} {x y z h : A}
  → (p : z ≡ h) (q : y ≡ z) (r : x ≡ y)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
≡-assoc refl refl refl = refl

→-refl : {A : Set i} → A → A
→-refl a = a

→-trans : {A : Set i} {B : Set j} {C : Set k}
  → (B → C) → (A → B) → (A → C)
→-trans f g x = f (g x)

infixl 5 _→∘_
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

postulate
  *-assoc : (a b c : ℕ)
    → (a * b) * c ≡ a * (b * c)

data _-⊥→_ (a b : ⊥) : Set where

data _-⊤→_ (a b : ⊤) : Set where
  -tt→ : tt -⊤→ tt


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

++-refl : {A : Set i}
  → List A
++-refl = []

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

list-map-id' : {A : Set i}
  → (as : List A)
  → list-map₁ →-refl as ≡ →-refl as
list-map-id' [] = refl
list-map-id' (a ∷ as) = cong (→-refl a ∷_) (list-map-id' as)

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

maybe-map₁-id' : {A : Set i}
  → (x : Maybe A)
  → maybe-map₁ →-refl x ≡ →-refl x
maybe-map₁-id' (just x) = refl
maybe-map₁-id' nothing  = refl

maybe-map₁-∘' : {A : Set i} {B : Set j} {C : Set k}
  → {f : B → C} {g : A → B}
  → (x : Maybe A)
  → maybe-map₁ (f →∘ g) x ≡ (maybe-map₁ f →∘ maybe-map₁ g) x
maybe-map₁-∘' (just x) = refl
maybe-map₁-∘' nothing = refl
