module Category.Functor where

open import Agda.Primitive
open import Data.Equality
open import Data.Heterogeneous-Equality
open import Data.Function
open import Data.Maybe
open import Data.List
open import Category.Category
open import Category.Monoid

private variable i j k l m n p q : Level
private variable ℂ : Category {i} {j}
private variable 𝔻 : Category {k} {l}
private variable 𝔼 : Category {m} {n}
private variable 𝔽 : Category {p} {q}

record Functor (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  constructor mkFunctor
  open Category.Category.Category ℂ renaming (_∘_ to _∘ℂ_)
  open Category.Category.Category 𝔻 renaming (_∘_ to _∘𝔻_)
  field
    map₀ : obj ℂ → obj 𝔻
    map₁ : {a b : obj ℂ} → hom ℂ a b → hom 𝔻 (map₀ a) (map₀ b)
    
    map-id : {a : obj ℂ} → map₁ (id ℂ {a}) ≡ id 𝔻 {map₀ a}
    map-∘  : {a b c : obj ℂ} {f : hom ℂ b c} {g : hom ℂ a b}
      → map₁ (f ∘ℂ g) ≡ map₁ f ∘𝔻 map₁ g
open Functor

_⇒_ = Functor

Endofunctor : Category {i} {j} → Set (i ⊔ j)
Endofunctor ℂ = ℂ ⇒ ℂ

func-refl : ℂ ⇒ ℂ
func-refl
  = record
  { map₀ = →-refl
  ; map₁ = →-refl
  ; map-id = ≡-refl
  ; map-∘ = ≡-refl
  }

func-trans : 𝔻 ⇒ 𝔼 → ℂ ⇒ 𝔻 → ℂ ⇒ 𝔼
func-trans
  record { map₀ = F₀ ; map₁ = F₁ ; map-id = map-id-F ; map-∘ = map-∘-F }
  record { map₀ = G₀ ; map₁ = G₁ ; map-id = map-id-G ; map-∘ = map-∘-G }
  = record
  { map₀ = F₀ →∘ G₀
  ; map₁ = F₁ →∘ G₁
  ; map-id = map-id-F ∙ cong F₁ map-id-G
  ; map-∘  = map-∘-F ∙ cong F₁ map-∘-G
  }
    
_⇒∘_ = func-trans


{-
open Category.Category.Category using (obj; hom)
FEq : (s t : ℂ ⇒ 𝔻) {a b c : obj ℂ} {f : hom ℂ b c} {g : hom ℂ a b}
  → map₀ s ≡ map₀ t
  → map₁ s {a} {b} ≅ map₁ t {a} {b}
  → map-id s {a} ≅ map-id t {a}
  → map-∘ s {a} {b} {c} {f} {g} ≅ map-∘ t {a} {b} {c} {f} {g}
  → s ≅ t
FEq (mkFunctor map₂ map₃ map-id₁ map-∘₁) (mkFunctor .map₂ map₅ map-id₂ map-∘₂) refl b c d = {!!}
-}

postulate
  func-left-id :
    (F : ℂ ⇒ 𝔻)
    → func-refl ⇒∘ F ≡ F

  func-right-id :
    (F : ℂ ⇒ 𝔻)
    → F ≡ F ⇒∘ func-refl

  func-assoc :
    (F : 𝔼 ⇒ 𝔽) (G : 𝔻 ⇒ 𝔼) (H : ℂ ⇒ 𝔻)
    → (F ⇒∘ G) ⇒∘ H ≡ F ⇒∘ (G ⇒∘ H)

CAT : ∀ {i j} → Category
CAT {i} {j}
  = record
  { obj = Category {i} {j}
  ; hom = Functor
  ; id = func-refl
  ; _∘_ = func-trans
  ; left-id = func-left-id
  ; right-id = func-right-id
  ; assoc = func-assoc
  }


maybe-functor : Endofunctor SET
maybe-functor
  = record
  { map₀ = Maybe
  ; map₁ = maybe-map₁
  ; map-id = ext λ{ (just a) → refl ; nothing → refl}
  ; map-∘ = ext λ { (just a) → refl ; nothing → refl}
  }
  where
  maybe-map₁ : ∀ {A B} → (A → B) → Maybe A → Maybe B
  maybe-map₁ f (just a) = just (f a)
  maybe-map₁ f nothing  = nothing

list-map₁ : {A : Set i} {B : Set j} → (A → B) → List A → List B
list-map₁ f [] = []
list-map₁ f (a ∷ as) = f a ∷ list-map₁ f as

list-map-id' : {A : Set i} → (as : List A) → list-map₁ →-refl as ≡ →-refl as
list-map-id' [] = refl
list-map-id' (l₇ ∷ as) = cong (→-refl l₇ ∷_) (list-map-id' as)

list-map-∘' : {A : Set i} {B : Set j} {C : Set k} → {f : B → C} {g : A → B}
  → (as : List A)
  → list-map₁ (→-trans f g) as ≡ →-trans (list-map₁ f) (list-map₁ g) as
list-map-∘' [] = refl
list-map-∘' {f = f} {g = g} (a ∷ as) = cong (→-trans f g a ∷_) (list-map-∘' as)

list-functor : Endofunctor SET
list-functor
  = record
  { map₀  = List
  ; map₁ = list-map₁
  ; map-id = ext list-map-id'
  ; map-∘ = ext list-map-∘'
  }

forgetful-functor : MON ⇒ SET
forgetful-functor = record
  { map₀ = Monoid.obj
  ; map₁ = Monoid-Homomorphism.map
  ; map-id = refl
  ; map-∘  = refl
  }

list-map₁-++ : {A : Set i} {B : Set i} → (f : A → B) → (as bs : List A)
  → list-map₁ f (as ++ bs) ≡ list-map₁ f as ++ list-map₁ f bs
list-map₁-++ f [] bs = refl
list-map₁-++ f (x ∷ as) bs = cong (f x ∷_) (list-map₁-++ f as bs)

{-
free-functor : SET ⇒ MON
free-functor
  = record
  { map₀ = free-monoid
  ; map₁ = λ f → record { map = list-map₁ f ; map-⊕ = λ {a} {b} → list-map₁-++ f a b }
  ; map-id = λ{ {a} → {!!} }
  ; map-∘ = {!!}
  }
-}

id-functor :
  (ℂ : Category {i} {j})
  → Endofunctor ℂ
id-functor ℂ = func-refl
