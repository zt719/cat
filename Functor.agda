module Functor where

open import Base
open import Category
open import Monoid

private variable ℂ : Category {i} {j}
private variable 𝔻 : Category {k} {l}
private variable 𝔼 : Category {m} {n}
private variable 𝔽 : Category {p} {q}

record Functor (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category
  field
    map : obj ℂ → obj 𝔻
    fmap : {a b : obj ℂ} → hom ℂ a b → hom 𝔻 (map a) (map b)
    
    id-law   : {a : obj ℂ} → fmap (id ℂ {a}) ≡ id 𝔻 {map a}
    trans-law : {a b c : obj ℂ} {f : hom ℂ b c} {g : hom ℂ a b}
      → fmap ((_∘_) ℂ f g) ≡ (_∘_) 𝔻 (fmap f) (fmap g)
open Functor

_⇒_ = Functor

Endofunctor : Category {i} {j} → Set (i ⊔ j)
Endofunctor ℂ = ℂ ⇒ ℂ

func-refl : ℂ ⇒ ℂ
func-refl = record { map = →-refl ; fmap = →-refl ; id-law = ≡-refl ; trans-law = ≡-refl}

func-trans : 𝔻 ⇒ 𝔼 → ℂ ⇒ 𝔻 → ℂ ⇒ 𝔼
func-trans
  record { map = map-F ; fmap = fmap-F ; id-law = id-law-F ; trans-law = trans-law-F }
  record { map = map-G ; fmap = fmap-G ; id-law = id-law-G ; trans-law = trans-law-G }
  = record
  { map  = map-F ←∘- map-G
  ; fmap = fmap-F ←∘- fmap-G
  ; id-law   = id-law-F ∙ cong fmap-F id-law-G
  ; trans-law = trans-law-F ∙ cong fmap-F trans-law-G
  }

_⇐∘=_ = func-trans

postulate
  func-left-id :
    (F : ℂ ⇒ 𝔻)
    → func-refl ⇐∘= F ≡ F

  func-right-id :
    (F : ℂ ⇒ 𝔻)
    → F ≡ F ⇐∘= func-refl

  func-assoc :
    (F : 𝔼 ⇒ 𝔽) (G : 𝔻 ⇒ 𝔼) (H : ℂ ⇒ 𝔻)
    → (F ⇐∘= G) ⇐∘= H ≡ F ⇐∘= (G ⇐∘= H)

CAT : ∀ {i j} → Category
CAT {i} {j} = record
        { obj = Category {i} {j}
        ; hom = _⇒_
        ; id = func-refl
        ; _∘_ = func-trans
        ; left-id = func-left-id
        ; right-id = func-right-id
        ; assoc = func-assoc
        }

maybe-functor : Endofunctor SET
maybe-functor
  = record
  { map  = Maybe
  ; fmap = maybe-fmap
  ; id-law = ext λ{ (just a) → refl ; nothing → refl}
  ; trans-law = ext λ { (just a) → refl ; nothing → refl}
  }
  where
  maybe-fmap : ∀ {A B} → (A → B) → Maybe A → Maybe B
  maybe-fmap f (just a) = just (f a)
  maybe-fmap f nothing  = nothing

list-functor : Endofunctor SET
list-functor
  = record
  { map  = List
  ; fmap = list-fmap
  ; id-law = ext list-id-law'
  ; trans-law = ext list-trans-law'
  }
  where
  list-fmap : ∀ {A B} → (A → B) → List A → List B
  list-fmap f [] = []
  list-fmap f (a ∷ as) = f a ∷ list-fmap f as
  
  list-id-law' : ∀ {A} → (as : List A) → list-fmap →-refl as ≡ →-refl as
  list-id-law' [] = refl
  list-id-law' (l₇ ∷ as) = cong (→-refl l₇ ∷_) (list-id-law' as)
  
  list-trans-law' : ∀ {A B C} → {f : B → C} {g : A → B}
    → (as : List A)
    → list-fmap (→-trans f g) as ≡ →-trans (list-fmap f) (list-fmap g) as
  list-trans-law' [] = refl
  list-trans-law' {f = f} {g = g} (a ∷ as) = cong (→-trans f g a ∷_) (list-trans-law' as)

forgetful-functor : MON ⇒ SET
forgetful-functor = record
  { map  = Monoid.obj
  ; fmap = Monoid-Homomorphism.map
  ; id-law   = refl
  ; trans-law = refl
  }

identity-functor :
  (ℂ : Category {i} {j})
  → Endofunctor ℂ
identity-functor ℂ = func-refl
