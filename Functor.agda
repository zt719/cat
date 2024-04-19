module Functor where

open import Category
open import Monoid

private variable l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ : Level
private variable A : UU l₁
private variable B : UU l₂
private variable C : UU l₃
private variable 𝓒 : Category {l₁} {l₂}
private variable 𝓓 : Category {l₃} {l₄}
private variable 𝓔 : Category {l₅} {l₆}
private variable 𝓕 : Category {l₇} {l₈}

record Functor (𝓒 : Category {l₁} {l₂} ) (𝓓 : Category {l₃} {l₄}) : UU (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄) where
  open Category.Category
  field
    -- Components --
    map : obj 𝓒 → obj 𝓓
    fmap : {a b : obj 𝓒} → hom 𝓒 a b → hom 𝓓 (map a) (map b)

    -- Functor Laws --
    map-id   : {a : obj 𝓒} → fmap (id 𝓒 {a}) ≡ id 𝓓 {map a}
    map-comp : {a b c : obj 𝓒} {f : hom 𝓒 b c} {g : hom 𝓒 a b}
      → fmap ((_∘_) 𝓒 f g) ≡ (_∘_) 𝓓 (fmap f) (fmap g)
open Functor

Endofunctor : Category {l₁} {l₂} → UU (l₁ ⊔ l₂)
Endofunctor 𝓒 = Functor 𝓒 𝓒

func-refl : Functor 𝓒 𝓒
func-refl
  = record
  { map  = →-refl
  ; fmap = →-refl
  ; map-id   = ≡-refl
  ; map-comp = ≡-refl
  }

func-trans : Functor 𝓓 𝓔 → Functor 𝓒 𝓓 → Functor 𝓒 𝓔
func-trans
  record { map = map-F ; fmap = fmap-F ; map-id = map-id-F ; map-comp = map-comp-F }
  record { map = map-G ; fmap = fmap-G ; map-id = map-id-G ; map-comp = map-comp-G }
  = record
  { map  = map-F ← map-G
  ; fmap = fmap-F ← fmap-G
  ; map-id   = map-id-F ≡∘ cong fmap-F map-id-G
  ; map-comp = map-comp-F ≡∘ cong fmap-F map-comp-G
  }

_⇐_ = func-trans

postulate
  func-≡ : (F D : Functor 𝓒 𝓓)
    → (map F ≡ map D)
    → F ≡ D

func-left-id :
    (F : Functor 𝓒 𝓓)
  → func-refl ⇐ F ≡ F
func-left-id F
  = func-≡ (func-refl ⇐ F) F refl

postulate
  func-assoc : (F : Functor 𝓔 𝓕) (G : Functor 𝓓 𝓔) (H : Functor 𝓒 𝓓)
    → (F ⇐ G) ⇐ H ≡ F ⇐ (G ⇐ H)

maybe-functor : Endofunctor SET
maybe-functor
  = record
  { map  = Maybe
  ; fmap = maybe-fmap
  ; map-id = ext λ{ (just a) → refl ; nothing → refl}
  ; map-comp = ext λ { (just a) → refl ; nothing → refl}
  }
  where
  maybe-fmap : (A → B) → Maybe A → Maybe B
  maybe-fmap f (just a) = just (f a)
  maybe-fmap f nothing  = nothing

list-functor : Endofunctor SET
list-functor
  = record
  { map  = List
  ; fmap = list-fmap
  ; map-id = ext list-map-id'
  ; map-comp = ext list-map-comp'
  }
  where
  list-fmap : (A → B) → List A → List B
  list-fmap f [] = []
  list-fmap f (a ∷ as) = f a ∷ list-fmap f as
  
  list-map-id' : (as : List A) → list-fmap →-refl as ≡ →-refl as
  list-map-id' [] = refl
  list-map-id' (l₇ ∷ as) = cong (→-refl l₇ ∷_) (list-map-id' as)
  
  list-map-comp' : {f : B → C} {g : A → B}
    → (as : List A)
    → list-fmap (→-trans f g) as ≡ →-trans (list-fmap f) (list-fmap g) as
  list-map-comp' [] = refl
  list-map-comp' {f = f} {g = g} (a ∷ as) = cong (→-trans f g a ∷_) (list-map-comp' as)

forgetful-functor : Functor MON SET
forgetful-functor = record
  { map  = Monoid.obj
  ; fmap = MH.map
  ; map-id   = refl
  ; map-comp = refl
  }

identity-functor :
  (𝓒 : Category {l₁} {l₂})
  → Endofunctor 𝓒
identity-functor 𝓒 = func-refl


