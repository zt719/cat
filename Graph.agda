module Graph where

open import Base
open import Category
open import Functor
open import Natural-Transformation

open Category.Category hiding (id)
open Functor.Functor

data Vertex : Set where
  E V : Vertex

data Hom : (v1 v2 : Vertex) → Set where
  id : (v : Vertex) → Hom v v
  s t  : Hom E V

𝕀 : Category
𝕀 = record
  { obj = Vertex
  ; hom = Hom
  ; id = λ{ {a = E} → (id E) ; {a = V} → (id V) }
  ; _∘_ = λ
    { (id E) (id E) → (id E) ; (id V) (id V) → (id V) ; (id V) s → s
    ; (id V) t → t ; s (id E) → s ; t (id E) → t
    }
  ; left-id = λ{ (id E) → refl ; (id V) → refl ; s → refl ; t → refl}
  ; right-id = λ{ (id E) → refl ; (id V) → refl ; s → refl ; t → refl}
  ; assoc = λ
    { (id E) (id E) (id E) → refl ; (id V) (id V) (id V) → refl
    ; (id V) (id V) s → refl ; (id V) (id V) t → refl
    ; (id V) s (id E) → refl ; (id V) t (id E) → refl
    ; s (id E) (id E) → refl ; t (id E) (id E) → refl
    }
  }

data GE : Set where
  a b : GE

data GV : Set where
  one two three : GV

Gs : GE → GV
Gs a = one
Gs b = one

Gt : GE → GV
Gt a = three
Gt b = three

G : 𝕀 ⇒ SET
G = record
  { map₀ = λ{ E → GE ; V → GV }
  ; map₁ = λ
    { (id E) → →-refl
    ; (id V) → →-refl
    ; s → Gs
    ; t → Gt
    }
  ; map-id = λ{ {a = E} → refl ; {a = V} → refl }
  ; map-∘ = λ
    { {f = (id E)} {g = (id E)} → refl
    ; {f = (id V)} {g = (id V)} → refl
    ; {f = (id V)} {g = s} → refl
    ; {f = (id V)} {g = t} → refl
    ; {f = s} {g = (id E)} → refl
    ; {f = t} {g = (id E)} → refl
    }
  }

data AE : Set where
  a' : AE

data AV : Set where
  one' two' : AV

As : AE → AV
As a' = one'

At : AE → AV
At a' = two'

A : 𝕀 ⇒ SET
A = record
  { map₀ = λ{ E → AE ; V → AV }
  ; map₁ = λ{ (id E) → →-refl ; (id V) → →-refl ; s → As ; t → At }
  ; map-id = λ
    { {a = E} → refl
    ; {a = V} → refl
    }
  ; map-∘ = λ
    { {f = (id E)} {g = (id E)} → refl
    ; {f = s} {g = (id E)} → refl
    ; {f = t} {g = (id E)} → refl
    ; {f = (id V)} {g = (id V)} → refl
    ; {f = (id V)} {g = s} → refl
    ; {f = (id V)} {g = t} → refl
    }
  }

αE : GE → AE
αE a = a'
αE b = a'

αV : GV → AV
αV one = one'
αV two = two'
αV three = two'

α : G ~ A
α = record
  { component = λ
    { {a = E} → αE
    ; {a = V} → αV
    }
  ; commute = λ
    { {f = (id E)} → refl
    ; {f = s} → ext (λ{ a → refl ; b → refl})
    ; {f = t} → ext (λ{ a → refl ; b → refl})
    ; {f = (id V)} → refl
    }
  }

_∘'_ = _∘_ 𝕀

Hom[_,-] : (x : obj 𝕀) → 𝕀 ⇒ SET
Hom[_,-] x = record
  { map₀ = λ y → hom 𝕀 x y
  ; map₁ = _∘'_
  ; map-id = λ
    { {a = E} → ext λ{ (id E) → refl }
    ; {a = V} → ext λ{ (id V) → refl ; s → refl ; t → refl}}
  ; map-∘ = λ
    { {f = (id E)} {g = (id E)} → ext λ{ (id E) → refl}
    ; {f = (id V)} {g = (id V)} → ext λ{ (id V) → refl ; s → refl ; t → refl}
    ; {f = (id V)} {g = s} → ext λ{ (id E) → refl}
    ; {f = (id V)} {g = t} → ext λ{ (id E) → refl}
    ; {f = s} {g = (id E)} → ext λ{ (id E) → refl}
    ; {f = t} {g = (id E)} → ext λ{ (id E) → refl}
    }
  }

G₀ = map₀ G
G₁ = map₁ G

φ : {X : obj 𝕀}
  → G₀ X → Hom[ X ,-] ~ G
φ x = record
  { component = λ f → G₁ f x
  ; commute = λ
    { {f = (id E)} → ext λ{ (id E) → refl}
    ; {f = (id V)} → ext λ{ (id V) → refl ; s → refl ; t → refl}
    ; {f = s} → ext λ{ (id E) → refl}
    ; {f = t} → ext λ{ (id E) → refl}
    }
  }
    
ψ : {X : obj 𝕀}
  → Hom[ X ,-] ~ G → G₀ X
ψ {X = X} record { component = α }
  = α {a = X} (id X)

ψ∘φ : {X : obj 𝕀}
  → (e : G₀ X) → ψ (φ e) ≡ e
ψ∘φ {X = E} a = refl
ψ∘φ {X = E} b = refl
ψ∘φ {X = V} one = refl
ψ∘φ {X = V} two = refl
ψ∘φ {X = V} three = refl

postulate
  φ∘ψ : {X : obj 𝕀}
    → (nt : Hom[ X ,-] ~ G) → φ (ψ nt) ≡ nt
