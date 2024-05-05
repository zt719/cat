module Category.Monoid where

open import Agda.Primitive
open import Data.Equality
open import Data.Function
open import Data.Nat
open import Data.List
open import Data.Unit
open import Category.Category

private variable i j k l : Level

record Monoid : Set (lsuc i) where
  field
    obj      : Set i
    ε        : obj 
    _⊕_      : obj → obj → obj
    left-id  : (a : obj) → ε ⊕ a ≡ a
    right-id : (a : obj) → a ≡ a ⊕ ε
    assoc    : (a b c : obj) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
open Monoid

private variable M : Monoid {i}
private variable N : Monoid {j}
private variable P : Monoid {k}
private variable Q : Monoid {l}

record Monoid-Homomorphism (M : Monoid {i}) (N : Monoid {j}) : Set (i ⊔ j) where
  open Monoid M renaming (_⊕_ to _⊝_)
  open Monoid N renaming (_⊕_ to _⊛_)
  field
    map  : obj M → obj N
    map-⊕ : {a b : obj M}
      → map (a ⊝ b) ≡ map a ⊛ map b
open Monoid-Homomorphism

_-M→_ = Monoid-Homomorphism

mh-refl : M -M→ M
mh-refl = record { map = →-refl ; map-⊕ = ≡-refl }

mh-trans : N -M→ P → M -M→ N → M -M→ P
mh-trans
  record { map = map-f ; map-⊕ = map-⊕-f}
  record { map = map-g ; map-⊕ = map-⊕-g}
  = record
  { map = map-f →∘ map-g
  ; map-⊕ = map-⊕-f ∙ cong map-f map-⊕-g
  }

postulate
  mh-left-id : 
    (f : M -M→ N)
    → mh-trans mh-refl f ≡ f

  mh-right-id : 
    (f : M -M→ N)
    → f ≡ mh-trans f mh-refl

  mh-assoc :
    (f : P -M→ Q) (g : N -M→ P) (h : M -M→ N)
    → mh-trans (mh-trans f g) h ≡ mh-trans f (mh-trans g h)

MON : Category {lsuc i} {i}
MON {i}
  = record
  { obj = Monoid {i}
  ; hom = _-M→_
  ; id  = mh-refl
  ; _∘_ = mh-trans
  ; left-id  = mh-left-id
  ; right-id = mh-right-id
  ; assoc    = mh-assoc
  }
      
ℕ-+-monoid : Monoid
ℕ-+-monoid
  = record
  { obj = ℕ
  ; ε   = 0
  ; _⊕_ = _+_
  ; left-id  = +-left-id
  ; right-id = +-right-id
  ; assoc    = +-assoc
  }

ℕ-*-monoid : Monoid
ℕ-*-monoid
  = record
  { obj = ℕ
  ; ε   = 1
  ; _⊕_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }

free-monoid : Set i → Monoid {i}
free-monoid A
  = record
  { obj = List A
  ; ε   = []
  ; _⊕_ = _++_
  ; left-id  = ++-left-id
  ; right-id = ++-right-id
  ; assoc    = ++-assoc
  }
  
MONOID : Monoid {i} → Category
MONOID
  record
  { obj = obj ; ε = ε ; _⊕_ = _⊕_
  ; left-id = left-id ; right-id = right-id ; assoc = assoc
  }
  = record
  { obj = ⊤
  ; hom = λ _ _ → obj
  ; id  = ε
  ; _∘_ = _⊕_
  ; left-id  = left-id
  ; right-id = right-id
  ; assoc    = assoc
  }
