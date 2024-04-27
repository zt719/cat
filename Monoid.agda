module Monoid where

open import Base
open import Category

record Monoid {i} : Set (lsuc i) where
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

-- Homomorphism between Monoids --
record Monoid-Homomorphism (M : Monoid {i}) (N : Monoid {j}) : Set (i ⊔ j) where
  field
    map  : obj M → obj N
    comp-law : {a b : obj M} → map ((_⊕_) M a b) ≡ (_⊕_) N (map a) (map b)
open Monoid-Homomorphism

_-M→_ = Monoid-Homomorphism

mh-refl : M -M→ M
mh-refl = record { map = →-refl ; comp-law = ≡-refl }

mh-trans : N -M→ P → M -M→ N → M -M→ P
mh-trans
  record { map = map-f ; comp-law = comp-law-f}
  record { map = map-g ; comp-law = comp-law-g}
  = record
  { map = map-f ←∘- map-g
  ; comp-law = comp-law-f ∙ cong map-f comp-law-g
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
      
ℕ-+-0-monoid : Monoid
ℕ-+-0-monoid
  = record
  { obj = Nat
  ; ε   = 0
  ; _⊕_ = _+_
  ; left-id  = +-left-id
  ; right-id = +-right-id
  ; assoc    = +-assoc
  }

Nat-*-1-monoid : Monoid
Nat-*-1-monoid
  = record
  { obj = Nat
  ; ε   = 1
  ; _⊕_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }

free-monoid : (A : Set i) → Monoid {i}
free-monoid A
  = record
  { obj = List A
  ; ε   = []
  ; _⊕_ = _++_
  ; left-id  = ++-left-id
  ; right-id = ++-right-id
  ; assoc    = ++-assoc
  }
  
monoid-as-category : Monoid {i} → Category
monoid-as-category
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
