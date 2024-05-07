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

record _-Monoid→_ (M : Monoid {i}) (N : Monoid {j}) : Set (i ⊔ j) where
  open Monoid M renaming (_⊕_ to _⊝_; ε to m)
  open Monoid N renaming (_⊕_ to _⊛_; ε to n)
  field
    map  : obj M → obj N
    map-ε : map m ≡ n
    map-⊕ : {a b : obj M}
      → map (a ⊝ b) ≡ map a ⊛ map b
open _-Monoid→_

-m→-refl : M -Monoid→ M
-m→-refl
  = record
  { map = →-refl
  ; map-ε = ≡-refl
  ; map-⊕ = ≡-refl
  }

-m→-trans : N -Monoid→ P → M -Monoid→ N → M -Monoid→ P
-m→-trans
  record { map = map-f ; map-ε = map-ε-f ; map-⊕ = map-⊕-f}
  record { map = map-g ; map-ε = map-ε-g ; map-⊕ = map-⊕-g}
  = record
  { map = map-f →∘ map-g
  ; map-ε = map-ε-f ∙ cong map-f map-ε-g
  ; map-⊕ = map-⊕-f ∙ cong map-f map-⊕-g
  }

postulate
  -m→-left-id : 
    (f : M -Monoid→ N)
    → -m→-trans -m→-refl f ≡ f

  -m→-right-id : 
    (f : M -Monoid→ N)
    → f ≡ -m→-trans f -m→-refl

  -m→-assoc :
    (f : P -Monoid→ Q) (g : N -Monoid→ P) (h : M -Monoid→ N)
    → -m→-trans (-m→-trans f g) h ≡ -m→-trans f (-m→-trans g h)

MON : Category {lsuc i} {i}
MON {i}
  = record
  { obj = Monoid {i}
  ; hom = _-Monoid→_
  ; id  = -m→-refl
  ; _∘_ = -m→-trans
  ; left-id  = -m→-left-id
  ; right-id = -m→-right-id
  ; assoc    = -m→-assoc
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
