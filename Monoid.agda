module Monoid where

open import Base
open import Category

private variable i j k l : Level

record Monoid {i} : UU (lsuc i) where
  field
    -- Components --
    obj      : UU i
    ε        : obj 
    _⊕_      : obj → obj → obj

    -- Monoidal Laws --
    mon-left-id  : (a : obj) → ε ⊕ a ≡ a
    mon-right-id : (a : obj) → a ⊕ ε ≡ a
    mon-assoc    : (a b c : obj) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
open Monoid

-- Homomorphism between Monoids --
record _-m→_ (M : Monoid {i}) (N : Monoid {j}) : UU (i ⊔ j) where
  field
    map-obj : obj M → obj N 
    M-comp  : {a b : obj M}
      → map-obj ((_⊕_) M a b) ≡ (_⊕_) N (map-obj a) (map-obj b)

-m→-refl : {M : Monoid {i}} → M -m→ M
-m→-refl
  = record
  { map-obj = →-refl
  ; M-comp = ≡-refl
  }

-m→-trans : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}}
  → M -m→ N → N -m→ P → M -m→ P
-m→-trans
  record { map-obj = map-obj-MN ; M-comp = M-comp-MN }
  record { map-obj = map-obj-NP ; M-comp = M-comp-NP }
  = record
    { map-obj = map-obj-MN →∘ map-obj-NP
    ; M-comp = (cong map-obj-NP M-comp-MN) ≡∘ M-comp-NP
    }

_-m→∘_ = -m→-trans

postulate
  -m→-left-id : {M : Monoid {i}} {N : Monoid {j}}
    → (mm : M -m→ N)
    → -m→-trans -m→-refl mm ≡ mm

  -m→-right-id : {M : Monoid {i}} {N : Monoid {j}}
    → (mm : M -m→ N)
    → -m→-trans mm -m→-refl ≡ mm

  -m→-assoc : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}} {Q : Monoid {l}}
    → (pq : M -m→ N) → (np : N -m→ P) → (mn : P -m→ Q)
    → (pq -m→∘ np) -m→∘ mn ≡ pq -m→∘ (np -m→∘ mn)

MON : {i : Level} → Category {lsuc i} {i}
MON {i = i}
  = record
  { obj = Monoid {i}
  ; hom = _-m→_
  ; id  = -m→-refl
  ; _∘_ = -m→-trans
  ; cat-left-id  = -m→-left-id
  ; cat-right-id = -m→-right-id
  ; cat-assoc    = -m→-assoc
  }
      
ℕ-+-0-monoid : Monoid
ℕ-+-0-monoid
  = record
  { obj = ℕ
  ; ε   = 0
  ; _⊕_ = _+_
  ; mon-left-id  = +-left-id
  ; mon-right-id = +-right-id
  ; mon-assoc    = +-assoc
  }

ℕ-*-1-monoid : Monoid
ℕ-*-1-monoid
  = record
  { obj = ℕ
  ; ε   = 1
  ; _⊕_ = _*_
  ; mon-left-id  = *-left-id
  ; mon-right-id = *-right-id
  ; mon-assoc    = *-assoc
  }

free-monoid : {i : Level}
  → (A : UU i) → Monoid {i}
free-monoid A
  = record
  { obj = List A
  ; ε   = []
  ; _⊕_ = _++_
  ; mon-left-id  = ++-left-id
  ; mon-right-id = ++-right-id
  ; mon-assoc    = ++-assoc
  }
  
monoid-as-category : {i : Level}
  → Monoid {i} → Category {lzero} {i}
monoid-as-category
  record
  { obj = obj ; ε = ε ; _⊕_ = _⊕_
  ; mon-left-id = mon-left-id ; mon-right-id = mon-right-id ; mon-assoc = mon-assoc
  }
  = record
  { obj = 𝟙
  ; hom = λ _ _ → obj
  ; id  = ε
  ; _∘_ = _⊕_
  ; cat-left-id  = mon-left-id
  ; cat-right-id = mon-right-id
  ; cat-assoc    = mon-assoc
  }
