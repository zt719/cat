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
    left-id  : (x : obj) → ε ⊕ x ≡ x
    right-id : (x : obj) → x ⊕ ε ≡ x
    assoc    : (x y z : obj) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
open Monoid

-- Homomorphism between Monoids --
record _-m→_ (M : Monoid {i}) (N : Monoid {j}) : UU (i ⊔ j) where
  field
    map-obj : obj M → obj N 
    M-comp : {A B : obj M}
      → map-obj ((_⊕_) M A B) ≡ (_⊕_) N (map-obj A) (map-obj B)

-m→-refl : {M : Monoid {i}} → M -m→ M
-m→-refl = record { map-obj = →-refl ; M-comp = ≡-refl }

-m→-trans : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}}
  → N -m→ P → M -m→ N → M -m→ P
-m→-trans
  record { map-obj = map-obj-NP ; M-comp = M-comp-NP }
  record { map-obj = map-obj-MN ; M-comp = M-comp-MN }
  = record
    { map-obj = →-trans map-obj-NP map-obj-MN
    ; M-comp = ≡-trans M-comp-NP (cong map-obj-NP M-comp-MN)
    }

postulate
  -m→-left-id : {M : Monoid {i}} {N : Monoid {j}}
    → (mm : M -m→ N)
    → -m→-trans -m→-refl mm ≡ mm

  -m→-right-id : {M : Monoid {i}} {N : Monoid {j}}
    → (mm : M -m→ N)
    → -m→-trans mm -m→-refl ≡ mm

  -m→-assoc : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}} {Q : Monoid {l}}
    → (pq : P -m→ Q) → (np : N -m→ P) → (mn : M -m→ N)
    → -m→-trans (-m→-trans pq np) mn ≡ -m→-trans pq (-m→-trans np mn)

MON : {i : Level} → Category {lsuc i} {i}
MON {i = i} = record
       { obj = Monoid {i}
       ; hom = _-m→_
       ; id = -m→-refl
       ; _∘_ = -m→-trans
       ; left-id = -m→-left-id
       ; right-id = -m→-right-id
       ; assoc = -m→-assoc
       }
      
ℕ-+-0-monoid : Monoid
ℕ-+-0-monoid
  = record
     { obj = ℕ
     ; ε = 0
     ; _⊕_ = _+_
     ; left-id = +-left-id
     ; right-id = +-right-id
     ; assoc = +-assoc
     }

ℕ-*-1-monoid : Monoid
ℕ-*-1-monoid
  = record
     { obj = ℕ
     ; ε = 1
     ; _⊕_ = _*_
     ; left-id = *-left-id
     ; right-id = *-right-id
     ; assoc = *-assoc
     }

free-monoid : {i : Level}
  → (A : UU i) → Monoid {i}
free-monoid A
  = record
     { obj = List A
     ; ε = []
     ; _⊕_ = _++_
     ; left-id = ++-left-id
     ; right-id = ++-right-id
     ; assoc = ++-assoc
     }
  
monoid-as-category : {i : Level}
  → Monoid {i} → Category {lzero} {i}
monoid-as-category
  record
    { obj = obj ; ε = ε ; _⊕_ = _⊕_
    ; left-id = left-id ; right-id = right-id ; assoc = assoc
    }
  = record
     { obj = 𝟙
     ; hom = λ _ _ → obj
     ; id = ε
     ; _∘_ = _⊕_
     ; left-id = left-id
     ; right-id = right-id
     ; assoc = assoc
     }
