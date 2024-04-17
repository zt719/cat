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

record MM (M : Monoid {i}) (N : Monoid {j}) : UU (i ⊔ j) where
  field
    map-obj : obj M → obj N 
    preserve-comp : {A B : obj M}
      → map-obj ((_⊕_) M A B) ≡ (_⊕_) N (map-obj A) (map-obj B)

MM-refl : {M : Monoid {i}} → MM M M
MM-refl = record { map-obj = →-refl ; preserve-comp = ≡-refl }

MM-trans : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}}
  → MM N P → MM M N → MM M P
MM-trans
  record { map-obj = map-obj-NP ; preserve-comp = preserve-comp-NP }
  record { map-obj = map-obj-MN ; preserve-comp = preserve-comp-MN }
  = record
    { map-obj = →-trans map-obj-NP map-obj-MN
    ; preserve-comp = ≡-trans preserve-comp-NP (cong map-obj-NP preserve-comp-MN)
    }

MM-left-id : {M : Monoid {i}} {N : Monoid {j}}
  → (mm : MM M N)
  → MM-trans MM-refl mm ≡ mm
MM-left-id record { map-obj = map-obj ; preserve-comp = preserve-comp }
  = {!!}

MM-right-id : {M : Monoid {i}} {N : Monoid {j}}
  → (mm : MM M N)
  → MM-trans mm MM-refl ≡ mm
MM-right-id record { map-obj = map-obj ; preserve-comp = preserve-comp }
  = {!!}

MM-assoc : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}} {Q : Monoid {l}}
  → (pq : MM P Q) → (np : MM N P) → (mn : MM M N)
  → MM-trans (MM-trans pq np) mn ≡ MM-trans pq (MM-trans np mn)
MM-assoc pq np mn
  = {!!}

Mon : Category
Mon = record
       { obj = Monoid
       ; hom = MM
       ; id = MM-refl
       ; _∘_ = MM-trans
       ; left-id = MM-left-id
       ; right-id = MM-right-id
       ; assoc = MM-assoc
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
  record { obj = obj ; ε = ε ; _⊕_ = _⊕_ ; left-id = left-id ; right-id = right-id ; assoc = assoc }
  = record
     { obj = 𝟙
     ; hom = λ _ _ → obj
     ; id = ε
     ; _∘_ = _⊕_
     ; left-id = left-id
     ; right-id = right-id
     ; assoc = assoc
     }
