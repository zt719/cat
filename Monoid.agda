module Monoid where

open import Base
open import Category

record Monoid {i} : UU (lsuc i) where
  field
    obj      : UU i
    ε        : obj 
    _⊕_      : obj → obj → obj
    left-id  : (x : obj) → ε ⊕ x ≡ x
    right-id : (x : obj) → x ⊕ ε ≡ x
    assoc    : (x y z : obj) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
open Monoid

record MM {i j : Level}
  (M : Monoid {i})
  (N : Monoid {j})
  : UU (i ⊔ j) where
  field
    map-obj : obj M → obj N 
    preserve-comp : {A B : obj M}
      → map-obj ((_⊕_) M A B) ≡ (_⊕_) N (map-obj A) (map-obj B)

Id : {i : Level} {A : UU i}
  → A → A
Id a = a

MM-refl : {i : Level} {M : Monoid {i}} → MM M M
MM-refl = record { map-obj = Id ; preserve-comp = refl }

MM-trans : {i j k : Level} {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}}
  → MM N P → MM M N → MM M P
MM-trans
  record { map-obj = map-obj-NP ; preserve-comp = preserve-comp-NP }
  record { map-obj = map-obj-MN ; preserve-comp = preserve-comp-MN }
  = record
    { map-obj = λ x → map-obj-NP (map-obj-MN x)
    ; preserve-comp = {!!}
    }


Mon : Category
Mon = record
       { obj = Monoid
       ; hom = MM
       ; id = MM-refl
       ; _∘_ = {!!}
       ; left-id = {!!}
       ; right-id = {!!}
       ; assoc = {!!}
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
