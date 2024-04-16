module Category where

open import Base public

record Category {i} {j} : UU (lsuc (i ⊔ j)) where
  field
  
    -- Components --
    obj : UU i
    hom : obj → obj → UU j
    id  : {A : obj} → hom A A
    _∘_ : {A B C : obj}
      → hom B C → hom A B → hom A C
      
    -- Category Laws -- 
    left-id  : {A B : obj} → (f : hom A B) → id ∘ f ≡ f
    right-id : {A B : obj} → (f : hom A B) → f ∘ id ≡ f
    assoc    : {A B C D : obj}
      → (f : hom C D) (g : hom B C) (h : hom A B)
      → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
open Category public

_⇒_ : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ⇒ B = A → B

SET : {i : Level} → Category {lsuc i} {i}
SET {i} = record
       { obj = UU i
       ; hom = _⇒_
       ; id = →-refl
       ; _∘_ = →-trans
       ; left-id = →-left-id
       ; right-id = →-right-id
       ; assoc = →-assoc
       }

ℕ-≤-preorder : Category
ℕ-≤-preorder
  = record
     { obj = ℕ
     ; hom = _≤_
     ; id = ≤-refl
     ; _∘_ = ≤-trans
     ; left-id = ≤-left-id
     ; right-id = ≤-right-id
     ; assoc = ≤-assoc 
     }

-- Monoids as Categories
M-+ : Category
M-+ =
  record
    { obj = 𝟙
    ; hom = λ _ _ → ℕ
    ; id  = 0
    ; _∘_ = _+_
    ; left-id  = +-left-id
    ; right-id = +-right-id
    ; assoc    = +-assoc
    }

M-* : Category
M-* =
  record
    { obj = 𝟙
    ; hom = λ _ _ → ℕ
    ; id  = 1
    ; _∘_ = _*_
    ; left-id  = *-left-id
    ; right-id = *-right-id
    ; assoc    = *-assoc
    }
    
_op : {i j : Level} → Category {i} {j} → Category {i} {j}
record { obj = obj ; hom = hom ; id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id ; assoc = assoc } op
  = record
     { obj = obj
     ; hom = λ A B → hom B A
     ; id  = id
     ; _∘_ = λ f g → g ∘ f
     ; left-id  = right-id
     ; right-id = left-id
     ; assoc    = λ f g h → ≡-sym (assoc h g f)
     }
