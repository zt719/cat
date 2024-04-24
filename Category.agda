
module Category where

open import Base public

record Category {i} {j} : UU (lsuc (i ⊔ j)) where
  field  
    -- Components --
    obj : UU i
    hom : obj → obj → UU j
    id  : {a : obj} → hom a a
    _∘_ : {a b c : obj}
      → hom b c → hom a b → hom a c
    -- Category Laws -- 
    left-id  : {a b : obj} → (f : hom a b) → id ∘ f ≡ f
    right-id : {a b : obj} → (f : hom a b) → f ≡ f ∘ id
    assoc    : {a b c d : obj}
      → (f : hom c d) (g : hom b c) (h : hom a b)
      → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
open Category

SET : Category
SET
  = record
  { obj = UU
  ; hom = λ a b → (a → b)
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
M-+
  = record
  { obj = 𝟙
  ; hom = λ _ _ → ℕ
  ; id  = +-refl
  ; _∘_ = _+_
  ; left-id  = +-left-id
  ; right-id = +-right-id
  ; assoc    = +-assoc
  }

M-* : Category
M-*
  = record
  { obj = 𝟙
  ; hom = λ _ _ → ℕ
  ; id  = *-refl
  ; _∘_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }
    
_op : {i j : Level} → Category {i} {j} → Category {i} {j}
record { obj = obj ; hom = hom ; id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id ; assoc = assoc } op
  = record
     { obj = obj
     ; hom = λ a b  → hom b a
     ; id = id
     ; _∘_ = λ f g → g ∘ f
     ; left-id = λ f → ≡-sym (right-id f)
     ; right-id = λ f → ≡-sym (left-id f)
     ; assoc = λ f g h → ≡-sym (assoc h g f)
     }
