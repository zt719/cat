
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
    cat-left-id  : {a b : obj} → (f : hom a b) → id ∘ f ≡ f
    cat-right-id : {a b : obj} → (f : hom a b) → f ∘ id ≡ f
    cat-assoc    : {a b c d : obj}
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
  ; cat-left-id = →-left-id
  ; cat-right-id = →-right-id
  ; cat-assoc = →-assoc
  }

ℕ-≤-preorder : Category
ℕ-≤-preorder
  = record
  { obj = ℕ
  ; hom = _≤_
  ; id = ≤-refl
  ; _∘_ = ≤-trans
  ; cat-left-id = ≤-left-id
  ; cat-right-id = ≤-right-id
  ; cat-assoc = ≤-assoc 
  }

-- Monoids as Categories
M-+ : Category
M-+
  = record
  { obj = 𝟙
  ; hom = λ _ _ → ℕ
  ; id  = 0
  ; _∘_ = _+_
  ; cat-left-id  = +-left-id
  ; cat-right-id = +-right-id
  ; cat-assoc    = +-assoc
  }

M-* : Category
M-*
  = record
  { obj = 𝟙
  ; hom = λ _ _ → ℕ
  ; id  = 1
  ; _∘_ = _*_
  ; cat-left-id  = *-left-id
  ; cat-right-id = *-right-id
  ; cat-assoc    = *-assoc
  }
    
_op : {i j : Level} → Category {i} {j} → Category {i} {j}
_op record { obj = obj ; hom = hom ; id = id ; _∘_ = _∘_ ; cat-left-id = cat-left-id ; cat-right-id = cat-right-id ; cat-assoc = cat-assoc }
  = record
  { obj = obj
  ; hom = λ a b → hom b a
  ; id  = id
  ; _∘_ = λ f g → g ∘ f
  ; cat-left-id  = cat-right-id
  ; cat-right-id = cat-left-id
  ; cat-assoc    = λ f g h → ≡-sym (cat-assoc h g f)
  }
