
module Category where

open import Base public

record Category {i} {j} : UU (lsuc (i ⊔ j)) where
  constructor Category_,_,_,_,_,_,_
  field  
    -- Components --
    obj : UU i
    hom : obj → obj → UU j
    id  : {a : obj} → hom a a
    _∘_ : {a b c : obj}
      → hom b c → hom a b → hom a c
    -- Category Laws -- 
    left-id  : {a b : obj} → (f : hom a b) → id ∘ f ≡ f
    right-id : {a b : obj} → (f : hom a b) → f ∘ id ≡ f
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
  { obj = ⊤
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
  { obj = ⊤
  ; hom = λ _ _ → ℕ
  ; id  = *-refl
  ; _∘_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }
    
_op : {i j : Level} → Category {i} {j} → Category {i} {j}
(Category obj , hom , id , _∘_ , left-id , right-id , assoc) op
  = Category obj , (λ a b → hom b a) , id , (λ f g → g ∘ f)
  , right-id , left-id , λ f g h → ≡-sym (assoc h g f)
