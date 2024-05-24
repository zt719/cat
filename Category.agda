module Category where

open import Base

record Category : Set (lsuc (i ⊔ j)) where
  field
    obj : Set i
    hom : obj → obj → Set j
    id  : {a : obj} → hom a a
    _∘_ : {a b c : obj}
      → hom b c → hom a b → hom a c

    left-id  : {a b : obj} (f : hom a b)
      → id ∘ f ≡ f
    right-id : {a b : obj} (f : hom a b)
      → f ≡ f ∘ id
    assoc    : {a b c d : obj} (f : hom c d) (g : hom b c) (h : hom a b)
      → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

SET : Category
SET
  = record
  { obj = Set
  ; hom = λ a b → (a → b)
  ; id = →-refl
  ; _∘_ = →-trans
  ; left-id = →-left-id
  ; right-id = →-right-id
  ; assoc = →-assoc
  }

PREORDER : Category
PREORDER
  = record
  { obj = ℕ
  ; hom = _≤_
  ; id = ≤-refl
  ; _∘_ = ≤-trans
  ; left-id = ≤-left-id
  ; right-id = ≤-right-id
  ; assoc = ≤-assoc 
  }

M+ : Category
M+
  = record
  { obj = ⊤
  ; hom = λ _ _ → ℕ
  ; id  = +-refl
  ; _∘_ = _+_
  ; left-id  = +-left-id
  ; right-id = +-right-id
  ; assoc    = +-assoc
  }

M* : Category
M*
  = record
  { obj = ⊤
  ; hom = λ _ _ → ℕ
  ; id  = *-refl
  ; _∘_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }

𝟘 : Category
𝟘 = record
  { obj = ⊥
  ; hom = _-⊥→_
  ; id = λ {}
  ; _∘_ = λ _ ()
  ; left-id = λ ()
  ; right-id = λ ()
  ; assoc = λ _ _ ()
  }

𝟙 : Category
𝟙 = record
  { obj = ⊤
  ; hom = _-⊤→_
  ; id = -tt→
  ; _∘_ = λ{ -tt→ -tt→ → -tt→ }
  ; left-id = λ{ -tt→ → refl }
  ; right-id = λ{ -tt→ → refl }
  ; assoc = λ{ -tt→ -tt→ -tt→ → refl }
  }

FIN : ℕ → Category
FIN k
  = record
  { obj = Fin k
  ; hom = Fin⇒ k
  ; id = Fin⇒-refl k
  ; _∘_ = Fin⇒-trans k
  ; left-id = Fin⇒-left-id k
  ; right-id = Fin⇒-right-id k
  ; assoc = Fin⇒-assoc k
  }

_op : Category {i} {j} → Category {i} {j}
record { obj = obj ; hom = hom ; id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id ; assoc = assoc } op
  = record
  { obj = obj
  ; hom = λ a b → hom b a
  ; id = id
  ; _∘_ = λ f g → g ∘ f
  ; left-id = λ f → ≡-sym (right-id f)
  ; right-id = λ f → ≡-sym (left-id f)
  ; assoc = λ f g h → ≡-sym (assoc h g f)
  }

PRODUCT :
  (𝔸 : Category {i} {j}) (B : Category {k} {l})
  → Category {i ⊔ k} {j ⊔ l}
PRODUCT
  record { obj = A ; hom = hom-𝔸 ; id = id-𝔸 ; _∘_ = _∘𝔸_ ; left-id = left-id-𝔸 ; right-id = right-id-𝔸 ; assoc = assoc-𝔸 }
  record { obj = B ; hom = hom-𝔹 ; id = id-𝔹 ; _∘_ = _∘𝔹_ ; left-id = left-id-𝔹 ; right-id = right-id-𝔹 ; assoc = assoc-𝔹 }
  = record
  { obj = A × B
  ; hom = λ{ (a1 , b1) (a2 , b2) → hom-𝔸 a1 a2 × hom-𝔹 b1 b2 }
  ; id = id-𝔸 , id-𝔹
  ; _∘_ = λ{ (fa , fb) (ga , gb) → (fa ∘𝔸 ga) , (fb ∘𝔹 gb) }
  ; left-id = λ{ (fa , fb) → cong₂ _,_ (left-id-𝔸 fa) (left-id-𝔹 fb) }
  ; right-id = λ{ (fa , fb) → cong₂ _,_ (right-id-𝔸 fa) (right-id-𝔹 fb) }
  ; assoc = λ{ (fa , fb) (ga , gb) (ha , hb) → cong₂ _,_ (assoc-𝔸 fa ga ha) (assoc-𝔹 fb gb hb) }
  }
