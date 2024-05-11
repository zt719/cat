module Category.Category where

open import Agda.Primitive
open import Data.Equality
open import Data.Function
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Fin
open import Data.Graph

private variable i j : Level

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
open Category  

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

-- Monoids as Categories
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

GRAPH : Category
GRAPH
  = record
  { obj = Point
  ; hom = Arrow
  ; id = arrow-refl
  ; _∘_ = arrow-trans
  ; left-id = arrow-left-id
  ; right-id = arrow-right-id
  ; assoc = arrow-assoc
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
