module Monoid where

open import Base
open import Category

record Mon : Set (lsuc i) where
  field
    obj      : Set i
    ε        : obj 
    _⊕_      : obj → obj → obj
    left-id  : (a : obj) → ε ⊕ a ≡ a
    right-id : (a : obj) → a ≡ a ⊕ ε
    assoc    : (a b c : obj) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
open Mon

private variable M : Mon {i}
private variable N : Mon {j}
private variable P : Mon {k}
private variable Q : Mon {l}

record _-Mon→_ (M : Mon {i}) (N : Mon {j}) : Set (i ⊔ j) where
  open Mon M renaming (_⊕_ to _⊝_; ε to εm)
  open Mon N renaming (_⊕_ to _⊛_; ε to εn)
  field
    map  : obj M → obj N
    map-ε : map εm ≡ εn
    map-⊕ : {a b : obj M}
      → map (a ⊝ b) ≡ map a ⊛ map b
open _-Mon→_

-m→-refl : M -Mon→ M
-m→-refl
  = record
  { map = →-refl
  ; map-ε = ≡-refl
  ; map-⊕ = ≡-refl
  }

-m→-trans : N -Mon→ P → M -Mon→ N → M -Mon→ P
-m→-trans
  record { map = map-f ; map-ε = map-ε-f ; map-⊕ = map-⊕-f}
  record { map = map-g ; map-ε = map-ε-g ; map-⊕ = map-⊕-g}
  = record
  { map = map-f →∘ map-g
  ; map-ε = map-ε-f ∙ cong map-f map-ε-g
  ; map-⊕ = map-⊕-f ∙ cong map-f map-⊕-g
  }

postulate
  -m→-left-id : 
    (f : M -Mon→ N)
    → -m→-trans -m→-refl f ≡ f

  -m→-right-id : 
    (f : M -Mon→ N)
    → f ≡ -m→-trans f -m→-refl

  -m→-assoc :
    (f : P -Mon→ Q) (g : N -Mon→ P) (h : M -Mon→ N)
    → -m→-trans (-m→-trans f g) h ≡ -m→-trans f (-m→-trans g h)

MON : Category {lsuc i} {i}
MON {i}
  = record
  { obj = Mon {i}
  ; hom = _-Mon→_
  ; id  = -m→-refl
  ; _∘_ = -m→-trans
  ; left-id  = -m→-left-id
  ; right-id = -m→-right-id
  ; assoc    = -m→-assoc
  }
      
ℕ-+-monoid : Mon
ℕ-+-monoid
  = record
  { obj = ℕ
  ; ε   = 0
  ; _⊕_ = _+_
  ; left-id  = +-left-id
  ; right-id = +-right-id
  ; assoc    = +-assoc
  }

ℕ-*-monoid : Mon
ℕ-*-monoid
  = record
  { obj = ℕ
  ; ε   = 1
  ; _⊕_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }

free-monoid : Set i → Mon {i}
free-monoid A
  = record
  { obj = List A
  ; ε   = []
  ; _⊕_ = _++_
  ; left-id  = ++-left-id
  ; right-id = ++-right-id
  ; assoc    = ++-assoc
  }
  
MONOID : Mon {i} → Category
MONOID
  record
  { obj = obj ; ε = ε ; _⊕_ = _⊕_
  ; left-id = left-id ; right-id = right-id ; assoc = assoc
  }
  = record
  { obj = ⊤
  ; hom = λ _ _ → obj
  ; id  = ε
  ; _∘_ = _⊕_
  ; left-id  = left-id
  ; right-id = right-id
  ; assoc    = assoc
  }

record CMon : Set (lsuc i) where
  field
    obj      : Set i
    ε        : obj 
    _⊕_      : obj → obj → obj
    left-id  : (a : obj) → ε ⊕ a ≡ a
    right-id : (a : obj) → a ≡ a ⊕ ε
    assoc    : (a b c : obj) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    sym      : (a b : obj) → a ⊕ b ≡ b ⊕ a
open CMon

lemma : {A : Set i} {B : Set j} {a b : A} {c d : B}
  → (p : a ≡ b) (q : c ≡ d)
  → (a , c) ≡ (b , d)
lemma refl refl = refl

PMon : Mon {i} → Mon {j} → Mon {i ⊔ j}
PMon
  record { obj = obj ; ε = ε ; _⊕_ = _+_ ; left-id = left-id ; right-id = right-id ; assoc = assoc }
  record { obj = obj₁ ; ε = ε₁ ; _⊕_ = _*_ ; left-id = left-id₁ ; right-id = right-id₁ ; assoc = assoc₁ }
  = record
     { obj = obj × obj₁
     ; ε = (ε , ε₁)
     ; _⊕_ = λ{ (a , b) (a₁ , b₁) → (a + a₁ , b * b₁) }
     ; left-id = λ{ (a , a₁) → lemma (left-id a) (left-id₁ a₁) }
     ; right-id = λ{ (a , a₁) → lemma (right-id a) (right-id₁ a₁)}
     ; assoc = λ{ (a , a₁) (b , b₁) (c , c₁) → lemma (assoc a b c) (assoc₁ a₁ b₁ c₁) }
     }

PCMon : CMon {i} → CMon {j} → CMon {i ⊔ j}
PCMon
  record { obj = obj ; ε = ε ; _⊕_ = _+_ ; left-id = left-id ; right-id = right-id ; assoc = assoc ; sym = sym}
  record { obj = obj₁ ; ε = ε₁ ; _⊕_ = _*_ ; left-id = left-id₁ ; right-id = right-id₁ ; assoc = assoc₁ ; sym = sym₁}
  = record
     { obj = obj × obj₁
     ; ε = (ε , ε₁)
     ; _⊕_ = λ{ (a , b) (a₁ , b₁) → (a + a₁ , b * b₁) }
     ; left-id = λ{ (a , a₁) → lemma (left-id a) (left-id₁ a₁) }
     ; right-id = λ{ (a , a₁) → lemma (right-id a) (right-id₁ a₁)}
     ; assoc = λ{ (a , a₁) (b , b₁) (c , c₁) → lemma (assoc a b c) (assoc₁ a₁ b₁ c₁) }
     ; sym = λ{ (a , a₁) (b , b₁) → lemma (sym a b) (sym₁ a₁ b₁) }
     }

record _-CMon→_ (M : CMon {i}) (N : CMon {j}) : Set (i ⊔ j) where
  open CMon M renaming (_⊕_ to _⊝_; ε to εm)
  open CMon N renaming (_⊕_ to _⊛_; ε to εn)
  field
    map  : obj M → obj N
    map-ε : map εm ≡ εn
    map-⊕ : {a b : obj M}
      → map (a ⊝ b) ≡ map a ⊛ map b

prjCMonˡ : {M : CMon {i}} {N : CMon {j}}
  → PCMon M N -CMon→ M
prjCMonˡ = record
  { map = proj₁
  ; map-ε = refl
  ; map-⊕ = refl
  }

injCMonˡ : {M : CMon {i}} {N : CMon {j}}
  → M -CMon→ PCMon M N
injCMonˡ
  {N = record { ε = ε ; right-id = right-id }}
  = record
  { map = λ x → (x , ε)
  ; map-ε = refl
  ; map-⊕ = lemma refl (right-id ε)
  }
