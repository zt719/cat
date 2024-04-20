{-# OPTIONS --allow-unsolved-metas #-}

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
    left-id  : (a : obj) → ε ⊕ a ≡ a
    right-id : (a : obj) → a ⊕ ε ≡ a
    assoc    : (a b c : obj) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
open Monoid

-- Homomorphism between Monoids --
record MH (M : Monoid {i}) (N : Monoid {j}) : UU (i ⊔ j) where
  constructor MH_,_
  field
    -- Component --
    map  : obj M → obj N

    -- Preserving Structure --
    map-comp : {a b : obj M} → map ((_⊕_) M a b) ≡ (_⊕_) N (map a) (map b)
open MH

mh-refl : {M : Monoid {i}} → MH M M
mh-refl = MH →-refl , ≡-refl

mh-trans : {M : Monoid {i}} {N : Monoid {j}} {P : Monoid {k}}
  → (f : MH N P) (g : MH M N) → MH M P
mh-trans
  (MH map-f , map-comp-f)
  (MH map-g , map-comp-g)
  = MH (map-f ← map-g) , (map-comp-f ≡∘ cong map-f map-comp-g)

_←mh-_ = mh-trans

mh-left-id : {M : Monoid {i}} {N : Monoid {j}}
  → (f : MH M N)
  → mh-refl ←mh- f ≡ f
mh-left-id (MH map-f , map-comp-f)
  = ≅-to-≡ (cong₂-h MH_,_ (≡-to-≅ (→-left-id map-f)) (≡-to-≅ {!≡-left-id map-comp-f!}))

mh-right-id : {M : Monoid {i}} {N : Monoid {j}}
  → (f : MH M N)
  → f ←mh- mh-refl ≡ f
mh-right-id (MH map-f , map-comp-f)
  = ≅-to-≡ (cong₂-h MH_,_ (≡-to-≅ (→-right-id map-f)) (≡-to-≅ {!≡-right-id map-comp-f!}))

mh-assoc : {l₁ l₂ l₃ l₄ : Level}
  → {M : Monoid {l₁}} {N : Monoid {l₂}} {P : Monoid {l₃}} {Q : Monoid {l₄}}
  → (f : MH P Q) (g : MH N P) (h : MH M N)
  → (f ←mh- g) ←mh- h ≡ f ←mh- (g ←mh- h)
mh-assoc
  (MH map-f , map-comp-f)
  (MH map-g , map-comp-g)
  (MH map-h , map-comp-h)
  = ≅-to-≡ (cong₂-h MH_,_ (≡-to-≅ (→-assoc map-f map-g map-h)) (≡-to-≅ {!!}))

MON : Category {lsuc i} {i}
MON {i = i}
  = record
  { obj = Monoid {i}
  ; hom = MH
  ; id  = mh-refl
  ; _∘_ = mh-trans
  ; left-id  = mh-left-id
  ; right-id = mh-right-id
  ; assoc    = mh-assoc
  }
      
ℕ-+-0-monoid : Monoid
ℕ-+-0-monoid
  = record
  { obj = ℕ
  ; ε   = 0
  ; _⊕_ = _+_
  ; left-id  = +-left-id
  ; right-id = +-right-id
  ; assoc    = +-assoc
  }

ℕ-*-1-monoid : Monoid
ℕ-*-1-monoid
  = record
  { obj = ℕ
  ; ε   = 1
  ; _⊕_ = _*_
  ; left-id  = *-left-id
  ; right-id = *-right-id
  ; assoc    = *-assoc
  }

free-monoid : (A : UU i) → Monoid {i}
free-monoid A
  = record
  { obj = List A
  ; ε   = []
  ; _⊕_ = _++_
  ; left-id  = ++-left-id
  ; right-id = ++-right-id
  ; assoc    = ++-assoc
  }
  
monoid-as-category : Monoid {i} → Category
monoid-as-category
  record
  { obj = obj ; ε = ε ; _⊕_ = _⊕_
  ; left-id = left-id ; right-id = right-id ; assoc = assoc
  }
  = record
  { obj = 𝟙
  ; hom = λ _ _ → obj
  ; id  = ε
  ; _∘_ = _⊕_
  ; left-id  = left-id
  ; right-id = right-id
  ; assoc    = assoc
  }

record Test : UU (lsuc i) where
  field
    t : UU i
    ft : UU i → UU i → UU i
open Test

