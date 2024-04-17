module Functor where

open import Category
open import Monoid

private variable i j k l m n : Level

record Functor (𝓒 : Category {i} {j} ) (𝓓 : Category {k} {l}) : UU (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category 𝓒
  open Category.Category 𝓓
  field
    -- Components --
    map : obj 𝓒 → obj 𝓓
    fmap : {a b : obj 𝓒} → hom 𝓒 a b → hom 𝓓 (map a) (map b)

    -- Functor Laws --
    func-id-law   : {a : obj 𝓒} → fmap (id 𝓒 {a}) ≡ id 𝓓 {map a}
    func-comp-law : {a b c : obj 𝓒} {f : hom 𝓒 a b} {g : hom 𝓒 b c}
      → fmap ((_∘_) 𝓒 f g) ≡ (_∘_) 𝓓 (fmap f) (fmap g)
open Functor

Endofunctor : (𝓒 : Category {i} {j}) → UU (i ⊔ j)
Endofunctor 𝓒 = Functor 𝓒 𝓒

func-refl : {𝓒 : Category {i} {j}}
  → Functor 𝓒 𝓒
func-refl
  = record
  { map  = →-refl
  ; fmap = →-refl
  ; func-id-law   = ≡-refl
  ; func-comp-law = ≡-refl
  }

func-trans : 
  {𝓒 : Category {i} {j}} {𝓓 : Category {k} {l}} {𝓔 : Category {m} {n}}
  → Functor 𝓒 𝓓 → Functor 𝓓 𝓔 → Functor 𝓒 𝓔
open Category.Category
func-trans
  record { map = map-F ; fmap = fmap-F ; func-id-law = func-id-law-F ; func-comp-law = func-comp-law-F }
  record { map = map-G ; fmap = fmap-G ; func-id-law = func-id-law-G ; func-comp-law = func-comp-law-G }
  = record
  { map  = map-F →∘ map-G
  ; fmap = fmap-F →∘ fmap-G
  ; func-id-law   = (cong fmap-G func-id-law-F) ≡∘ func-id-law-G 
  ; func-comp-law = (cong fmap-G func-comp-law-F) ≡∘ func-comp-law-G
  }

maybe-functor : Endofunctor SET
maybe-functor
  = record
  { map  = Maybe
  ; fmap = maybe-fmap
  ; func-id-law = ext λ{ (just x) → refl ; nothing → refl}
  ; func-comp-law = ext (λ { (just x) → refl ; nothing → refl})
  }
  where
  maybe-fmap : {A : UU i} {B : UU j}
    → (A → B) → Maybe A → Maybe B
  maybe-fmap f (just x) = just (f x)
  maybe-fmap f nothing  = nothing

list-functor : Endofunctor SET
list-functor
  = record
  { map  = List
  ; fmap = list-fmap
  ; func-id-law = ext list-func-id-law'
  ; func-comp-law = ext list-func-comp-law'
  }
  where
  list-fmap : {A : UU i} {B : UU j}
    → (A → B) → List A → List B
  list-fmap f [] = []
  list-fmap f (x ∷ as) = f x ∷ list-fmap f as
  
  list-func-id-law' : {a : UU i}
    → (as : List a) → list-fmap →-refl as ≡ →-refl as
  list-func-id-law' [] = refl
  list-func-id-law' (x ∷ as) = cong (→-refl x ∷_) (list-func-id-law' as)
  
  list-func-comp-law' : {A : UU i} {B : UU j} {C : UU j}
    → {f : A → B} {g : B → C}
    → (as : List A)
    → list-fmap (→-trans f g) as ≡ →-trans (list-fmap f) (list-fmap g) as
  list-func-comp-law' [] = refl
  list-func-comp-law' {f = f} {g = g} (a ∷ as) = cong (→-trans f g a ∷_) (list-func-comp-law' as)

forgetful-functor : Functor MON SET
forgetful-functor = record
  { map  = Monoid.obj
  ; fmap = _-m→_.map-obj
  ; func-id-law = refl
  ; func-comp-law = refl
  }

identity-functor :
  (𝓒 : Category {i} {j})
  → Endofunctor 𝓒
identity-functor 𝓒 = func-refl


