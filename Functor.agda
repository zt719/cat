module Functor where

open import Category
open import Monoid

private variable i j k l : Level

record Functor (𝓒 : Category {i} {j} ) (𝓓 : Category {k} {l}) : UU (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category
  field
    -- Components --
    map-obj : obj 𝓒 → obj 𝓓
    map-morph : {A B : obj 𝓒} → hom 𝓒 A B → hom 𝓓 (map-obj A) (map-obj B)

    -- Functor Laws --
    F-id   : {A : obj 𝓒} → map-morph (id 𝓒 {A}) ≡ id 𝓓 {map-obj A}
    F-comp : {A B C : obj 𝓒} → (f : hom 𝓒 B C) → (g : hom 𝓒 A B)
      → map-morph ((_∘_) 𝓒 f g) ≡ (_∘_) 𝓓 (map-morph f) (map-morph g)
open Functor

Endofunctor : (𝓒 : Category {i} {j}) → UU (i ⊔ j)
Endofunctor 𝓒 = Functor 𝓒 𝓒

Maybe-map-morph : {A : UU i} {B : UU j}
  → (A → B) → Maybe A → Maybe B
Maybe-map-morph f (just x) = just (f x)
Maybe-map-morph f nothing  = nothing

Maybe-as-Functor : Endofunctor SET
Maybe-as-Functor
  = record
     { map-obj = Maybe
     ; map-morph = Maybe-map-morph
     ; F-id = ext λ{ (just x) → refl ; nothing → refl}
     ; F-comp = λ f g → ext (λ { (just x) → refl ; nothing → refl})
     }

List-map-morph : {A : UU i} {B : UU j}
  → (A → B) → List A → List B
List-map-morph f [] = []
List-map-morph f (x ∷ as) = f x ∷ List-map-morph f as

List-F-id' : {A : UU i}
  → (as : List A) → List-map-morph →-refl as ≡ →-refl as
List-F-id' [] = refl
List-F-id' (x ∷ as) = cong (→-refl x ∷_) (List-F-id' as)

List-F-comp' : {A : UU i} {B : UU j} {C : UU j}
  → (f : B → C)
  → (g : A → B)
  → (as : List A)
  → List-map-morph (→-trans f g) as ≡ →-trans (List-map-morph f) (List-map-morph g) as
List-F-comp' f g [] = refl
List-F-comp' f g (a ∷ as) = cong (→-trans f g a ∷_) (List-F-comp' f g as)

List-as-Functor : Endofunctor SET
List-as-Functor
  = record
  { map-obj = List
  ; map-morph = List-map-morph
  ; F-id = ext List-F-id'
  ; F-comp = λ f g → ext (List-F-comp' f g)
  }

Forgetful-Functor : Functor MON SET
Forgetful-Functor = record
  { map-obj = Monoid.obj
  ; map-morph = _-m→_.map-obj
  ; F-id = refl
  ; F-comp = λ f g → refl
  }
