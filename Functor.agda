{-# OPTIONS --allow-unsolved-metas #-}

module Functor where

open import Base  
open import Category

open import Agda.Builtin.Maybe
  using (Maybe; nothing; just)

private variable i j k l : Level

record Functor (𝓒 : Category {i} {j} ) (𝓓 : Category {k} {l}) : UU (i ⊔ j ⊔ k ⊔ l) where
  field
    -- Components --
    F : obj 𝓒 → obj 𝓓
    F-map : {A B : obj 𝓒} → hom 𝓒 A B → hom 𝓓 (F A) (F B)

    -- Functor Laws --
    F-id   : {A : obj 𝓒} → F-map (id 𝓒 {A}) ≡ id 𝓓 {F A}
    F-comp : {A B C : obj 𝓒} → (f : hom 𝓒 B C) → (g : hom 𝓒 A B)
      → F-map ((_∘_) 𝓒 f g) ≡ (_∘_) 𝓓 (F-map f) (F-map g)
open Functor

postulate
  ext : {A : UU i} {B : UU j} {f g : A → B}
    → ((x : A) → f x ≡ g x) → f ≡ g

Maybe-F-map : {A : UU i} {B : UU j}
  → (A → B) → Maybe A → Maybe B
Maybe-F-map f (just x) = just (f x)
Maybe-F-map f nothing  = nothing

Maybe-is-Functor : Functor SET SET
Maybe-is-Functor
  = record
     { F = Maybe
     ; F-map = Maybe-F-map
     ; F-id = ext λ{ (just x) → refl ; nothing → refl}
     ; F-comp = λ f g → ext (λ { (just x) → refl ; nothing → refl})
     }

List-F-map : {A : UU i} {B : UU j}
  → (A → B) → List A → List B
List-F-map f [] = []
List-F-map f (x ∷ as) = f x ∷ List-F-map f as

List-F-id' : {A : UU i}
  → (as : List A) → List-F-map →-refl as ≡ →-refl as
List-F-id' [] = refl
List-F-id' (x ∷ as) = cong (→-refl x ∷_) (List-F-id' as)

List-F-comp' : {A : UU i} {B : UU j} {C : UU j}
  → (f : B → C)
  → (g : A → B)
  → (as : List A)
  → List-F-map (→-trans f g) as ≡ →-trans (List-F-map f) (List-F-map g) as
List-F-comp' f g [] = refl
List-F-comp' f g (a ∷ as) = cong (→-trans f g a ∷_) (List-F-comp' f g as)

List-is-Functor : Functor SET SET
List-is-Functor
  = record
  { F = List
  ; F-map = List-F-map
  ; F-id = ext List-F-id'
  ; F-comp = λ f g → ext (List-F-comp' f g)
  }
