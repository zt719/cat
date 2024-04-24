module F-Algebra where

open import Base
open import Category
open import Functor
open import Universal

private variable i j : Level

-- F-Algebra --
record F-Alg (𝓒 : Category {i} {j}) (F : Endofunctor 𝓒) : UU (i ⊔ j) where
  open Category.Category 𝓒
  open Functor.Functor
  field
    carrier : obj
    eval    : hom (map F carrier) carrier
open F-Alg

-- Homomorphsim between F-Algebra
record F-Alg⇒ {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒}
  (Aα : F-Alg 𝓒 F) (Bβ : F-Alg 𝓒 F) : UU (i ⊔ j) where
  open Category.Category 𝓒
  open Functor.Functor
  open F-Alg Aα renaming (carrier to A; eval to α)
  open F-Alg Bβ renaming (carrier to B; eval to β)
  field
    f : hom A B
    f-law : f ∘ α ≡ β ∘ fmap F f
open F-Alg⇒

NatF : F-Alg SET maybe-functor
NatF = record { carrier = ℕ ; eval = λ{ (just x) → suc x ; nothing → zero } }

F-Alg⇒-refl : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒} {alg : F-Alg 𝓒 F} → F-Alg⇒ alg alg
F-Alg⇒-refl
  {𝓒 = record { id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id  }}
  {F = record { map-id = map-id }}
  {alg = record { eval = eval }}
    = record { f = id ; f-law = cong (eval ∘_) (≡-sym map-id) ≡∘ right-id eval ≡∘ left-id eval }

F-Alg⇒-trans : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒} {alg1 alg2 alg3 : F-Alg 𝓒 F }
  → F-Alg⇒ alg2 alg3 → F-Alg⇒ alg1 alg2 → F-Alg⇒ alg1 alg3
open Functor.Functor
F-Alg⇒-trans
  {𝓒 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = F}
  {alg1 = record { eval = α}}
  {alg2 = record { eval = β}}
  {alg3 = record { eval = γ}}
  record { f = f ; f-law = f-law }
  record { f = g ; f-law = g-law }
  = record
  { f = f ∘ g
  ; f-law = cong (γ ∘_) (≡-sym (map-comp F))
    ≡∘ assoc γ (fmap F f) (fmap F g)
    ≡∘ cong (_∘ fmap F g) f-law
    ≡∘ ≡-sym (assoc f β (fmap F g))
    ≡∘ cong (f ∘_) g-law
    ≡∘ assoc f g α
  }

postulate
  F-Alg⇒-left-id : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒} {alg1 alg2 : F-Alg 𝓒 F}
    → (alg⇒ : F-Alg⇒ alg1 alg2)
    → F-Alg⇒-trans F-Alg⇒-refl alg⇒ ≡ alg⇒

  F-Alg⇒-right-id : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒} {alg1 alg2 : F-Alg 𝓒 F}
    → (alg⇒ : F-Alg⇒ alg1 alg2)
    → alg⇒ ≡ F-Alg⇒-trans alg⇒ F-Alg⇒-refl

  F-Alg⇒-assoc : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒} {alg1 alg2 alg3 alg4 : F-Alg 𝓒 F}
    → (alg⇒1 : F-Alg⇒ alg3 alg4)
    → (alg⇒2 : F-Alg⇒ alg2 alg3)
    → (alg⇒3 : F-Alg⇒ alg1 alg2)    
    → F-Alg⇒-trans (F-Alg⇒-trans alg⇒1 alg⇒2) alg⇒3 ≡ F-Alg⇒-trans alg⇒1 (F-Alg⇒-trans alg⇒2 alg⇒3)

F-Alg-Cat : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒} → Category {i ⊔ j} {i ⊔ j}
F-Alg-Cat {𝓒 = 𝓒} {F = F} = record
             { obj = F-Alg 𝓒 F
             ; hom = F-Alg⇒
             ; id = F-Alg⇒-refl
             ; _∘_ = F-Alg⇒-trans
             ; left-id = F-Alg⇒-left-id
             ; right-id = F-Alg⇒-right-id
             ; assoc = F-Alg⇒-assoc
             }

{-
Lambek : {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒}
  → (init : Initial (F-Alg-Cat {𝓒 = 𝓒} {F = F}))
  → map F (carrier (Initial.initial init)) ≅ carrier (Initial.initial init)
Lambek = {!!}
-}
