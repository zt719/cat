module F-Algebra where

open import Base
open import Category
open import Functor
open import Universal

-- F-Algebra --
record F-Alg (ℂ : Category {i} {j}) (F : Endofunctor ℂ) : Set (i ⊔ j) where
  open Category.Category ℂ
  open Functor.Functor
  field
    carrier : obj
    eval    : hom (map F carrier) carrier
open F-Alg

-- Homomorphsim between F-Algebra
record F-Alg⇒ {ℂ : Category {i} {j}} {F : Endofunctor ℂ}
  (Aα : F-Alg ℂ F) (Bβ : F-Alg ℂ F) : Set (i ⊔ j) where
  open Category.Category ℂ
  open Functor.Functor
  open F-Alg Aα renaming (carrier to A; eval to α)
  open F-Alg Bβ renaming (carrier to B; eval to β)
  field
    f : hom A B
    f-law : f ∘ α ≡ β ∘ fmap F f
open F-Alg⇒

NatF : F-Alg SET maybe-functor
NatF = record { carrier = Nat ; eval = λ{ (just x) → suc x ; nothing → zero } }

F-Alg⇒-refl : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg : F-Alg ℂ F} → F-Alg⇒ alg alg
F-Alg⇒-refl
  {ℂ = record { id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id  }}
  {F = record { id-law = id-law }}
  {alg = record { eval = eval }}
    = record { f = id ; f-law = cong (eval ∘_) (≡-sym id-law) ∙ right-id eval ∙ left-id eval }

F-Alg⇒-trans : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 alg3 : F-Alg ℂ F }
  → F-Alg⇒ alg2 alg3 → F-Alg⇒ alg1 alg2 → F-Alg⇒ alg1 alg3
open Functor.Functor
F-Alg⇒-trans
  {ℂ = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = F}
  {alg1 = record { eval = α}}
  {alg2 = record { eval = β}}
  {alg3 = record { eval = γ}}
  record { f = f ; f-law = f-law }
  record { f = g ; f-law = g-law }
  = record
  { f = f ∘ g
  ; f-law = cong (γ ∘_) (≡-sym (trans-law F))
    ∙ assoc γ (fmap F f) (fmap F g)
    ∙ cong (_∘ fmap F g) f-law
    ∙ ≡-sym (assoc f β (fmap F g))
    ∙ cong (f ∘_) g-law
    ∙ assoc f g α
  }

postulate
  F-Alg⇒-left-id : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 : F-Alg ℂ F}
    → (alg⇒ : F-Alg⇒ alg1 alg2)
    → F-Alg⇒-trans F-Alg⇒-refl alg⇒ ≡ alg⇒

  F-Alg⇒-right-id : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 : F-Alg ℂ F}
    → (alg⇒ : F-Alg⇒ alg1 alg2)
    → alg⇒ ≡ F-Alg⇒-trans alg⇒ F-Alg⇒-refl

  F-Alg⇒-assoc : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 alg3 alg4 : F-Alg ℂ F}
    → (alg⇒1 : F-Alg⇒ alg3 alg4)
    → (alg⇒2 : F-Alg⇒ alg2 alg3)
    → (alg⇒3 : F-Alg⇒ alg1 alg2)    
    → F-Alg⇒-trans (F-Alg⇒-trans alg⇒1 alg⇒2) alg⇒3 ≡ F-Alg⇒-trans alg⇒1 (F-Alg⇒-trans alg⇒2 alg⇒3)

F-Alg-Cat : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} → Category {i ⊔ j} {i ⊔ j}
F-Alg-Cat {ℂ = ℂ} {F = F} = record
             { obj = F-Alg ℂ F
             ; hom = F-Alg⇒
             ; id = F-Alg⇒-refl
             ; _∘_ = F-Alg⇒-trans
             ; left-id = F-Alg⇒-left-id
             ; right-id = F-Alg⇒-right-id
             ; assoc = F-Alg⇒-assoc
             }

{-
Lambek : {ℂ : Category {i} {j}} {F : Endofunctor ℂ}
  → (init : Initial (F-Alg-Cat {ℂ = ℂ} {F = F}))
  → map F (carrier (Initial.initial init)) ≅ carrier (Initial.initial init)
Lambek = {!!}
-}
