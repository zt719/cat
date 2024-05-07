module Category.F-Algebra where

open import Agda.Primitive
open import Data.Equality
open import Data.Nat
open import Data.Maybe
open import Category.Category
open import Category.Functor
open import Category.Universal

private variable i j : Level

record F-Alg (ℂ : Category {i} {j}) (F : Endofunctor ℂ) : Set (i ⊔ j) where
  open Category.Category.Category ℂ
  open Category.Functor.Functor F renaming (map₀ to F₀)
  field
    carrier : obj
    eval    : hom (F₀ carrier) carrier
open F-Alg

record -F-Alg→ {ℂ : Category {i} {j}} {F : Endofunctor ℂ}
  (Aα : F-Alg ℂ F) (Bβ : F-Alg ℂ F) : Set (i ⊔ j) where
  open Category.Category.Category ℂ using (hom; _∘_)
  open Category.Functor.Functor F renaming (map₁ to F₁)
  open F-Alg Aα renaming (carrier to A; eval to α)
  open F-Alg Bβ renaming (carrier to B; eval to β)
  field
    f : hom A B
    commute : f ∘ α ≡ β ∘ F₁ f
open -F-Alg→

ℕF : F-Alg SET maybe-functor
ℕF = record { carrier = ℕ ; eval = λ{ (just x) → suc x ; nothing → zero } }

-F-Alg→-refl : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg : F-Alg ℂ F} → -F-Alg→ alg alg
-F-Alg→-refl
  {ℂ = record { id = id ; _∘_ = _∘_ ; left-id = left-id ; right-id = right-id  }}
  {F = record { map-id = map-id }}
  {alg = record { eval = α }}
    = record { f = id ; commute = cong (α ∘_) (≡-sym map-id) ∙ right-id α ∙ left-id α }

-F-Alg→-trans : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 alg3 : F-Alg ℂ F }
  → -F-Alg→ alg2 alg3 → -F-Alg→ alg1 alg2 → -F-Alg→ alg1 alg3
-F-Alg→-trans
  {ℂ = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = record { map₁ = F₁ ; map-∘ = map-∘}}
  {alg1 = record { eval = α}}
  {alg2 = record { eval = β}}
  {alg3 = record { eval = γ}}
  record { f = f ; commute = commute-f }
  record { f = g ; commute = commute-g }
  = record
  { f = f ∘ g
  ; commute = cong (γ ∘_) (≡-sym (map-∘))
    ∙ assoc γ (F₁ f) (F₁ g)
    ∙ cong (_∘ F₁ g) commute-f
    ∙ ≡-sym (assoc f β (F₁ g))
    ∙ cong (f ∘_) commute-g
    ∙ assoc f g α
  }

postulate
  -F-Alg→-left-id : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 : F-Alg ℂ F}
    → (alg⇒ : -F-Alg→ alg1 alg2)
    → -F-Alg→-trans -F-Alg→-refl alg⇒ ≡ alg⇒

  -F-Alg→-right-id : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 : F-Alg ℂ F}
    → (alg⇒ : -F-Alg→ alg1 alg2)
    → alg⇒ ≡ -F-Alg→-trans alg⇒ -F-Alg→-refl

  -F-Alg→-assoc : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} {alg1 alg2 alg3 alg4 : F-Alg ℂ F}
    → (alg⇒1 : -F-Alg→ alg3 alg4)
    → (alg⇒2 : -F-Alg→ alg2 alg3)
    → (alg⇒3 : -F-Alg→ alg1 alg2)    
    → -F-Alg→-trans (-F-Alg→-trans alg⇒1 alg⇒2) alg⇒3 ≡ -F-Alg→-trans alg⇒1 (-F-Alg→-trans alg⇒2 alg⇒3)

F-ALG : {ℂ : Category {i} {j}} {F : Endofunctor ℂ} → Category {i ⊔ j} {i ⊔ j}
F-ALG {ℂ = ℂ} {F = F}
  = record
  { obj = F-Alg ℂ F
  ; hom = -F-Alg→
  ; id = -F-Alg→-refl
  ; _∘_ = -F-Alg→-trans
  ; left-id = -F-Alg→-left-id
  ; right-id = -F-Alg→-right-id
  ; assoc = -F-Alg→-assoc
  }

