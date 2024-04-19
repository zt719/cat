module Natural-Transformation where

open import Base
open import Category
open import Functor

private variable l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ : Level
private variable 𝓒 : Category {l₁} {l₂}
private variable 𝓓 : Category {l₃} {l₄}
private variable 𝓔 : Category {l₅} {l₆}
private variable 𝓕 : Category {l₇} {l₈}

record NT {𝓒 : Category {l₁} {l₂}} {𝓓 : Category {l₃} {l₄}}
  (F G : Functor 𝓒 𝓓) : UU (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄) where
  open Category.Category
  open Functor.Functor
  field
    α : (a : obj 𝓒) → hom 𝓓 (map F a) (map G a)
    natural : {a b : obj 𝓒} {f : hom 𝓒 a b}
      → (_∘_) 𝓓 (α b) (fmap F f) ≡ (_∘_) 𝓓 (fmap G f) (α a)
open NT

head : {A : UU l₁}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-nt : NT list-functor maybe-functor
head-as-nt = record
  { α = λ _ → head
  ; natural = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

nt-refl : {F : Functor 𝓒 𝓓}
  → NT F F
open Category.Category
open Functor.Functor
nt-refl
  {𝓒 = record { id = id ; left-id = left-id ; right-id = right-id }}
  {F = record { fmap = fmap ; map-comp = map-comp }}
  = record
  { α = λ a → fmap (id {a})
  ; natural = λ
    { {f = f} → map-comp
    ≡∘ cong fmap (≡-sym (right-id f) ≡∘ left-id f)
    ≡∘ ≡-sym map-comp
    }
  }

identity-nt :
  (F : Functor 𝓒 𝓓) → NT F F
identity-nt F = nt-refl

nt-trans : {F G H : Functor 𝓒 𝓓}
  → NT G H → NT F G → NT F H
open Category.Category
open Functor.Functor
nt-trans
  {𝓓 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = F} {G = G} {H = H}
  record { α = α ; natural = natural-α }
  record { α = β ; natural = natural-β }
  = record
  { α = λ a → (α a) ∘ (β a)
  ; natural = λ
    { {a} {b} {f} → assoc (fmap H f) (α a) (β a)
    ≡∘ cong (_∘ (β a)) natural-α
    ≡∘ ≡-sym (assoc (α b) (fmap G f) (β a))
    ≡∘ cong ((α b) ∘_) natural-β
    ≡∘ assoc (α b) (β b) (fmap F f)
    }
  }

_~_ = nt-trans

postulate
  nt-left-id : {F G : Functor 𝓒 𝓓}
    → (nt : NT F G)
    → nt-refl ~ nt ≡ nt

  nt-right-id : {F G : Functor 𝓒 𝓓}
    → (nt : NT F G)
    → nt ~ nt-refl ≡ nt

  nt-assoc : {F G H J : Functor 𝓒 𝓓}
    → (nt1 : NT H J) (nt2 : NT G H) (nt3 : NT F G)
    → (nt1 ~ nt2) ~ nt3 ≡ nt1 ~ (nt2 ~ nt3)

nt-horizontal : {F F' : Functor 𝓒 𝓓} {G G' : Functor 𝓓 𝓔}
  → NT G G' → NT F F' → NT (G ⇐ F) (G' ⇐ F')
open Category.Category
open Functor.Functor
nt-horizontal
  {𝓔 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F} {F'} {G} {G'}
  record { α = β ; natural = natural-β }
  record { α = α ; natural = natural-α }
  = record
  { α = λ a → fmap G' (α a) ∘ β (map F a)
  ; natural = λ
    { {a} {b} {f} → assoc (fmap (G' ⇐ F') f) (fmap G' (α a)) (β (map F a))
    ≡∘ cong (_∘ β (map F a)) (map-comp G' ≡∘ cong (fmap G') natural-α ≡∘ ≡-sym (map-comp G'))
    ≡∘ ≡-sym (assoc (fmap G' (α b)) (fmap (G' ⇐ F) f) (β (map F a)))
    ≡∘ cong (fmap G' (α b) ∘_) (natural-β {map F a} {map F b} {fmap F f})
    ≡∘ assoc (fmap G' (α b)) (β (map F b)) (fmap (G ⇐ F) f)
    }
  }

_~h_ = nt-horizontal

nt-func-horizontal : {G G' : Functor 𝓓 𝓔}
  → (β : NT G G')
  → (F : Functor 𝓒 𝓓)
  → NT (G ⇐ F) (G' ⇐ F)
nt-func-horizontal β F = β ~h identity-nt F

_~hl_ = nt-func-horizontal

func-nt-horizontal : {F F' : Functor 𝓒 𝓓}
  → (G : Functor 𝓓 𝓔)
  → (α : NT F F')
  → NT (G ⇐ F) (G ⇐ F')
func-nt-horizontal G α = identity-nt G ~h α

_~hr_ = func-nt-horizontal

FUN : (𝓒 : Category {l₁} {l₂}) (𝓓 : Category {l₃} {l₄}) → Category
FUN 𝓒 𝓓  = record
       { obj = Functor 𝓒 𝓓
       ; hom = NT
       ; id = nt-refl
       ; _∘_ = _~_
       ; left-id = nt-left-id
       ; right-id = nt-right-id
       ; assoc = nt-assoc
       }

