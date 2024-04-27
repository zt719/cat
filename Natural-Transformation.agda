module Natural-Transformation where

open import Base
open import Category
open import Functor

private variable ℂ : Category {i} {j}
private variable 𝔻 : Category {k} {l}
private variable 𝔼 : Category {m} {n}
private variable 𝔽 : Category {p} {q}

private variable F G H J : ℂ ⇒ 𝔻

record Natural-Transformation {ℂ : Category {i} {j}} {𝔻 : Category {k} {l}}
  (F G : ℂ ⇒ 𝔻) : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category
  open Functor.Functor
  field
    α : {a : obj ℂ} → hom 𝔻 (map F a) (map G a)
    natural : {a b : obj ℂ} {f : hom ℂ a b}
      → (_∘_) 𝔻 (α {b}) (fmap F f) ≡ (_∘_) 𝔻 (fmap G f) (α {a})
open Natural-Transformation

_~_ = Natural-Transformation

head : {A : Set i}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-nt : list-functor ~ maybe-functor
head-as-nt = record
  { α = head
  ; natural = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

nt-refl : {F : ℂ ⇒ 𝔻} → F ~ F
nt-refl
  {ℂ = record { id = id ; left-id = left-id ; right-id = right-id }}
  {F = record { fmap = fmap ; trans-law = trans-law }}
  = record
  { α = fmap id
  ; natural = λ
    { {f = f} → trans-law
    ∙ cong fmap (right-id f ∙ left-id f)
    ∙ ≡-sym trans-law
    }
  }

id-nt : (F : ℂ ⇒ 𝔻) → F ~ F
id-nt F = nt-refl

nt-trans : {F G H : ℂ ⇒ 𝔻}
  → G ~ H → F ~ G → F ~ H
open Category.Category
open Functor.Functor
nt-trans
  {𝔻 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = F} {G = G} {H = H}
  record { α = α ; natural = natural-α }
  record { α = β ; natural = natural-β }
  = record
  { α = α ∘ β
  ; natural = λ
    { {a} {b} {f} → assoc (fmap H f) (α {a}) (β {a})
    ∙ cong (_∘ (β {a})) natural-α
    ∙ ≡-sym (assoc (α {b}) (fmap G f) (β {a}))
    ∙ cong ((α {b}) ∘_) natural-β
    ∙ assoc (α {b}) (β {b}) (fmap F f)
    }
  }

_~∘~_ = nt-trans

postulate
  nt-left-id :
    (α : F ~ G)
    → nt-refl ~∘~ α ≡ α
    
  nt-right-id :
    (α : F ~ G)
    → α ≡ α ~∘~ nt-refl

  nt-assoc :
    (α : H ~ J) (β : G ~ H) (γ : F ~ G)
    → (α ~∘~ β) ~∘~ γ ≡ α ~∘~ (β ~∘~ γ)

FUNC : {ℂ : Category {i} {j}} {𝔻 : Category {k} {l}} → Category
FUNC {ℂ = ℂ} {𝔻 = 𝔻}
  = record
  { obj = ℂ ⇒ 𝔻
  ; hom = _~_
  ; id = nt-refl
  ; _∘_ = nt-trans
  ; left-id = nt-left-id
  ; right-id = nt-right-id
  ; assoc = nt-assoc
  }

nt-horizontal : {F F' : ℂ ⇒ 𝔻} {G G' : 𝔻 ⇒ 𝔼}
  → G ~ G' → F ~ F' → (G ⇐∘= F) ~ (G' ⇐∘= F')
nt-horizontal
  {𝔼 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F} {F'} {G} {G'}
  record { α = β ; natural = natural-β }
  record { α = α ; natural = natural-α }
  = record
  { α = fmap G' α ∘ β 
  ; natural = λ
    { {a} {b} {f} → assoc (fmap (G' ⇐∘= F') f) (fmap G' (α {a})) (β {map F a})
    ∙ cong (_∘ β {map F a}) (trans-law G' ∙ cong (fmap G') natural-α ∙ ≡-sym (trans-law G'))
    ∙ ≡-sym (assoc (fmap G' (α {b})) (fmap (G' ⇐∘= F) f) (β {map F a}))
    ∙ cong (fmap G' (α {b}) ∘_) (natural-β {map F a} {map F b} {fmap F f})
    ∙ assoc (fmap G' (α {b})) (β {map F b}) (fmap (G ⇐∘= F) f)
    }
  }

_~h_ = nt-horizontal

nt-func-horizontal : {G G' : 𝔻 ⇒ 𝔼}
  → (β : G ~ G')
  → (F : ℂ ⇒ 𝔻)
  → (G ⇐∘= F) ~ (G' ⇐∘= F)
nt-func-horizontal β F = β ~h id-nt F

_~hl_ = nt-func-horizontal

func-nt-horizontal : {F F' : ℂ ⇒ 𝔻}
  → (G : 𝔻 ⇒ 𝔼)
  → (α : F ~ F')
  → (G ⇐∘= F) ~ (G ⇐∘= F')
func-nt-horizontal G α = id-nt G ~h α

_~hr_ = nt-func-horizontal
