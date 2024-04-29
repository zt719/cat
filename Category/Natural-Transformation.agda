module Category.Natural-Transformation where

open import Agda.Primitive
open import Data.Equality
open import Data.Maybe
open import Data.List
open import Category.Category
open import Category.Functor

private variable i j k l m n p q : Level
private variable ℂ : Category {i} {j}
private variable 𝔻 : Category {k} {l}
private variable 𝔼 : Category {m} {n}
private variable 𝔽 : Category {p} {q}

private variable F G H J : ℂ ⇒ 𝔻

record Natural-Transformation {ℂ : Category {i} {j}} {𝔻 : Category {k} {l}}
  (F G : ℂ ⇒ 𝔻) : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category.Category
  open Category.Functor.Functor
  field
    at : {a : obj ℂ} → hom 𝔻 (map F a) (map G a)
    natural : {a b : obj ℂ} {f : hom ℂ a b}
      → (_∘_) 𝔻 (at {b}) (fmap F f) ≡ (_∘_) 𝔻 (fmap G f) (at {a})
open Natural-Transformation

_~_ = Natural-Transformation

head : {A : Set i}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-nt : list-functor ~ maybe-functor
head-as-nt = record
  { at = head
  ; natural = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

nt-refl : {F : ℂ ⇒ 𝔻} → F ~ F
nt-refl
  {ℂ = record { id = id ; left-id = left-id ; right-id = right-id }}
  {F = record { fmap = fmap ; trans-law = trans-law }}
  = record
  { at = fmap id
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
open Category.Category.Category
open Category.Functor.Functor
nt-trans
  {𝔻 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = F} {G = G} {H = H}
  record { at = at ; natural = natural-at }
  record { at = β ; natural = natural-β }
  = record
  { at = at ∘ β
  ; natural = λ
    { {a} {b} {f} → assoc (fmap H f) (at {a}) (β {a})
    ∙ cong (_∘ (β {a})) natural-at
    ∙ ≡-sym (assoc (at {b}) (fmap G f) (β {a}))
    ∙ cong ((at {b}) ∘_) natural-β
    ∙ assoc (at {b}) (β {b}) (fmap F f)
    }
  }

_~∘~_ = nt-trans

postulate
  nt-left-id :
    (at : F ~ G)
    → nt-refl ~∘~ at ≡ at
    
  nt-right-id :
    (at : F ~ G)
    → at ≡ at ~∘~ nt-refl

  nt-assoc :
    (at : H ~ J) (β : G ~ H) (γ : F ~ G)
    → (at ~∘~ β) ~∘~ γ ≡ at ~∘~ (β ~∘~ γ)

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
  record { at = β ; natural = natural-β }
  record { at = at ; natural = natural-at }
  = record
  { at = fmap G' at ∘ β 
  ; natural = λ
    { {a} {b} {f} → assoc (fmap (G' ⇐∘= F') f) (fmap G' (at {a})) (β {map F a})
    ∙ cong (_∘ β {map F a}) (trans-law G' ∙ cong (fmap G') natural-at ∙ ≡-sym (trans-law G'))
    ∙ ≡-sym (assoc (fmap G' (at {b})) (fmap (G' ⇐∘= F) f) (β {map F a}))
    ∙ cong (fmap G' (at {b}) ∘_) (natural-β {map F a} {map F b} {fmap F f})
    ∙ assoc (fmap G' (at {b})) (β {map F b}) (fmap (G ⇐∘= F) f)
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
  → (at : F ~ F')
  → (G ⇐∘= F) ~ (G ⇐∘= F')
func-nt-horizontal G at = id-nt G ~h at

_~hr_ = nt-func-horizontal
