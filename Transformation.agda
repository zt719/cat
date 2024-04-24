module Transformation where

open import Base
open import Category
open import Functor

private variable l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ : Level
private variable 𝓒 : Category {l₁} {l₂}
private variable 𝓓 : Category {l₃} {l₄}
private variable 𝓔 : Category {l₅} {l₆}
private variable 𝓕 : Category {l₇} {l₈}

record Transformation {𝓒 : Category {l₁} {l₂}} {𝓓 : Category {l₃} {l₄}}
  (F G : Functor 𝓒 𝓓) : UU (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄) where
  constructor Transformation#_,_
  open Category.Category
  open Functor.Functor
  field
    α : {a : obj 𝓒} → hom 𝓓 (map F a) (map G a)
    natural : {a b : obj 𝓒} {f : hom 𝓒 a b}
      → (_∘_) 𝓓 (α {b}) (fmap F f) ≡ (_∘_) 𝓓 (fmap G f) (α {a})
open Transformation

head : {A : UU l₁}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-transformation : Transformation list-functor maybe-functor
head-as-transformation = record
  { α = head
  ; natural = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

transformation-refl : {F : Functor 𝓒 𝓓}
  → Transformation F F
open Category.Category
open Functor.Functor
transformation-refl
  {𝓒 = record { id = id ; left-id = left-id ; right-id = right-id }}
  {F = record { fmap = fmap ; map-comp = map-comp }}
  = record
  { α = fmap id
  ; natural = λ
    { {f = f} → map-comp
    ≡∘ cong fmap (right-id f ≡∘ left-id f)
    ≡∘ ≡-sym map-comp
    }
  }

idetransformationity-transformation :
  (F : Functor 𝓒 𝓓) → Transformation F F
idetransformationity-transformation F = transformation-refl

transformation-trans : {F G H : Functor 𝓒 𝓓}
  → Transformation G H → Transformation F G → Transformation F H
open Category.Category
open Functor.Functor
transformation-trans
  {𝓓 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = F} {G = G} {H = H}
  record { α = α ; natural = natural-α }
  record { α = β ; natural = natural-β }
  = record
  { α = α ∘ β
  ; natural = λ
    { {a} {b} {f} → assoc (fmap H f) (α {a}) (β {a})
    ≡∘ cong (_∘ (β {a})) natural-α
    ≡∘ ≡-sym (assoc (α {b}) (fmap G f) (β {a}))
    ≡∘ cong ((α {b}) ∘_) natural-β
    ≡∘ assoc (α {b}) (β {b}) (fmap F f)
    }
  }

_~_ = transformation-trans

postulate
  transformation-left-id : {F G : Functor 𝓒 𝓓}
    → (transformation : Transformation F G)
    → transformation-refl ~ transformation ≡ transformation
    
  transformation-right-id : {F G : Functor 𝓒 𝓓}
    → (transformation : Transformation F G)
    → transformation ≡ transformation ~ transformation-refl

  transformation-assoc : {F G H J : Functor 𝓒 𝓓}
    → (transformation1 : Transformation H J) (transformation2 : Transformation G H) (transformation3 : Transformation F G)
    → (transformation1 ~ transformation2) ~ transformation3 ≡ transformation1 ~ (transformation2 ~ transformation3)

transformation-horizotransformational : {F F' : Functor 𝓒 𝓓} {G G' : Functor 𝓓 𝓔}
  → Transformation G G' → Transformation F F' → Transformation (G ⇐ F) (G' ⇐ F')
open Category.Category
open Functor.Functor
transformation-horizotransformational
  {𝓔 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F} {F'} {G} {G'}
  record { α = β ; natural = natural-β }
  record { α = α ; natural = natural-α }
  = record
  { α = fmap G' α ∘ β 
  ; natural = λ
    { {a} {b} {f} → assoc (fmap (G' ⇐ F') f) (fmap G' (α {a})) (β {map F a})
    ≡∘ cong (_∘ β {map F a}) (map-comp G' ≡∘ cong (fmap G') natural-α ≡∘ ≡-sym (map-comp G'))
    ≡∘ ≡-sym (assoc (fmap G' (α {b})) (fmap (G' ⇐ F) f) (β {map F a}))
    ≡∘ cong (fmap G' (α {b}) ∘_) (natural-β {map F a} {map F b} {fmap F f})
    ≡∘ assoc (fmap G' (α {b})) (β {map F b}) (fmap (G ⇐ F) f)
    }
  }

_~h_ = transformation-horizotransformational

transformation-func-horizotransformational : {G G' : Functor 𝓓 𝓔}
  → (β : Transformation G G')
  → (F : Functor 𝓒 𝓓)
  → Transformation (G ⇐ F) (G' ⇐ F)
transformation-func-horizotransformational β F = β ~h idetransformationity-transformation F

_~hl_ = transformation-func-horizotransformational

func-transformation-horizotransformational : {F F' : Functor 𝓒 𝓓}
  → (G : Functor 𝓓 𝓔)
  → (α : Transformation F F')
  → Transformation (G ⇐ F) (G ⇐ F')
func-transformation-horizotransformational G α = idetransformationity-transformation G ~h α

_~hr_ = func-transformation-horizotransformational

FUN : (𝓒 : Category {l₁} {l₂}) (𝓓 : Category {l₃} {l₄}) → Category
FUN 𝓒 𝓓  = record
       { obj = Functor 𝓒 𝓓
       ; hom = Transformation
       ; id = transformation-refl
       ; _∘_ = _~_
       ; left-id = transformation-left-id
       ; right-id = transformation-right-id
       ; assoc = transformation-assoc
       }

