module Category.Natural-Transformation where

open import Agda.Primitive
open import Data.Equality
open import Data.Maybe
open import Data.List
open import Data.Function 
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
  open Category.Category.Category using (obj; hom)
  open Category.Category.Category 𝔻 using (_∘_)
  open Category.Functor.Functor F renaming (map₀ to F₀; map₁ to F₁)
  open Category.Functor.Functor G renaming (map₀ to G₀; map₁ to G₁)  
  field
    component : {a : obj ℂ} → hom 𝔻 (F₀ a) (G₀ a)
    commute : {a b : obj ℂ} {f : hom ℂ a b}
      → (component {b}) ∘ (F₁ f) ≡ (G₁ f) ∘ (component {a})
open Natural-Transformation

_~_ = Natural-Transformation

head : {A : Set i}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-nt : list-functor ~ maybe-functor
head-as-nt = record
  { component = head
  ; commute = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

nt-refl : {F : ℂ ⇒ 𝔻} → F ~ F
nt-refl
  {ℂ = record { id = id ; left-id = left-id ; right-id = right-id }}
  {F = record { map₁ = map₁ ; map-∘ = map-∘ }}
  = record
  { component = map₁ id
  ; commute = λ
    { {f = f} → map-∘
    ∙ cong map₁ (right-id f ∙ left-id f)
    ∙ ≡-sym map-∘
    }
  }

id-nt : (F : ℂ ⇒ 𝔻) → F ~ F
id-nt F = nt-refl

nt-trans : {F G H : ℂ ⇒ 𝔻}
  → G ~ H → F ~ G → F ~ H
nt-trans
  {𝔻 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = record { map₁ = F₁ }}
  {G = record { map₁ = G₁ }}
  {H = record { map₁ = H₁ }}  
  record { component = α ; commute = commute-α }
  record { component = β ; commute = commute-β }
  = record
  { component = α ∘ β
  ; commute = λ
    { {a} {b} {f} → assoc (H₁ f) (α {a}) (β {a})
    ∙ cong (_∘ (β {a})) commute-α
    ∙ ≡-sym (assoc (α {b}) (G₁ f) (β {a}))
    ∙ cong ((α {b}) ∘_) commute-β
    ∙ assoc (α {b}) (β {b}) (F₁ f)
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



{-

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
-}

{-
nt-horizontal : {F G : ℂ ⇒ 𝔻} {H J : 𝔻 ⇒ 𝔼}
  → H ~ J
  → F ~ G
  → (H ⇐∘= F) ~ (J ⇐∘= G)
nt-horizontal
  {𝔼 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = record { map₀ = F₀ ; map₁ = F₁ }}
  {G = record { map₀ = G₀ ; map₁ = G₁ }}
  {H = record { map₀ = H₀ ; map₁ = H₁ }}
  {J = record { map₀ = J₀ ; map₁ = J₁ }}  
  record { at = β ; commute = commute-β }
  record { at = α ; commute = commute-α }
  = record
  { at = H₁ α ∘ β 
  ; commute = λ
    { {a} {b} {f} → assoc (map₁ (J ⇐∘= G) f) (map₁ J (at {a})) (β {map₀ F a})
    ∙ cong (_∘ β {map₀ F a}) (map-∘ J ∙ cong (map₁ J) commute-at ∙ ≡-sym (map-∘ J))
    ∙ ≡-sym (assoc (map₁ J (at {b})) (map₁ (J ⇐∘= F) f) (β {map₀ F a}))
    ∙ cong (map₁ J (at {b}) ∘_) (commute-β {map₀ F a} {map₀ F b} {map₁ F f})
    ∙ assoc (map₁ J (at {b})) (β {map₀ F b}) (map₁ (H ⇐∘= F) f)
    }

  }
-}

nt-horizontal : {F G : ℂ ⇒ 𝔻} {H J : 𝔻 ⇒ 𝔼}
  → H ~ J → F ~ G → (H ⇒∘ F) ~ (J ⇒∘ G)
nt-horizontal
  {𝔼 = record { _∘_ = _∘_ ; assoc = assoc }}
  {F = record { map₀ = F₀ ; map₁ = F₁ }}
  {G = record { map₁ = G₁ }}
  {H = record { map₁ = H₁ }}
  {J = record { map₁ = J₁ ; map-∘ = map-∘ }}  
  record { component = β ; commute = commute-β }
  record { component = α ; commute = commute-α }
  = record
  { component = J₁ α ∘ β 
  ; commute = λ
    { {a} {b} {f} → assoc ((J₁ →∘ G₁) f) (J₁ (α {a})) (β {F₀ a})
    ∙ cong (_∘ β {F₀ a}) (map-∘ ∙ cong J₁ commute-α ∙ ≡-sym map-∘)
    ∙ ≡-sym (assoc (J₁ (α {b})) ((J₁ →∘ F₁) f) (β {F₀ a}))
    ∙ cong (J₁ (α {b}) ∘_) (commute-β {F₀ a} {F₀ b} {F₁ f})
    ∙ assoc (J₁ (α {b})) (β {F₀ b}) ((H₁ →∘ F₁) f)
    }
  }
