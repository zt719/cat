module Natural-Transformation where

open import Base
open import Category
open import Functor

private variable i j k l m n : Level
private variable 𝓒 : Category {i} {j}
private variable 𝓓 : Category {k} {l}
private variable 𝓔 : Category {m} {n}

record NT {𝓒 : Category {i} {j}} {𝓓 : Category {k} {l}}
  (F G : Functor 𝓒 𝓓) : UU (i ⊔ j ⊔ l ⊔ k) where
  open Category.Category
  open Functor.Functor
  field
    α : (a : obj 𝓒) → hom 𝓓 (map F a) (map G a)
    ntl : {a b : obj 𝓒} {f : hom 𝓒 a b}
      → (_∘_) 𝓓 (α b) (fmap F f) ≡ (_∘_) 𝓓 (fmap G f) (α a)
open NT

head : {A : UU i}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-as-nt : NT list-functor maybe-functor
head-as-nt = record
  { α = λ _ → head
  ; ntl = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

nt-refl : {F : Functor 𝓒 𝓓}
  → NT F F
open Category.Category
open Functor.Functor
nt-refl
  {𝓒 = record { id = id ; cat-left-id = left-id ; cat-right-id = right-id }}
  {F = record { fmap = fmap ; func-comp = func-comp }}
  = record
  { α = λ a → fmap (id {a})
  ; ntl = λ
    { {f = f} → func-comp
    ∘≡ cong fmap (≡-sym (right-id f) ∘≡ left-id f)
    ∘≡ ≡-sym func-comp
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
  {𝓓 = record { _∘_ = _∘_ ; cat-assoc = assoc }}
  {F = F} {G = G} {H = H}
  record { α = α ; ntl = ntl-α }
  record { α = β ; ntl = ntl-β }
  = record
  { α = λ a → (α a) ∘ (β a)
  ; ntl = λ
    { {a} {b} {f} → assoc (fmap H f) (α a) (β a)
    ∘≡ cong (_∘ (β a)) ntl-α
    ∘≡ ≡-sym (assoc (α b) (fmap G f) (β a))
    ∘≡ cong ((α b) ∘_) ntl-β
    ∘≡ assoc (α b) (β b) (fmap F f)
    }
  }

_<~∘_ = nt-trans

nt-horizontal : {F F' : Functor 𝓒 𝓓} {G G' : Functor 𝓓 𝓔}
  → NT G G' → NT F F' → NT (G ⇐∘ F) (G' ⇐∘ F')
open Category.Category
open Functor.Functor
nt-horizontal
  {𝓔 = record { _∘_ = _∘_ ; cat-assoc = assoc }}
  {F} {F'} {G} {G'}
  record { α = β ; ntl = ntl-β }
  record { α = α ; ntl = ntl-α }
  = record
  { α = λ a → fmap G' (α a) ∘ β (map F a)
  ; ntl = λ
    { {a} {b} {f} → assoc (fmap (G' ⇐∘ F') f) (fmap G' (α a)) (β (map F a))
    ∘≡ cong (_∘ β (map F a)) (func-comp G' ∘≡ cong (fmap G') ntl-α ∘≡ ≡-sym (func-comp G'))
    ∘≡ ≡-sym (assoc (fmap G' (α b)) (fmap (G' ⇐∘ F) f) (β (map F a)))
    ∘≡ cong (fmap G' (α b) ∘_) (ntl-β {map F a} {map F b} {fmap F f})
    ∘≡ assoc (fmap G' (α b)) (β (map F b)) (fmap (G ⇐∘ F) f)
    }
  }

_<~∘h_ = nt-horizontal

nt-func-horizontal : {G G' : Functor 𝓓 𝓔}
  → (β : NT G G')
  → (F : Functor 𝓒 𝓓)
  → NT (G ⇐∘ F) (G' ⇐∘ F)
nt-func-horizontal β F = β <~∘h identity-nt F

_<~∘F_ = nt-func-horizontal

func-nt-horizontal : {F F' : Functor 𝓒 𝓓}
  → (G : Functor 𝓓 𝓔)
  → (α : NT F F')
  → NT (G ⇐∘ F) (G ⇐∘ F')
func-nt-horizontal G α = identity-nt G <~∘h α

_F∘<~_ = func-nt-horizontal
