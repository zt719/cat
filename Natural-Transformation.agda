module Natural-Transformation where

open import Base
open import Category
open import Functor

private variable i j k l m n : Level

record NT {𝓒 : Category {i} {j}} {𝓓 : Category {k} {l}}
  (F G : Functor 𝓒 𝓓) : UU (i ⊔ j ⊔ l ⊔ k) where
  open Category.Category
  open Functor.Functor
  field
    α : {A : obj 𝓒} → hom 𝓓 (map F A) (map G A)
    NTL : {A B : obj 𝓒} {f : hom 𝓒 A B}
      → (_∘_) 𝓓 (fmap F f) (α {B}) ≡ (_∘_) 𝓓 (α {A}) (fmap G f)
open NT

head : {A : UU i}
  → List A → Maybe A
head [] = nothing
head (a ∷ as) = just a

head-is-NT : NT list-functor maybe-functor
head-is-NT = record
  { α = head
  ; NTL = ext (λ{ [] → refl ; (a ∷ as) → refl })
  }

NT-trans : {𝓒 : Category {i} {j}} {𝓓 : Category {k} {l}}
  → {F G H : Functor 𝓒 𝓓}
  → NT F G → NT G H → NT F H
open Category.Category
open Functor.Functor
NT-trans
  {𝓓 = record { _∘_ = _∘_ ; cat-assoc = cat-assoc }}
  {F = F} {G = G} {H = H}
  record { α = α-FG ; NTL = NTL-FG }
  record { α = α-GH ; NTL = NTL-GH }
  = record
  { α = α-FG ∘ α-GH
  ; NTL = λ{ {f = f} →
    ≡-sym (cat-assoc (fmap F f) α-FG α-GH)
    ≡∘ cong (_∘ α-GH) NTL-FG
    ≡∘ cat-assoc α-FG (fmap G f) α-GH
    ≡∘ (cong (α-FG ∘_) NTL-GH)
    ≡∘ ≡-sym (cat-assoc α-FG α-GH (fmap H f))}
  }

-- NT-horizontal : {𝓒 : Category {i} {j}} {𝓓 : Category {k} {l}} {𝓔 : Category {m} {n}}
--  → {F G : Functor 𝓒 𝓓} {H J : Functor 𝓓 𝓔}
--  → 
