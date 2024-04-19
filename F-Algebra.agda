module F-Algebra where

open import Base
open import Category
open import Functor

private variable i j : Level

-- F-Algebra --
record F-Alg (𝓒 : Category {i} {j}) (F : Endofunctor 𝓒): UU (i ⊔ j) where
  open Category.Category
  open Functor.Functor
  field
    carrier : obj 𝓒
    eval    : hom 𝓒 (map F carrier) carrier
open F-Alg

-- Homomorphsim between F-Algebra
record ⇐F-Alg= {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒}
  (Aα : F-Alg 𝓒 F) (Bβ : F-Alg 𝓒 F) : UU (i ⊔ j) where
  open Category.Category
  open Functor.Functor
  field
    f : hom 𝓒 (carrier Aα) (carrier Bβ)
    f-law : (_∘_) 𝓒 f (eval Aα) ≡ (_∘_) 𝓒 (eval Bβ) (fmap F f) 
open ⇐F-Alg=
