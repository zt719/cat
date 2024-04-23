module F-Algebra where

open import Base
open import Category
open import Functor

private variable i j : Level

-- F-Algebra --
record F-Alg (𝓒 : Category {i} {j}) (F : Endofunctor 𝓒): UU (i ⊔ j) where
  open Category.Category 𝓒
  open Functor.Functor
  field
    carrier : obj
    eval    : hom (map F carrier) carrier
open F-Alg

-- Homomorphsim between F-Algebra
record ⇐F-Alg= {𝓒 : Category {i} {j}} {F : Endofunctor 𝓒}
  (Aα : F-Alg 𝓒 F) (Bβ : F-Alg 𝓒 F) : UU (i ⊔ j) where
  open Category.Category 𝓒
  open Functor.Functor
  open F-Alg Aα renaming (carrier to A; eval to α)
  open F-Alg Bβ renaming (carrier to B; eval to β)
  field
    f : hom A B
    f-law : f ∘ α ≡ β ∘ fmap F f
open ⇐F-Alg=
