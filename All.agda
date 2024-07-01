module All where

open import Base
open import Category
open import Monoid

Type : (A : Set i)→ Category
Type A = record
        { obj = A
        ; hom = _≡_
        ; id = ≡-refl
        ; _∘_ = ≡-trans
        ; left-id = ≡-left-id
        ; right-id = ≡-right-id
        ; assoc = ≡-assoc
        }
