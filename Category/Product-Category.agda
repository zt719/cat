module Category.Product-Category where

open import Agda.Primitive
open import Data.Equality
open import Data.Sigma
open import Category.Category

private variable i j k l : Level

PRODUCT :
  (𝔸 : Category {i} {j}) (B : Category {k} {l})
  → Category {i ⊔ k} {j ⊔ l}
PRODUCT
  record { obj = A ; hom = hom-𝔸 ; id = id-𝔸 ; _∘_ = _∘𝔸_ ; left-id = left-id-𝔸 ; right-id = right-id-𝔸 ; assoc = assoc-𝔸 }
  record { obj = B ; hom = hom-𝔹 ; id = id-𝔹 ; _∘_ = _∘𝔹_ ; left-id = left-id-𝔹 ; right-id = right-id-𝔹 ; assoc = assoc-𝔹 }
  = record
  { obj = A × B
  ; hom = λ{ (a1 , b1) (a2 , b2) → hom-𝔸 a1 a2 × hom-𝔹 b1 b2 }
  ; id = id-𝔸 , id-𝔹
  ; _∘_ = λ{ (fa , fb) (ga , gb) → (fa ∘𝔸 ga) , (fb ∘𝔹 gb) }
  ; left-id = λ{ (fa , fb) → cong₂ _,_ (left-id-𝔸 fa) (left-id-𝔹 fb) }
  ; right-id = λ{ (fa , fb) → cong₂ _,_ (right-id-𝔸 fa) (right-id-𝔹 fb) }
  ; assoc = λ{ (fa , fb) (ga , gb) (ha , hb) → cong₂ _,_ (assoc-𝔸 fa ga ha) (assoc-𝔹 fb gb hb) }
  }
     
