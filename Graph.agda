module Graph where

open import Base

data Point : UU where
  a : Point
  b : Point
  c : Point

data Arrow : Point → Point → UU where
  aa : Arrow a a
  ab : Arrow a b
  ac : Arrow a c
  bb : Arrow b b
  bc : Arrow b c
  cc : Arrow c c
  
arrow-refl : {x : Point}
  → Arrow x x
arrow-refl {a} = aa
arrow-refl {b} = bb
arrow-refl {c} = cc

arrow-trans : {x y z : Point}
  → Arrow y z → Arrow x y → Arrow x z
arrow-trans aa aa = aa
arrow-trans ab aa = ab
arrow-trans ac aa = ac
arrow-trans bb ab = ab
arrow-trans bc ab = ac
arrow-trans cc ac = ac
arrow-trans bb bb = bb
arrow-trans bc bb = bc
arrow-trans cc bc = bc
arrow-trans cc cc = cc

arrow-left-id : {x y : Point}
  → (arrow : Arrow x y)
  → arrow-trans arrow-refl arrow ≡ arrow
arrow-left-id aa = refl
arrow-left-id ab = refl
arrow-left-id ac = refl
arrow-left-id bb = refl
arrow-left-id bc = refl
arrow-left-id cc = refl

arrow-right-id : {x y : Point}
  → (arrow : Arrow x y)
  → arrow ≡ arrow-trans arrow arrow-refl
arrow-right-id aa = refl
arrow-right-id ab = refl
arrow-right-id ac = refl
arrow-right-id bb = refl
arrow-right-id bc = refl
arrow-right-id cc = refl

arrow-assoc : {x y z s : Point}
  → (f : Arrow z s) (g : Arrow y z) (h : Arrow x y)
  → arrow-trans (arrow-trans f g) h ≡ arrow-trans f (arrow-trans g h)
arrow-assoc aa aa aa = refl
arrow-assoc ab aa aa = refl
arrow-assoc ac aa aa = refl
arrow-assoc bb ab aa = refl
arrow-assoc bc ab aa = refl
arrow-assoc cc ac aa = refl
arrow-assoc bb bb ab = refl
arrow-assoc bc bb ab = refl
arrow-assoc cc bc ab = refl
arrow-assoc cc cc ac = refl
arrow-assoc bb bb bb = refl
arrow-assoc bc bb bb = refl
arrow-assoc cc bc bb = refl
arrow-assoc cc cc bc = refl
arrow-assoc cc cc cc = refl
