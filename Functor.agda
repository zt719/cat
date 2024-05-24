module Functor where

open import Base
open import Category
open import Monoid

private variable ℂ : Category {i} {j}
private variable 𝔻 : Category {k} {l}
private variable 𝔼 : Category {m} {n}
private variable 𝔽 : Category {p} {q}

record Functor (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category
  private _∘ℂ_ = Category._∘_ ℂ
  private _∘𝔻_ = Category._∘_ 𝔻
  field
    map₀ : obj ℂ → obj 𝔻
    map₁ : {a b : obj ℂ} → hom ℂ a b → hom 𝔻 (map₀ a) (map₀ b)
    
    map-id : {a : obj ℂ} → map₁ (id ℂ {a}) ≡ id 𝔻 {map₀ a}
    map-∘  : {a b c : obj ℂ} {f : hom ℂ b c} {g : hom ℂ a b}
      → map₁ (f ∘ℂ g) ≡ map₁ f ∘𝔻 map₁ g

_⇒_ = Functor

record Contravariant (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category
  private _∘ℂ_ = Category._∘_ ℂ
  private _∘𝔻_ = Category._∘_ 𝔻
  field
    map₀ : obj ℂ → obj 𝔻
    map₁ : {a b : obj ℂ} → hom ℂ a b → hom 𝔻 (map₀ b) (map₀ a)
    
    map-id : {a : obj ℂ} → map₁ (id ℂ {a}) ≡ id 𝔻 {map₀ a}
    map-∘  : {a b c : obj ℂ} {f : hom ℂ b c} {g : hom ℂ a b}
      → map₁ (f ∘ℂ g) ≡ map₁ g ∘𝔻 map₁ f

record Invariant (ℂ : Category {i} {j} ) (𝔻 : Category {k} {l})
  : Set (i ⊔ j ⊔ k ⊔ l) where
  open Category.Category
  private _∘ℂ_ = Category._∘_ ℂ
  private _∘𝔻_ = Category._∘_ 𝔻
  field
    map₀ : obj ℂ → obj 𝔻
    map₁ : {a b : obj ℂ} → hom ℂ a b → hom ℂ b a → hom 𝔻 (map₀ a) (map₀ b)
    
    map-id : {a : obj ℂ} → map₁ (id ℂ {a}) (id ℂ {a}) ≡ id 𝔻 {map₀ a}
    map-∘  : {a b c : obj ℂ}
      → {f1 : hom ℂ b c} {f2 : hom ℂ c b}
      → {g1 : hom ℂ a b} {g2 : hom ℂ b a}
      → map₁ (f1 ∘ℂ g1) (g2 ∘ℂ f2) ≡ map₁ f1 f2 ∘𝔻 map₁ g1 g2

record Bifunctor (ℂ : Category {i} {j}) (𝔻 : Category {k} {l})
  (𝔼 : Category {m} {n}) : Set (i ⊔ j ⊔ k ⊔ l ⊔ m ⊔ n) where
  open Category.Category using (obj; hom; id)
  private _∘ℂ_ = Category._∘_ ℂ
  private _∘𝔻_ = Category._∘_ 𝔻
  private _∘𝔼_ = Category._∘_ 𝔼  
  field
    bimap₀ : obj ℂ → obj 𝔻 → obj 𝔼
    bimap₁ : {a b : obj ℂ} {c d : obj 𝔻}
      → (f : hom ℂ a b) (g : hom 𝔻 c d)
      → hom 𝔼 (bimap₀ a c) (bimap₀ b d)
    bimap-id : {a : obj ℂ} {b : obj 𝔻}
      → bimap₁ (id ℂ {a}) (id 𝔻 {b}) ≡ id 𝔼 {bimap₀ a b}
    bimap-∘  : {a1 b1 c1 : obj ℂ} {a2 b2 c2 : obj 𝔻}
      → {f1 : hom ℂ b1 c1} {g1 : hom ℂ a1 b1}
      → {f2 : hom 𝔻 b2 c2} {g2 : hom 𝔻 a2 b2}
      → bimap₁ (f1 ∘ℂ g1) (f2 ∘𝔻 g2) ≡ bimap₁ f1 f2 ∘𝔼 bimap₁ g1 g2

record Profunctor (ℂ : Category {i} {j}) (𝔻 : Category {k} {l})
  (𝔼 : Category {m} {n}) : Set (i ⊔ j ⊔ k ⊔ l ⊔ m ⊔ n) where
  open Category.Category
  private _∘ℂ_ = Category._∘_ ℂ
  private _∘𝔻_ = Category._∘_ 𝔻
  private _∘𝔼_ = Category._∘_ 𝔼
  field
    dimap₀ : obj ℂ → obj 𝔻 → obj 𝔼
    dimap₁ : {a b : obj ℂ} {c d : obj 𝔻}
      → (f : hom ℂ a b) (g : hom 𝔻 c d)
      → hom 𝔼 (dimap₀ b c) (dimap₀ a d)
    dimap-id : {a : obj ℂ} {b : obj 𝔻}
      → dimap₁ (id ℂ {a}) (id 𝔻 {b}) ≡ id 𝔼 {dimap₀ a b}
    dimap-∘  : {a1 b1 c1 : obj ℂ} {a2 b2 c2 : obj 𝔻}
      → {f1 : hom ℂ b1 c1} {g1 : hom ℂ a1 b1}
      → {f2 : hom 𝔻 b2 c2} {g2 : hom 𝔻 a2 b2}
      → dimap₁ (f1 ∘ℂ g1) (f2 ∘𝔻 g2) ≡ dimap₁ g1 f2 ∘𝔼 dimap₁ f1 g2

Endofunctor : Category {i} {j} → Set (i ⊔ j)
Endofunctor ℂ = ℂ ⇒ ℂ

func-refl : ℂ ⇒ ℂ
func-refl
  = record
  { map₀ = →-refl
  ; map₁ = →-refl
  ; map-id = ≡-refl
  ; map-∘ = ≡-refl
  }

func-trans : 𝔻 ⇒ 𝔼 → ℂ ⇒ 𝔻 → ℂ ⇒ 𝔼
func-trans
  record { map₀ = F₀ ; map₁ = F₁ ; map-id = map-id-F ; map-∘ = map-∘-F }
  record { map₀ = G₀ ; map₁ = G₁ ; map-id = map-id-G ; map-∘ = map-∘-G }
  = record
  { map₀ = F₀ →∘ G₀
  ; map₁ = F₁ →∘ G₁
  ; map-id = map-id-F ∙ cong F₁ map-id-G
  ; map-∘  = map-∘-F ∙ cong F₁ map-∘-G
  }
    
_⇒∘_ = func-trans

postulate
  func-left-id :
    (F : ℂ ⇒ 𝔻)
    → func-refl ⇒∘ F ≡ F

  func-right-id :
    (F : ℂ ⇒ 𝔻)
    → F ≡ F ⇒∘ func-refl

  func-assoc :
    (F : 𝔼 ⇒ 𝔽) (G : 𝔻 ⇒ 𝔼) (H : ℂ ⇒ 𝔻)
    → (F ⇒∘ G) ⇒∘ H ≡ F ⇒∘ (G ⇒∘ H)

CAT : {i j : Level} → Category
CAT {i} {j}
  = record
  { obj = Category {i} {j}
  ; hom = Functor
  ; id = func-refl
  ; _∘_ = func-trans
  ; left-id = func-left-id
  ; right-id = func-right-id
  ; assoc = func-assoc
  }

maybe-functor : Endofunctor SET
maybe-functor
  = record
  { map₀ = Maybe
  ; map₁ = maybe-map₁
  ; map-id = ext maybe-map₁-id'
  ; map-∘ = ext maybe-map₁-∘'
  }

list-functor : Endofunctor SET
list-functor
  = record
  { map₀  = List
  ; map₁ = list-map₁
  ; map-id = ext list-map-id'
  ; map-∘ = ext list-map-∘'
  }

forgetful-functor : MON ⇒ SET
forgetful-functor
  = record
  { map₀ = Monoid.obj
  ; map₁ = _-Monoid→_.map
  ; map-id = ≡-refl
  ; map-∘  = ≡-refl
  }

{-
free-functor : SET ⇒ MON
free-functor
  = record
  { map₀ = free-monoid
  ; map₁ = λ f → record { map = list-map₁ f ; map-⊕ = λ {a} {b} → list-map₁-++ f a b }
  ; map-id = λ{ {a} → {!!} }
  ; map-∘ = {!!}
  }
-}

id-functor :
  (ℂ : Category {i} {j})
  → Endofunctor ℂ
id-functor ℂ = func-refl
