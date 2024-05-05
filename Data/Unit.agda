module Data.Unit where

open import Agda.Builtin.Unit public

data _-⊤→_ (a b : ⊤) : Set where
  -tt→ : tt -⊤→ tt
