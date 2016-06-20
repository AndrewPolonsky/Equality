module Setoid2 where

open import prop

record genSetoid (X : Set) : Set where
  field
    HOM : Set
    s, t : HOM → X

generateS : ∀ {X : Set} → genSetoid X → Setoid
generateS _ = ?
    
