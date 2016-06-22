module prop.Product where

open import Data.Product public
open import prop public

PRODP : Set → Set → Set
PRODP p q = p × q

PRODP* : ∀ {p p'} (p* : p ⇔ p') {q q'} (q* : q ⇔ q') → PRODP p q ⇔ PRODP p' q'
PRODP* (pp' , p'p) (qq' , q'q) = (λ {(x , y) → pp' x , qq' y}) , (λ {(x , y) → p'p x , q'q y})
