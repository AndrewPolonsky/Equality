module Setoid.Function where

open import Data.Product
open import Prop
open import Setoid

record FunS (S S' : Setoid) : Set where
  field
    app : El S → El S'
    app1 : ∀ (x y : El S) → E S x y → E S' (app x) (app y)
infixl 50 _·_
_·_ : ∀ { S T : Setoid } → FunS S T → El S → El T
f · a = FunS.app f a
infixl 50 _•_
_•_ : ∀ { S T : Setoid } → (f : FunS S T) → {s s' : El S} → (E S s s') → (E T (f · s) (f · s'))
f • p = FunS.app1 f _ _ p

FUNS : Setoid → Setoid → Setoid
FUNS S S' = record {
  El = FunS S S';
  E = λ f g → ∀ x x' → E S x x' → E S' (f · x) (g · x');
  r = FunS.app1 ;
  E* = λ {f} {f'} f* {g} {g'} g* → 
    ∀* (λ x → ∀* (λ x' → imp* refl_p (E* S' (f* x x (r S x)) (g* x' x' (r S x'))))) }
