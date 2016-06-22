module Setoid.Product where

open import Data.Product public
open import prop.Product
open import Setoid public
open import Setoid.Function

PRODS : ∀ (S S' : Setoid) → Setoid
PRODS S S' = record {
  El = El S × El S';
  E = λ x y → PRODP (E S (proj₁ x) (proj₁ y)) (E S' (proj₂ x) (proj₂ y)) ;
  r = λ { (x , x') → r S x , r S' x'};
  E* = λ { (x1* , x2*) (y1* , y2*) → PRODP* (E* S x1* y1*) (E* S' x2* y2*) }}

ProdF : ∀ {A A' B B'} → FunS A A' → FunS B B' → FunS (PRODS A B) (PRODS A' B')
ProdF f g = record { 
  app = λ {(a , b) → f · a , g · b} ; 
  app1 = λ {(a , b) (a' , b') (a* , b*) → f • a* , g • b* }}
