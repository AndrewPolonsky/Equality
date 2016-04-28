module Setoid.Fibra-SP where

open import Prop
open import Setoid.Product
open import Setoid.Function

record FibSP (B : Setoid) : Set₁ where
  field
    Fib : ∀ (x : El B) → Set
    Sub : ∀ (x y : El B) → E B x y → (Fib x ⇔ Fib y)
open FibSP public

diagS : ∀ (S : Setoid) → FibSP (PRODS S S) 
diagS = λ S → record {
  Fib = λ x → E S (proj₁ x) (proj₂ x);
  Sub = λ x y x₁ → E* S (proj₁ x₁) (proj₂ x₁) }

FibSP-p1 : ∀ {S T : Setoid} → FibSP (PRODS S T) → El T → FibSP S
FibSP-p1 {S} {T} F t = 
  record { Fib = λ s → Fib F (s , t); Sub = λ x y p → Sub F (x , t) (y , t) (p , (r T t)) }

FibSP-p2 : ∀ {S T : Setoid} → FibSP (PRODS S T) → El S → FibSP T
FibSP-p2 {S} {T} F s = 
  record { Fib = λ t → Fib F (s , t); Sub = λ x y p → Sub F (s , x) (s , y) (r S s , p) }

--The pullback of a fibration along a function is a fibration
pullback : ∀ {S} {S'} → FunS S S' → FibSP S' → FibSP S
pullback f F = record { 
  Fib = λ x → Fib F (f · x) ; 
  Sub = λ x x' x* → Sub F (f · x) (f · x') (f • x*) }

