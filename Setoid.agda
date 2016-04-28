{-# OPTIONS --type-in-type #-}

module Setoid where

open import Data.Product
open import Prop

record Setoid : Set where
  field
    El : Set
    E : El → El → Set
    r : ∀ (x : El) → E x x
    E* : ∀ {x x' : El} → E x x' → ∀ {y y' : El} → E y y' → (E x y ⇔ E x' y')

  sym : ∀ {x y : El} → E x y → E y x
  sym {x} {y} p = proj₁ (E* p (r x)) (r x)

  trans : ∀ {x y z : El} → E x y → E y z → E x z
  trans {x} {y} {z} p q = proj₂ (E* p (r z)) q
--TODO Make proj₁, proj₂ into lemmas in Prop?

open Setoid public

Prop:Set : Setoid
Prop:Set = record {
  El = Set;
  E = _⇔_;
  r = λ S → refl_p;
  E* = ⇔* }
    
record ContrS (S : Setoid) : Set where
  field
    c : El S
    p : ∀ (x : El S) → E S x c