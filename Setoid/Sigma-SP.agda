module Setoid.Sigma-SP where

open import Data.Product
open import Setoid
open import Setoid.Fibra-SP

Sigma-SP : ∀ (S : Setoid) → (FibSP S) → Setoid
Sigma-SP S P = record {
  El = Σ[ s ∈ El S ] (FibSP.Fib P s);
  E = λ x y → E S (proj₁ x) (proj₁ y);
  r = λ x → r S (proj₁ x);
  E* = λ x* y* → E* S x* y*}

proj₁* : ∀ {S P x x'} → E (Sigma-SP S P) x x' → E S (proj₁ x) (proj₁ x')
proj₁* x* = x*

ax4S : ∀ (S : Setoid) → (x : El S) → ContrS (Sigma-SP S (FibSP-p2 {S} {S} (diagS S) x) )
ax4S S x = record { c = x , r S x; p = λ x → sym S (proj₂ x) }

ax4S' : ∀ (S : Setoid) → (x : El S) → ContrS (Sigma-SP S (FibSP-p1 {S} {S} (diagS S) x) )
ax4S' S x = record { c = x , r S x; p = proj₂ }