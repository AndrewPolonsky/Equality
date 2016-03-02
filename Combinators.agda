module Combinators where

open import Data.Product public

infix 75 _∘_
_∘_ : ∀ {i} {j} {k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

K : ∀ {i} {j} {A : Set i} {B : Set j} → A → B → A
K a _ = a

infixl 50 _S_
_S_ : ∀ {i} {j} {k} {A : Set i} {B : A → Set j} {C : ∀ a → B a → Set k} →
  (∀ a b → C a b) → ∀ (f : ∀ a → B a) → ∀ a → C a (f a)
(g S f) a = g a (f a)

∨ : ∀ {i} {j} {A : Set i} {B : A → Set j} {P : Σ[ a ∈ A ] B a → Set} → (∀ a b → P (a , b)) → ∀ p → P p
∨ p (a , b) = p a b

∧ : ∀ {i} {j} {k} {A : Set i} {B : A → Set j} {P : Σ[ a ∈ A ] B a → Set k} → (∀ p → P p) → ∀ a b → P (a , b)
∧ p a b = p (a , b)

