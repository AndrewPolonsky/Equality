{-# OPTIONS --no-positivity-check #-}

module Universes.EqSim where
open import Data.Product

-- Universe with Eq defined inductively, ∼ defined recursively, Rel defined as T ∘ ∼

data U : Set
T : U → Set
data Eq : U → U → Set
Rel : ∀ {A} {B} → Eq A B → T A → T B → Set
infix 60 _∼〈_〉_
_∼〈_〉_ : ∀ {A} {B} → T A → Eq A B → T B → U

data U where
    * : U
    π : ∀ A → (T A → U) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U

T * = U
T (π A B) = ∀ a → T (B a)
T (σ A B) = Σ[ a ∈ T A ] T (B a)
T (A ≃ B) = Eq A B

data Eq where
    r* : Eq * *
    π* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ a a' (a* : Rel A* a a') → Eq (B a) (B' a')) →
           Eq (π A B) (π A' B')
    σ* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ a a' (a* : Rel A* a a') → Eq (B a) (B' a')) →
           Eq (σ A B) (σ A' B')
    _≃*_ : ∀ {A} {A'} (A* : Eq A A') {B} {B'} (B* : Eq B B') → 
           Eq (A ≃ B) (A' ≃ B')

Rel e a b = T (a ∼〈 e 〉 b)

A ∼〈 r* 〉 B = A ≃ B
f ∼〈 π* {A} {A'} A* {B} {B'} B* 〉 g = π A (λ x → π A' (λ x' → 
  π (x ∼〈 A* 〉 x') (λ x* → f x ∼〈 B* x x' x* 〉 g x')))
p ∼〈 σ* {A} {A'} A* {B} {B'} B* 〉 q = σ (proj₁ p ∼〈 A* 〉 proj₁ q) 
  (λ a* → proj₂ p ∼〈 B* (proj₁ p) (proj₁ q) a* 〉 proj₂ q)
e ∼〈 _≃*_ {A} {A'} A* {B} {B'} B* 〉 e' = 
  π A (λ a → π A' (λ a' → π (a ∼〈 A* 〉 a') (λ a* → 
  π B (λ b → π B' (λ b' → π (b ∼〈 B* 〉 b') (λ b* → 
  (a ∼〈 e 〉 b) ≃ (a' ∼〈 e' 〉 b')))))))

syntax π A (λ a → B) = π[ a ∶ A ] B
syntax σ A (λ a → B) = σ[ a ∶ A ] B
