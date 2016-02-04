{-# OPTIONS --no-positivity-check #-}

module Equality2 where

data Σ {A : Set} (B : A → Set) : Set where
  _,_ : ∀ a → B a → Σ B

π₁ : ∀ {A} {B} → Σ B → A
π₁ (a , _) = a

π₂ : ∀ {A} {B} (p : Σ {A} B) → B (π₁ p)
π₂ (_ , b) = b

mutual
  data U : Set where
    * : U
    π : ∀ A → (T A → U) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U

  T : U → Set
  T * = U
  T (π A B) = ∀ a → T (B a)
  T (σ A B) = Σ (λ a → T (B a))
  T (A ≃ B) = Eq A B

  data Eq : U → U → Set where
    r* : Eq * *
    π* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ a a' (a* : Rel A* a a') → Eq (B a) (B' a')) →
           Eq (π A B) (π A' B')
    σ* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ a a' (a* : Rel A* a a') → Eq (B a) (B' a')) →
           Eq (σ A B) (σ A' B')
    _≃*_ : ∀ {A} {A'} (A* : Eq A A') {B} {B'} (B* : Eq B B') → 
           Eq (A ≃ B) (A' ≃ B')

  Rel : ∀ {A} {B} → Eq A B → T A → T B → Set
  Rel e a b = T (a ∼〈 e 〉 b)

  _∼〈_〉_ : ∀ {A} {B} → T A → Eq A B → T B → U
  A ∼〈 r* 〉 B = A ≃ B
  f ∼〈 π* {A} {A'} A* {B} {B'} B* 〉 g = π A (λ x → π A' (λ x' → 
    π (x ∼〈 A* 〉 x') (λ x* → f x ∼〈 B* x x' x* 〉 g x')))
  p ∼〈 σ* {A} {A'} A* {B} {B'} B* 〉 q = σ (π₁ p ∼〈 A* 〉 π₁ q) 
    (λ a* → π₂ p ∼〈 B* (π₁ p) (π₁ q) a* 〉 π₂ q)
  e ∼〈 _≃*_ {A} {A'} A* {B} {B'} B* 〉 e' = 
    π A (λ a → π A' (λ a' → π (a ∼〈 A* 〉 a') (λ a* → 
    π B (λ b → π B' (λ b' → π (b ∼〈 B* 〉 b') (λ b* → 
    (a ∼〈 e 〉 b) ≃ (a' ∼〈 e' 〉 b')))))))
