{-# OPTIONS --no-positivity-check #-}

module Universes.EqRel where
open import Data.Product

-- A universe with Eq defined inductively, Rel defined recursively
-- and ∼ introduced as a reflection of Rel

mutual
  data U : Set where
    * : U
    π : ∀ A → (T A → U) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U
    _∼〈_〉_ : ∀ {A} {B} → T A → Eq A B → T B → U

  T : U → Set
  T * = U
  T (π A B) = ∀ a → T (B a)
  T (σ A B) = Σ[ a ∈ T A ] T (B a)
  T (A ≃ B) = Eq A B
  T (a ∼〈 e 〉 b) = Rel e a b

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
    ∼* : ∀ {A} {A'} (A* : Eq A A') {B} {B'} (B* : Eq B B')
           {e} {e'} (e* : ∀ a a' (a* : Rel A* a a') b b' (b* : Rel B* b b') → 
                            Eq (_∼〈_〉_ {A} {B} a e b) (_∼〈_〉_ {A'} {B'} a' e' b'))
           {a} {a'} (a* : Rel A* a a') {b} {b'} (b* : Rel B* b b') →
           Eq (a ∼〈 e 〉 b) (a' ∼〈 e' 〉 b')

  Rel : ∀ {A} {B} → Eq A B → T A → T B → Set
  Rel r* A B = Eq A B
  Rel (π* A* B*) f f' = ∀ a a' (a* : Rel A* a a') → 
    Rel (B* a a' a*) (f a) (f' a')
  Rel (σ* A* B*) (p₁ , p₂) (p'₁ , p'₂) = Σ[ x* ∈ Rel A* p₁ p'₁ ] Rel (B* p₁ p'₁ x*) p₂ p'₂
  Rel (A* ≃* B*) e e' = ∀ a a' (a* : Rel A* a a') b b' (b* : Rel B* b b') → 
    Eq (a ∼〈 e 〉 b) (a' ∼〈 e' 〉 b')
  Rel (∼* A* B* {e} {e'} e* {a} {a'} a* {b} {b'} b*) γ γ' = 
    Rel {a ∼〈 e 〉 b} {a' ∼〈 e' 〉 b'} (e* a a' a* b b' b*) γ γ'

syntax π A (λ a → B) = π[ a ∶ A ] B
syntax σ A (λ a → B) = σ[ a ∶ A ] B
