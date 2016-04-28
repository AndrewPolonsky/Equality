module stratUniv where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

data U : ℕ → Set
T : ∀ {n} → U n → Set
Eq : ∀ {n} (A : U n) → T A → T A → Set

data U where
  true : U 0
  false : U 0
  build : ∀ {n} → U n → U (suc n)
  _⇒_ : ∀ {n} → U n → U n → U n
  _≃_ : ∀ {n} (A : U (suc n)) (a a' : T A) → U n
  o : U 1

T true = Unit
T false = ⊥
T (build A) = Σ[ a ∈ T A ] Σ[ a' ∈ T A ] Eq A a a'
T (A ⇒ B) = Σ[ f ∈ (T A → T B) ]
          (∀ (a a' : (T A)) → T (_≃_ A a a' ⇒ _≃_ B (f a) (f a')))
T (_≃_ A a a') = Eq A a a'
T o = ℕ

Eq true a b = Unit
Eq false a b = Unit
Eq {suc n} (build A) (a1 , a2 , a3) (a1' , a2' , a3') = Σ[ e1 ∈ Eq A a1 a1' ] Σ[ e2 ∈ Eq A a2 a2' ] {!!}
Eq {0} (A ⇒ B) f g = ∀ (x : T A) → Eq B (f x) (g x)
Eq {suc n} (A ⇒ B) (f , phi) (g , xi) = ∀ (x : T A) → Eq B (f x) (g x)
Eq {0} (_≃_ A a b) e e' = Unit
Eq {suc n} (_≃_ (build A) (proj₁ , a) (proj₂ , a')) (proj₃ , proj₄ , _) e' = ?
Eq {suc n} (_≃_ (A ⇒ A₁) a a') e e' = {!!}
Eq {suc n} (_≃_ (_≃_ A a a') a₁ a'') e e' = {!!}
Eq o n m = n ≡ m

{- T {zero} true = Unit
T {zero} false = ⊥
T {zero} (A ⇒ B) = T A → T B
T {zero} (_≃_ A a a') = Unit
-- T {suc n} A = Σ[ a ∈ T A ] Σ[ a' ∈ T A ] Eq A a a'

Eq {zero} A a b = Unit
Eq {suc n} A a b = Unit
-}
