{-# OPTIONS --no-positivity-check #-}

module Kipling where

open import Level

infix 75 _∘_
_∘_ : ∀ {i} {j} {k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

K : ∀ {i} {j} {A : Set i} {B : Set j} → A → B → A
K a _ = a

infixl 50 _S_
_S_ : ∀ {i} {j} {k} {A : Set i} {B : A → Set j} {C : ∀ a → B a → Set k} →
  (∀ a b → C a b) → ∀ (f : ∀ a → B a) → ∀ a → C a (f a)
(g S f) a = g a (f a)

data Unit : Set where
  unit : Unit

data Σ {A : Set} (B : A → Set) : Set where
  _,_ : ∀ a → B a → Σ B

π₁ : ∀ {A} {B} → Σ B → A
π₁ (a , _) = a

π₂ : ∀ {A} {B} (p : Σ {A} B) → B (π₁ p)
π₂ (_ , b) = b

∨ : ∀ {A} {B} {P : Σ {A} B → Set} → (∀ a b → P (a , b)) → ∀ p → P p
∨ p (a , b) = p a b

∧ : ∀ {i} {A} {B} {P : Σ {A} B → Set i} → (∀ p → P p) → ∀ a b → P (a , b)
∧ p a b = p (a , b)

mutual
  data U : Set where
    * : U
    π : ∀ A → (T A → U) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U
    _∼〈_〉_ : ∀ {A} {B} → T A → Eq A B → T B → U -- TODO Define this instead

  T : U → Set
  T * = U
  T (π A B) = ∀ a → T (B a)
  T (σ A B) = Σ (λ a → T (B a))
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
  Rel (σ* A* B*) (p₁ , p₂) (p'₁ , p'₂) = Σ (λ (x* : Rel A* p₁ p'₁) → 
    Rel (B* p₁ p'₁ x*) p₂ p'₂)
  Rel (A* ≃* B*) e e' = ∀ a a' (a* : Rel A* a a') b b' (b* : Rel B* b b') → 
    Eq (a ∼〈 e 〉 b) (a' ∼〈 e' 〉 b')
  Rel (∼* A* B* {e} {e'} e* {a} {a'} a* {b} {b'} b*) γ γ' = 
    Rel {a ∼〈 e 〉 b} {a' ∼〈 e' 〉 b'} (e* a a' a* b b' b*) γ γ'

mutual
  infixl 70 _,_
  data Context : Set where
    〈〉 : Context
    _,_ : ∀ Γ → (⟦ Γ ⟧C → U) → Context

  ⟦_⟧C : Context → Set
  ⟦ 〈〉 ⟧C = Unit
  ⟦ Γ , A ⟧C = Σ (λ γ → T (A γ))

Type : Context → Set
Type Γ = ⟦ Γ ⟧C → U

⟦_⟧T : ∀ {Γ} → Type Γ → Set
⟦ A ⟧T = ∀ γ → T (A γ)

data Var : ∀ (Γ : Context) (A : Type Γ) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ , A) (A ∘ π₁)
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ , A) (B ∘ π₁)

⟦_⟧V : ∀ {Γ} {A} → Var Γ A → ⟦ A ⟧T
⟦ ⊥ ⟧V (_ , a) = a
⟦ ↑ x ⟧V (γ , _) = ⟦ x ⟧V γ

mutual
  data _⊢_type (Γ : Context) : Type Γ → Set where

  data _⊢_ (Γ : Context) : Type Γ → Set where
    var  : ∀ {A} → Var Γ A → Γ ⊢ A
    star : Γ ⊢ K *
    pi   : ∀ (A : Γ ⊢ K *) → Γ , ⟦ A ⟧ ⊢ K * → Γ ⊢ K *
    sigma : ∀ (A : Γ ⊢ K *) → Γ , ⟦ A ⟧ ⊢ K * → Γ ⊢ K *
    eq   : Γ ⊢ K * → Γ ⊢ K * → Γ ⊢ K *
    ∼    : ∀ {A B : Γ ⊢ K *} → Γ ⊢ (λ γ → ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) → Γ ⊢ ⟦ A ⟧ → Γ ⊢ ⟦ B ⟧ → Γ ⊢ K *
    Λ    : ∀ {A : Γ ⊢ K *} {B : Γ , ⟦ A ⟧ ⊢ K *} → Γ , ⟦ A ⟧ ⊢ ⟦ B ⟧ → Γ ⊢ K π S ⟦ A ⟧ S ∧ ⟦ B ⟧
    app  : ∀ {A : Γ ⊢ K *} {B : Γ , ⟦ A ⟧ ⊢ K *} → Γ ⊢ K π S ⟦ A ⟧ S ∧ ⟦ B ⟧ → ∀ (a : Γ ⊢ ⟦ A ⟧) → Γ ⊢ ∧ ⟦ B ⟧ S ⟦ a ⟧
--TODO: pair, pi1, pi2
    **   : Γ ⊢ K (* ≃ *)
    pistar : ∀ {A A' : Γ ⊢ K *} (A* : Γ ⊢ (λ γ → ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ))
               {B : Γ , ⟦ A ⟧ ⊢ K *} {B' : Γ , ⟦ A' ⟧ ⊢ K *} 
               (B* : Γ , ⟦ A ⟧ , ⟦ A' ⟧ ∘ π₁ , (λ x → ⟦ A ⟧ (π₁ (π₁ x)) ≃ ⟦ A' ⟧ ((π₁ (π₁ x)))) ⊢ λ γ → ⟦ B ⟧ ((π₁ (π₁ (π₁ γ))) , π₂ (π₁ (π₁ γ))) ≃ ⟦ B' ⟧ ((π₁ (π₁ (π₁ γ))) , (π₂ (π₁ γ)))) →
               Γ ⊢ λ γ → π (⟦ A ⟧ γ) (λ a → ⟦ B ⟧ (γ , a)) ≃ π (⟦ A' ⟧ γ) (λ a → ⟦ B' ⟧ (γ , a))

  ⟦_⟧ : ∀ {Γ} {A} → Γ ⊢ A → ⟦ A ⟧T
  ⟦ var x ⟧ γ  = ⟦ x ⟧V γ
  ⟦ star ⟧ _ = *
  ⟦ pi A B ⟧ γ = π (⟦ A ⟧ γ) (‌∧ ⟦ B ⟧ γ)
  ⟦ sigma A B ⟧ γ = σ (⟦ A ⟧ γ) (‌∧ ⟦ B ⟧ γ)
  ⟦ eq A B ⟧ γ = ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ
  ⟦ ∼ e a b ⟧ γ = ⟦ a ⟧ γ ∼〈 ⟦ e ⟧ γ 〉 ⟦ b ⟧ γ
  ⟦ Λ M ⟧ γ = λ a → ⟦ M ⟧ (γ , a)
  ⟦ app M N ⟧ γ = ⟦ M ⟧ γ (⟦ N ⟧ γ)
  ⟦ ** ⟧ γ = r*
  ⟦ pistar A* B* ⟧ γ = π* (⟦ A* ⟧ γ) (λ a a' _ → ⟦ B* ⟧ (((γ , a) , a') , (⟦ A* ⟧ γ)))
