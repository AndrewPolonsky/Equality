module Syntax.LambdaSimeq where

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  data Fin : ℕ → Set where
    ⊥ : ∀ {n} → Fin (succ n)
    ↑ : ∀ {n} → Fin n → Fin (succ n)

  lift : ∀ {U} {V} → (Fin U → Fin V) → Fin (succ U) → Fin (succ V)
  lift ρ ⊥ = ⊥
  lift ρ (↑ x) = ↑ (ρ x)

  infix 75 _≃_
  data Term : ℕ → Set where
    * : ∀ {V} → Term V
    var : ∀ {V} → Fin V → Term V
    Π : ∀ {V} → Term V → Term (succ V) → Term V
    Σ : ∀ {V} → Term V → Term (succ V) → Term V
    _≃_ : ∀ {V} → Term V → Term V → Term V
    _∼〈_〉_ : ∀ {V} → Term V → Term V → Term V → Term V
    Λ : ∀ {V} → Term V → Term (succ V) → Term V
    app : ∀ {V} → Term V → Term V → Term V
    _,_ : ∀ {V} → Term V → Term V → Term V
    π₁ : ∀ {V} → Term V → Term V
    π₂ : ∀ {V} → Term V → Term V

  rep : ∀ {U} {V} → (Fin U → Fin V) → Term U → Term V
  rep ρ * = *
  rep ρ (var x) = var (ρ x)
  rep ρ (Π A B) = Π (rep ρ A) (rep (lift ρ) B)
  rep ρ (Σ A B) = Σ (rep ρ A) (rep (lift ρ) B)
  rep ρ (A ≃ B) = rep ρ A ≃ rep ρ B
  rep ρ (a ∼〈 e 〉 b) = rep ρ a ∼〈 rep ρ e 〉 rep ρ b
  rep ρ (Λ A b) = Λ (rep ρ A) (rep (lift ρ) b)
  rep ρ (app M N) = app (rep ρ M) (rep ρ N)
  rep ρ (M , N) = rep ρ M , rep ρ N
  rep ρ (π₁ M) = π₁ (rep ρ M)
  rep ρ (π₂ M) = π₂ (rep ρ M)

  liftTerm : ∀ {V} → Term V → Term (succ V)
  liftTerm M = rep ↑ M

  liftSub : ∀ {U} {V} → (Fin U → Term V) → (Fin (succ U) → Term (succ V))
  liftSub σ ⊥ = var ⊥
  liftSub σ (↑ x) = liftTerm (σ x)

  infix 90 _⟦_⟧
  infix 90 _∼〈_〉_
  _⟦_⟧ : ∀ {U} {V} → Term U → (Fin U → Term V) → Term V
  * ⟦ _ ⟧ = *
  var x ⟦ σ ⟧ = σ x
  Π A B ⟦ σ ⟧ = Π (A ⟦ σ ⟧) (B ⟦ liftSub σ ⟧)
  Σ A B ⟦ σ ⟧ = Σ (A ⟦ σ ⟧) (B ⟦ liftSub σ ⟧)
  (A ≃ B) ⟦ σ ⟧ = A ⟦ σ ⟧ ≃ B ⟦ σ ⟧
  (a ∼〈 e 〉 b) ⟦ σ ⟧ = a ⟦ σ ⟧ ∼〈 e ⟦ σ ⟧ 〉 b ⟦ σ ⟧
  Λ A b ⟦ σ ⟧ = Λ (A ⟦ σ ⟧) (b ⟦ liftSub σ ⟧)
  app f a ⟦ σ ⟧ = app (f ⟦ σ ⟧) (a ⟦ σ ⟧)
  (M , N) ⟦ σ ⟧ = M ⟦ σ ⟧ , N ⟦ σ ⟧
  (π₁ M) ⟦ σ ⟧ = π₁ (M ⟦ σ ⟧)
  (π₂ M) ⟦ σ ⟧ = π₂ (M ⟦ σ ⟧)

  ⊥↦_ : ∀ {V} → Term V → Fin (succ V) → Term V
  (⊥↦ M) ⊥     = M
  (⊥↦ _) (↑ x) = var x

  data _conv_ : ∀ {V} → Term V → Term V → Set where
    β : ∀ {V} {A : Term V} {M} {N} → app (Λ A M) N conv M ⟦ ⊥↦ N ⟧
    ref : ∀ {V} {M : Term V} → M conv M
    sym : ∀ {V} {M N : Term V} → M conv N → N conv M
    trans : ∀ {V} {M N P : Term V} → M conv N → N conv P → M conv P
    Π : ∀ {V} {A A' : Term V} {B B' : Term (succ V)} →
      A conv A' → B conv B' → Π A B conv Π A B'
    Σ : ∀ {V} {A A' : Term V} {B B'} → A conv A' → B conv B' → Σ A B conv Σ A' B'
    _≃_ : ∀ {V} {A A' B B' : Term V} → A conv A' → B conv B' → A ≃ B conv A' ≃ B'
    _∼〈_〉_ : ∀ {V} {a a' e e' b b' : Term V} → a conv a' → b conv b' → e conv e' → a ∼〈 e 〉 b conv a' ∼〈 e' 〉 b'
    Λ : ∀ {V} {A A' : Term V} {b b'} → A conv A' → b conv b' → Λ A b conv Λ A' b'
    app : ∀ {V} {f f' a a' : Term V} → f conv f' → a conv a' → app f a conv app f' a'
    _,_ : ∀ {V} {M M' N N' : Term V} → M conv M' → N conv N' → M , N conv M' , N'
    π₁ : ∀ {V} {M N : Term V} → M conv N → π₁ M conv π₁ N
    π₂ : ∀ {V} {M N : Term V} → M conv N → π₂ M conv π₂ N

  infix 75 _,_
  data Context : ℕ → Set where
    〈〉 : Context zero
    _,_ : ∀ {V} → Context V → Term V → Context (succ V)

  typeof : ∀ {V} → Fin V → Context V → Term V
  typeof ⊥ (_ , A) = liftTerm A
  typeof (↑ x) (Γ , _) = liftTerm (typeof x Γ)

  mutual
    data _ctx : ∀ {V} → Context V → Set where
      〈〉 : 〈〉 ctx
      _,_ : ∀ {V} {Γ : Context V} {A} → Γ ⊢ A ∶ * → Γ , A ctx

    infix 2 _⊢_∶_
    data _⊢_∶_ : ∀ {V} → Context V → Term V → Term V → Set where
      * : ∀ {V} {Γ : Context V} → 

        Γ ctx → 
      ------------
        Γ ⊢ * ∶ *

      var : ∀ {V} {Γ : Context V} {x} → 

        Γ ctx → 
    -----------------------------
        Γ ⊢ var x ∶ typeof x Γ

      Π : ∀ {V} {Γ : Context V} {A} {B} → 

        Γ , A ⊢ B ∶ * → 
      ---------------------
        Γ ⊢ Π A B ∶ *

      Σ : ∀ {V} {Γ : Context V} {A} {B} → 

        Γ , A ⊢ B ∶ * → 
      -------------------
        Γ ⊢ Σ A B ∶ *

      ≃R : ∀ {V} {Γ : Context V} {A} {B} → 

        Γ ⊢ A ∶ * → Γ ⊢ B ∶ * → 
      ---------------------------
            Γ ⊢ A ≃ B ∶ *

      ∼ : ∀ {V} {Γ : Context V} {A} {B} {e} {a} {b} →

        Γ ⊢ e ∶ A ≃ B → Γ ⊢ a ∶ A → Γ ⊢ b ∶ B →
      -------------------------------------------
                   Γ ⊢ a ∼〈 e 〉 b ∶ *

      Λ : ∀ {V} {Γ : Context V} {A} {B} {b} →

        Γ , A ⊢ b ∶ B →
      -------------------
        Γ ⊢ Λ A b ∶ Π A B

      app : ∀ {V} {Γ : Context V} {A} {B} {f} {a} →

        Γ ⊢ f ∶ Π A B → Γ ⊢ a ∶ A →
      -------------------------------
          Γ ⊢ app f a ∶ B ⟦ ⊥↦ a ⟧

      pair : ∀ {V} {Γ : Context V} {A} {B} {a} {b} →

        Γ ⊢ a ∶ A → Γ ⊢ b ∶ B ⟦ ⊥↦ a ⟧ →
      ------------------------------------
          Γ ⊢ a , b ∶ Σ A B

      π₁ : ∀ {V} {Γ : Context V} {A} {B} {p} →

        Γ ⊢ p ∶ Σ A B →
      -------------------
        Γ ⊢ π₁ p ∶ A

      π₂ : ∀ {V} {Γ : Context V} {A} {B} {p} →

        Γ ⊢ p ∶ Σ A B →
      ---------------------------
        Γ ⊢ π₂ p ∶ B ⟦ ⊥↦ π₁ p ⟧

      conv : ∀ {V} {Γ : Context V} {M} {A} {B} →

                   Γ ⊢ M ∶ A → Γ ⊢ B ∶ * →
                   A conv B → 
                  ---------------------------
                         Γ ⊢ M ∶ B
