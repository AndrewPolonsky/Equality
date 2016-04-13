{-# OPTIONS --type-in-type #-}
module groupoid where

open import setoid

open import Data.Unit
open import Data.Product
-- open import Data.Nat

record Groupoid : Set where
  field
    Ob : Set
    _≃_ : Ob → Ob → Setoid
    rr : ∀ (x : Ob) → El (x ≃ x)
    ≃* : ∀ {x x' y y' : Ob} → FunS (x ≃ x') (FUNS (y ≃ y') (ISO (x ≃ y) (x' ≃ y')))

open Groupoid using (Ob ; rr) renaming (_≃_ to _∋_≃_)

record ContrG (G : Groupoid) : Set where
  field
    c : Ob G
    p : ∀ (x : Ob G) → El (G ∋ x ≃ c)
    
record Fibra-GS (B : Groupoid) : Set where
  field
    Fib : ∀ (x : Ob B) → Setoid
    Sub : ∀ (x y : Ob B) → FunS (B ∋ x ≃ y) (ISO (Fib x) (Fib y))
    Sub-rr : ∀ (x : Ob B) → E (ISO (Fib x) (Fib x)) (FunS.app (Sub x x) (rr B x)) (id_iso (Fib x))
  Sub-id : ∀ (x : Ob B) (s : El (Fib x)) → Fibra-SP.Fib (Iso.R (FunS.app (Sub x x) (rr B x))) (s , s)
  Sub-id = λ x s → proj₂ (Sub-rr x s s) (r (Fib x) s)

Sigma-GS : ∀ (G : Groupoid) → (Fibra-GS G) → Groupoid
Sigma-GS G S =
  record { Ob = Σ[ g ∈ Ob G ] El (Fibra-GS.Fib S g);
           _≃_ = eq;
           rr = λ x → rr G (proj₁ x) , Fibra-GS.Sub-id S (proj₁ x) (proj₂ x) ;
           ≃* = ≃̂ _ _ _ _ } where
    eq : Σ[ g ∈ Ob G ] El (Fibra-GS.Fib S g) → Σ[ g ∈ Ob G ] El (Fibra-GS.Fib S g) → Setoid
    eq (g , s) (g' , s') =
      Sigma-SP (G ∋ g ≃ g') (record { 
        Fib = (λ p → Fibra-SP.Fib (Iso.R (Fibra-GS.Sub S g g' · p)) (s , s')); 
        Sub = λ x y x₁ → FunS.app1 (Fibra-GS.Sub S g g') x y x₁ s s' })
    ≃̂ : ∀ (x x' y y' : Σ-syntax (Ob G) (λ g → El (Fibra-GS.Fib S g))) →
           FunS (eq x x') (FUNS (eq y y') (ISO (eq x y) (eq x' y')))
    ≃̂ (g1 , s1) (g1' , s1') (g2 , s2) (g2' , s2') = record {
      app = λ { (g1* , s1*) → record {
              app = λ {(g2* , s2*) → record {
                R = record { Fib = λ {((g12 , s12) , (g12' , s12')) → {!!}};
                             Sub = {!!} };
                R+ = {!!};
                R- = {!!} }};
              app1 = {!!} } };
      app1 = {!!} }
    

PRODG : ∀ (G G' : Groupoid) → Groupoid
PRODG G G' = record {
  Ob = Ob G × Ob G';
  _≃_ = Hom} where
  Hom : Ob G × Ob G' → Ob G × Ob G' → Setoid
  Hom (g1 , g1') (g2 , g2') = PRODS (G ∋ g1 ≃ g2) (G' ∋ g1' ≃ g2')

postulate ReflG : ∀ (G : Groupoid) (x : Ob G) → Setoid.El (G ∋ x ≃ x)

Fibra_p1 : ∀ { G G' : Groupoid} → Fibra-GS (PRODG G G') → Ob G' → Fibra-GS G
Fibra_p1 {G} {G'} F Y = record {
    Fib = λ x → Fibra-GS.Fib F (x , Y);
    Sub   = λ x y → record { app = λ p → FunS.app (Fibra-GS.Sub F (x , Y) (y , Y)) (p , ReflG G' Y);
                             app1 = λ x₁ y₁ x₂ x₃ y₂ → (λ x₄ → {!!}) , (λ x₄ → {!!}) } }

record Equiv (G G' : Groupoid) : Set where
  field
    R : Fibra-GS (PRODG G G')
    R+ : ∀ (x : Ob G) → ContrG (Sigma-GS G' {!R !}) -- ContrG (Sigma-GS G' ?)
    R- : ∀ (y : Ob G') → ContrG (Sigma-GS G (Fibra_p1 {G} {G'} R y))


UnitS : Setoid
UnitS = record { El = Unit; E = λ x x₁ → Unit }
UnitG : Groupoid
UnitG = record { Ob = Unit; _≃_ = λ x x₁ → UnitS }

record Fibration (G : Groupoid) : Set where
  field
    Fib : Ob G → Groupoid
    Sub : ∀ (x y : Groupoid.Ob G) → El (G ∋ x ≃ y) → Equiv (Fib x) (Fib y)

postulate SigmaG : ∀ (G : Groupoid) → Fibration G → Groupoid


infixl 70 _,,_
data Context : Set
Type : Context → Set
⟦_⟧C : Context → Groupoid

postulate Fib : (G : Groupoid) → Fibration G → Ob G → Groupoid
-- The collection of contexts Γ

data Context where
  〈〉 : Context
  _,,_ : ∀ Γ → (Type Γ) → Context

-- The collection of Γ-types
Type Γ = Fibration (⟦ Γ ⟧C)

-- The collection of Γ-instances
⟦ 〈〉 ⟧C = UnitG
⟦ Γ ,, A ⟧C = SigmaG ⟦ Γ ⟧C A

-- The elements of a Γ-type on the meta-level
⟦_⟧T : ∀ {Γ} → Type Γ → Set
⟦_⟧T {Γ} A = ∀ γ → Ob (Fib ⟦ Γ ⟧C A γ)

{-
data Var : ∀ (Γ : Context) (A : Type Γ) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ ,, A) (A ∘ proj₁)
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ ,, A) (B ∘ proj₁)

⟦_⟧V : ∀ {Γ} {A} → Var Γ A → ⟦ A ⟧T
⟦ ⊥ ⟧V (_ , a) = a
⟦ ↑ x ⟧V (γ , _) = ⟦ x ⟧V γ

Telescope : ℕ → Set
Telescope zero = U
Telescope (suc n) = Σ[ A ∈ U ] (T A → Telescope n)

cons : ∀ {n} (A : U) → (T A → Telescope n) → Telescope (suc n)
cons A B = A , B

syntax cons A (λ a → B) = a ∶ A ⇒ B

tjt : ∀ {n} Γ → (⟦ Γ ⟧C → Telescope n) → Set -- "Typing judgement with telescope"
data tj (Γ : Context) : Type Γ → Set
infix 75 ⟦_⟧
⟦_⟧ : ∀ {Γ} {A} → tj Γ A → ⟦ A ⟧T

tjt {zero} Γ A = tj Γ A
tjt {suc n} Γ P = tjt {n} (Γ ,, (λ γ → proj₁ (P γ))) (λ γ → proj₂ (P (proj₁ γ)) (proj₂ γ))

syntax tjt Γ (λ γ → A) = γ ∶ Γ ⊢ A

data tj Γ where -- "Typing judgement"
  star  : 

    -------------
      γ ∶ Γ ⊢ *

  var   : ∀ {A} → 

      Var Γ A → 
    ---------------
      γ ∶ Γ ⊢ A γ

  pi    : ∀ 

      (A : (γ ∶ Γ ⊢ *)) → (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)) →
    -----------------------------------------------------
                   γ ∶ Γ ⊢ *

  sigma : ∀ 

      (A : γ ∶ Γ ⊢ *) → (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)) →
    --------------------------------------------------
                   γ ∶ Γ ⊢ *

  eq    : 

      γ ∶ Γ ⊢ * → γ ∶ Γ ⊢ * → 
    ------------------------
            γ ∶ Γ ⊢ *

  ∼     : ∀ 

      {A : γ ∶ Γ ⊢ *}   {B : γ ∶ Γ ⊢ *} → (γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) →
    -------------------------------------------------------------------
                    γ ∶ Γ ⊢ ⟦ A ⟧ γ → γ ∶ Γ ⊢ ⟦ B ⟧ γ → γ ∶ Γ ⊢ *

  Λ     : ∀ 

      {A : γ ∶ Γ ⊢ *}    {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)} →  γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ ⟦ B ⟧ (γ , a)) → 
    ------------------------------------------------------------------------------------------------
                     γ ∶ Γ ⊢ π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)

  app   : ∀ 

      {A : γ ∶ Γ ⊢ *}   {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)} →   γ ∶ Γ ⊢ π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a) →      ∀ (a : γ ∶ Γ ⊢ ⟦ A ⟧ γ) →
    ---------------------------------------------------------------------------------------------------------------------------------
                                     γ ∶ Γ ⊢ ⟦ B ⟧ (γ , (⟦ a ⟧ γ))

  pair  : ∀ 

      {A : γ ∶ Γ ⊢ *}   {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}     (a : γ ∶ Γ ⊢ ⟦ A ⟧ γ) →    γ ∶ Γ ⊢ ⟦ B ⟧ (γ , ⟦ a ⟧ γ) →
    -------------------------------------------------------------------------------------------------------------------
                                   γ ∶ Γ ⊢ σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)

  π₁    : ∀ 

      {A : γ ∶ Γ ⊢ *}     {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)} →      γ ∶ Γ ⊢ σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a) →
    ----------------------------------------------------------------------------------------------------------
                                        γ ∶ Γ ⊢ ⟦ A ⟧ γ

  π₂    : ∀ 

      {A : γ ∶ Γ ⊢ *}        {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}     (p : γ ∶ Γ ⊢ σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) → 
    ---------------------------------------------------------------------------------------------------------------
                      γ ∶ Γ ⊢ ⟦ B ⟧ (γ , (proj₁ (⟦ p ⟧ γ)))

  **    : 

    -----------------
      γ ∶ Γ ⊢ * ≃ *

  pistar : ∀ 

      {A  : γ ∶ Γ ⊢ *}                                         {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}
      {A' : γ ∶ Γ ⊢ *}                                         {B' : γ ∶ Γ ⊢ (a ∶ ⟦ A' ⟧ γ ⇒ *)}
      (A* : γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ (a' ∶ ⟦ A' ⟧ γ ⇒ (a* ∶ a ∼〈 ⟦ A* ⟧ γ 〉 a' ⇒ ⟦ B ⟧ (γ , a) ≃ ⟦ B' ⟧ (γ , a'))))) →
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------
                                  γ ∶ Γ ⊢ (π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) ≃ (π[ a' ∶ ⟦ A' ⟧ γ ] ⟦ B' ⟧ (γ , a'))

  sigmastar : ∀ 

      {A  : γ ∶ Γ ⊢ *}                                         {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}
      {A' : γ ∶ Γ ⊢ *}                                         {B' : γ ∶ Γ ⊢ (a ∶ ⟦ A' ⟧ γ ⇒ *)}
      (A* : γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ (a' ∶ ⟦ A' ⟧ γ ⇒ (a* ∶ a ∼〈 ⟦ A* ⟧ γ 〉 a' ⇒ ⟦ B ⟧ (γ , a) ≃ ⟦ B' ⟧ (γ , a'))))) →
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------
                                  γ ∶ Γ ⊢ (σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) ≃ (σ[ a' ∶ ⟦ A' ⟧ γ ] ⟦ B' ⟧ (γ , a'))

  eqstar : ∀ 

      {A : γ ∶ Γ ⊢ *}                   {B : γ ∶ Γ ⊢ *}
      {A' : γ ∶ Γ ⊢ *}                  {B' : γ ∶ Γ ⊢ *} →
      (γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ ⟦ B ⟧ γ ≃ ⟦ B' ⟧ γ) →
    ----------------------------------------------------------------------
              γ ∶ Γ ⊢ (⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) ≃ (⟦ A' ⟧ γ ≃ ⟦ B' ⟧ γ)

⟦ var x ⟧ γ           = ⟦ x ⟧V γ
⟦ star ⟧ _            = *
⟦ pi A B ⟧ γ          = π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)
⟦ sigma A B ⟧ γ       = σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)
⟦ eq A B ⟧ γ          = ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ
⟦ ∼ e a b ⟧ γ         = ⟦ a ⟧ γ ∼〈 ⟦ e ⟧ γ 〉 ⟦ b ⟧ γ
⟦ Λ M ⟧ γ             = λ a → ⟦ M ⟧ (γ , a)
⟦ app M N ⟧ γ         = ⟦ M ⟧ γ (⟦ N ⟧ γ)
⟦ pair a b ⟧ γ        = (⟦ a ⟧ γ) , (⟦ b ⟧ γ)
⟦ π₁ p ⟧ γ            = proj₁ (⟦ p ⟧ γ)
⟦ π₂ p ⟧ γ            = proj₂ (⟦ p ⟧ γ)
⟦ ** ⟧ γ              = r*
⟦ pistar A* B* ⟧ γ    = π* (⟦ A* ⟧ γ) (λ a a' a* → ⟦ B* ⟧ (((γ , a) , a') , a*))
⟦ sigmastar A* B* ⟧ γ = σ* (⟦ A* ⟧ γ) (λ a a' a* → ⟦ B* ⟧ (((γ , a) , a') , a*))
⟦ eqstar A* B* ⟧ γ    = ⟦ A* ⟧ γ ≃* ⟦ B* ⟧ γ
-}
