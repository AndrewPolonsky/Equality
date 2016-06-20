{-# OPTIONS --type-in-type #-}
module groupoid where

open import prop
open import Setoid
open import Setoid.Function
open import Setoid.Isomorphism
open import Setoid.Product
open import Setoid.Fibra-SP renaming (Fib to Fib-SP;Sub to Sub-SP)
open import Setoid.Sigma-SP
open import Data.Unit
open import Data.Product
-- open import Data.Nat

record Groupoid : Set where
  field
    Ob : Set
    Eq : Ob → Ob → Setoid
    rr : ∀ (x : Ob) → El (Eq x x)
    ≃* : ∀ {x x' y y' : Ob} → FunS (PRODS (Eq x x') (Eq y y')) (ISO (Eq x y) (Eq x' y'))

open Groupoid public

_∋_≃_ : ∀ G → Ob G → Ob G → Set
G ∋ x ≃ y = El (Eq G x y)

record ContrG (G : Groupoid) : Set where
  field
    c : Ob G
    p : ∀ (x : Ob G) → G ∋ x ≃ c
    
record Fibra-GS (B : Groupoid) : Set where
  field
    Fib : ∀ (x : Ob B) → Setoid
    Sub : ∀ {x y : Ob B} → FunS (Eq B x y) (ISO (Fib x) (Fib y))
    Sub-rr : ∀ (x : Ob B) → E (ISO (Fib x) (Fib x)) (Sub · rr B x) (id-iso (Fib x))
    Sub-≃* : ∀ {a a' b b' : Ob B} (a* : B ∋ a ≃ a') (b* : B ∋ b ≃ b') (a≃b : B ∋ a ≃ b) (a'≃b' : B ∋ a' ≃ b') →
      (a≃b ~< ≃* B · a* · b* > a'≃b') ⇔ (Sub · a≃b ~< Iso* (Sub · a*) (Sub · b*) > Sub · a'≃b')

  HE : ∀ {x y : Ob B} → El (Fib x) → (p : B ∋ x ≃ y) → El (Fib y) → Set
  HE a p b = Fib-SP (Iso.R (Sub · p)) (a , b)

  Sub-id : ∀ (x : Ob B) (s : El (Fib x)) → HE s (rr B x) s
  Sub-id = λ x s → proj₂ (Sub-rr x s s) (r (Fib x) s)

  Sub-lm : ∀ {a a' b b' : Ob B} {a* : B ∋ a ≃ a'} {b* : B ∋ b ≃ b'} {p : B ∋ a ≃ b} {q : B ∋ a' ≃ b'}
    {x x' y y'} →
    p ~< ≃* B · a* · b* > q → x ~< Sub · a* > x' → y ~< Sub · b* > y' →
    x ~< Sub · p > y ⇔ x' ~< Sub · q > y'
  Sub-lm {a} {a'} {b} {b'} {a*} {b*} {p} {q} p~q x~x' y~y' = 
    proj₁ (Sub-≃* a* b* p q) p~q x~x' y~y'

  Sub-transport : ∀ {a a' b b' : Ob B} (a* : B ∋ a ≃ a') (b* : B ∋ b ≃ b') (a≃b : B ∋ a ≃ b) →
    E (ISO (Fib a') (Fib b')) (Sub · (transport (≃* B · a* · b*) a≃b)) (transport (Iso* (Sub · a*) (Sub · b*)) (Sub · a≃b))
  Sub-transport a* b* a≃b = λ x y → sym Prop:Set (Sub-lm (iso-transport (≃* B · a* · b*) a≃b) (transport⁻¹-iso (Sub · a*) x) (transport⁻¹-iso (Sub · b*) y))

_∋_~<_>_ : ∀ {B : Groupoid} → (F : Fibra-GS B) → {x y : Ob B} →
           El (Fibra-GS.Fib F x) → (p : B ∋ x ≃ y) → El (Fibra-GS.Fib F y) → Set
_∋_~<_>_ = Fibra-GS.HE

Sigma-GS : ∀ (G : Groupoid) → (Fibra-GS G) → Groupoid
Sigma-GS G S =
  record { Ob = Σ[ g ∈ Ob G ] El (Fibra-GS.Fib S g);
           Eq = eq;
           rr = λ x → rr G (proj₁ x) , Fibra-GS.Sub-id S (proj₁ x) (proj₂ x) ;
           ≃* = ≃̂ _ _ _ _ } where
    eq : Σ[ g ∈ Ob G ] El (Fibra-GS.Fib S g) → Σ[ g ∈ Ob G ] El (Fibra-GS.Fib S g) → Setoid
    eq (g , s) (g' , s') =
      Sigma-SP (Eq G g g') (record { 
        Fib = (λ p → (S ∋ s ~< p > s'));
        Sub = λ x y p → (Fibra-GS.Sub S • p) s s'})
    ≃̂ : ∀ (x x' y y' : Σ-syntax (Ob G) (λ g → El (Fibra-GS.Fib S g))) →
           FunS (eq x x') (FUNS (eq y y') (ISO (eq x y) (eq x' y')))
    ≃̂ (g1 , s1) (g1' , s1') (g2 , s2) (g2' , s2') = record {
      app = λ { (g1* , s1*) → record {
              app = λ {(g2* , s2*) → record {
                R = record { Fib = λ {((g12 , s12) , (g12' , s12'))
                                     → g12 ~< ≃* G · g1* · g2* > g12'};
                             Sub = λ {((g12 , s12) , g12' , s12') →
                                   λ {((g12# , s12#) , g12#' , s12#') →
                                     Sub-SP (Iso.R (≃* G · g1* · g2*))
                                       (g12 , g12') (g12# , g12#') }}};
                R+ = λ {(g1=g2 , s1~s2) → record { 
                  c = ((transport (≃* G · g1* · g2*) g1=g2) , 
                      proj₁ (Fibra-GS.Sub-lm S (iso-transport (≃* G · g1* · g2*) g1=g2) s1* s2*) s1~s2) ,
                      iso-transport (≃* G · g1* · g2*) g1=g2 ; 
                  p = λ {((g1'=g2' , _) , g1=g2~g1'=g2') → transport-unique (≃* G · g1* · g2*) g1=g2 g1'=g2' g1=g2~g1'=g2'} }};
                R- = λ {(g1'=g2' , s1'=s2') → record { 
                  c = (transport⁻¹ (≃* G · g1* · g2*) g1'=g2' , 
                      proj₂
                        (Fibra-GS.Sub-lm S (transport⁻¹-iso (≃* G · g1* · g2*) g1'=g2') s1*
                         s2*)
                        s1'=s2') , 
                      transport⁻¹-iso (≃* G · g1* · g2*) g1'=g2' ; 
                  p = λ {((g1=g2 , _) , g1=g2~g1'=g2') → transport⁻¹-unique (≃* G · g1* · g2*) g1=g2 g1'=g2' g1=g2~g1'=g2'} }} }};
              app1 = λ { (g2≃g2' , s2~s2') (g2≃'g2' , s2~'s2') g2≃g2'=g2≃'g2' (g1≃g2 , s1~s2) (g1'≃g2' , s1'~s2') →
                       proj₁ (_~*<_>_ {Eq G g1 g2} {Eq G g1' g2'} {g1≃g2} {g1≃g2} {≃* G · g1* · g2≃g2'} {≃* G · g1* · g2≃'g2'} {g1'≃g2'} {g1'≃g2'} (r (Eq G g1 g2) g1≃g2) 
                         (≃* G · g1* • g2≃g2'=g2≃'g2') (r (Eq G g1' g2') g1'≃g2'))
                         , proj₁ (_~*<_>_ {Eq G g1 g2} {Eq G g1' g2'} {g1≃g2} {g1≃g2} {≃* G · g1* · g2≃'g2'} {≃* G · g1* · g2≃g2'} {g1'≃g2'} {g1'≃g2'} (r (Eq G g1 g2) g1≃g2) 
                              (≃* G · g1* • sym (Eq G g2 g2') g2≃g2'=g2≃'g2') (r (Eq G g1' g2') g1'≃g2')) } } }; --TODO Refactor as immediately below
      app1 = λ {(g1≃g1' , s1~s1') (g1≃'g1' , s1~'s1') g1≃g1'~g1≃'g1' (g2≃g2' , s2~s2') (g2≃'g2' , s2~'s2') g2≃g2'~g2≃'g2' (g1≃g2 , s1~s2) (g1'≃g2' , s1'~s2') → 
        (≃* G • g1≃g1'~g1≃'g1') g2≃g2' g2≃'g2' g2≃g2'~g2≃'g2' g1≃g2 g1'≃g2' } }
    

PRODG : ∀ (G G' : Groupoid) → Groupoid
PRODG G G' = record {
  Ob = Ob G × Ob G';
  Eq = Hom} where
  Hom : Ob G × Ob G' → Ob G × Ob G' → Setoid
  Hom (g1 , g1') (g2 , g2') = PRODS (Eq G g1 g2) (Eq G' g1' g2')

postulate ReflG : ∀ (G : Groupoid) (x : Ob G) → G ∋ x ≃ x

Fibra_p1 : ∀ { G G' : Groupoid} → Fibra-GS (PRODG G G') → Ob G' → Fibra-GS G
Fibra_p1 {G} {G'} F Y = record {
    Fib = λ x → Fibra-GS.Fib F (x , Y);
    Sub   = λ {x} {y} → record { app = λ p → Fibra-GS.Sub F · (p , ReflG G' Y);
                             app1 = λ x₁ y₁ x₂ x₃ y₂ → (λ x₄ → {!!}) , (λ x₄ → {!!}) } }

record Equiv (G G' : Groupoid) : Set where
  field
    R : Fibra-GS (PRODG G G')
    R+ : ∀ (x : Ob G) → ContrG (Sigma-GS G' {!R !}) -- ContrG (Sigma-GS G' ?)
    R- : ∀ (y : Ob G') → ContrG (Sigma-GS G (Fibra_p1 {G} {G'} R y))


UnitS : Setoid
UnitS = record { El = ⊤; E = λ x x₁ → ⊤ }
UnitG : Groupoid
UnitG = record { Ob = ⊤; Eq = λ x x₁ → UnitS }

Diag : ∀ G → Fibra-GS (PRODG G G)
Diag G = ?

{-

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

  ~     : ∀ 

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
      (A* : γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ (a' ∶ ⟦ A' ⟧ γ ⇒ (a* ∶ a ~〈 ⟦ A* ⟧ γ 〉 a' ⇒ ⟦ B ⟧ (γ , a) ≃ ⟦ B' ⟧ (γ , a'))))) →
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------
                                  γ ∶ Γ ⊢ (π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) ≃ (π[ a' ∶ ⟦ A' ⟧ γ ] ⟦ B' ⟧ (γ , a'))

  sigmastar : ∀ 

      {A  : γ ∶ Γ ⊢ *}                                         {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}
      {A' : γ ∶ Γ ⊢ *}                                         {B' : γ ∶ Γ ⊢ (a ∶ ⟦ A' ⟧ γ ⇒ *)}
      (A* : γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ (a' ∶ ⟦ A' ⟧ γ ⇒ (a* ∶ a ~〈 ⟦ A* ⟧ γ 〉 a' ⇒ ⟦ B ⟧ (γ , a) ≃ ⟦ B' ⟧ (γ , a'))))) →
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
⟦ ~ e a b ⟧ γ         = ⟦ a ⟧ γ ~〈 ⟦ e ⟧ γ 〉 ⟦ b ⟧ γ
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
