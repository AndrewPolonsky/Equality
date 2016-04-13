{-# OPTIONS --type-in-type #-}

module setoid where

open import Data.Product

_⇔_ : Set → Set → Set
p ⇔ q = (p → q) × (q → p)
refl_p : ∀ {p : Set} → p ⇔ p
refl_p = (λ x → x) , (λ x → x)

⇔* : ∀ {p1 p2} → (p1 ⇔ p2) → ∀ {q1 q2} → (q1 ⇔ q2) → (p1 ⇔ q1) ⇔ (p2 ⇔ q2)
⇔* {p1} {p2} p12 {q1} {q2} q12 = (
  (λ x → (λ z → proj₁ q12 (proj₁ x (proj₂ p12 z))) , (λ z → proj₁ p12 (proj₂ x (proj₂ q12 z)))) ,
  (λ x → (λ z → proj₂ q12 (proj₁ x (proj₁ p12 z))) , (λ z → proj₂ p12 (proj₂ x (proj₁ q12 z)))) )

record Setoid : Set where
  field
    El : Set
    E : El → El → Set
    r : ∀ (x : El) → E x x
    E* : ∀ {x x' : El} → E x x' → ∀ {y y' : El} → E y y' → (E x y ⇔ E x' y')
  sym : ∀ {x y : El} → E x y → E y x
  sym {x} {y} p = proj₁ (E* p (r x)) (r x)

_⁻¹ : ∀ {S} {x} {y} → Setoid.E S x y → Setoid.E S y x
_⁻¹ {S} {x} {y} = Setoid.sym S

Prop:Set : Setoid
Prop:Set = record {
  El = Set;
  E = _⇔_;
  r = λ S → refl_p;
  E* = ⇔* }

record ContrS (S : Setoid) : Set where
  open Setoid S
  field
    c : El
    p : ∀ (x : El) → E x c

open Setoid public
    
record Fibra-SP (B : Setoid) : Set where
  field
    Fib : ∀ (x : El B) → Set
    Sub : ∀ (x y : El B) → E B x y → (Fib x ⇔ Fib y)

open Fibra-SP public
    
Sigma-SP : ∀ (S : Setoid) → (Fibra-SP S) → Setoid
Sigma-SP S P = record {
  El = Σ[ s ∈ El S ] (Fibra-SP.Fib P s);
  E = λ x y → Setoid.E S (proj₁ x) (proj₁ y);
  r = λ x → r S (proj₁ x);
  E* = λ {x} {x'} x* {y} {y'} y* → E*0 x x' x* y y' y* } where
  E*0 : (x x' : Σ-syntax (El S) (λ s → Fibra-SP.Fib P s)) →
      E S (proj₁ x) (proj₁ x') →
      (y y' : Σ-syntax (El S) (λ s → Fibra-SP.Fib P s)) →
      E S (proj₁ y) (proj₁ y') →
      E S (proj₁ x) (proj₁ y) ⇔ E S (proj₁ x') (proj₁ y')
  E*0 (x , xp) (x' , xp') x* (y , yp) (y' , yp') y*  =
    (λ x₁ → proj₁ (E* S x* y*) x₁) , (λ x₁ → proj₂ (E* S x* y*) x₁)

PRODS : ∀ (S S' : Setoid) → Setoid
PRODS S S' = record {
  El = El S × El S';
  E = Ê ;
  r = λ x → r̂ x;
  E* = λ x* y* → Ê* _ _ x* _ _ y* } where
  Ê : El S × El S' → El S × El S' → Set
  Ê x y = Setoid.E S (proj₁ x) (proj₁ y) × Setoid.E S' (proj₂ x) (proj₂ y)
  r̂ : ∀ x → Ê x x
  r̂ (x , x') = (r S x , r S' x')
  Ê* : ∀ (x x' : El S × El S') → Ê x x' →
        (y y' : El S × El S') → Ê y y' → Ê x y ⇔ Ê x' y'
  Ê* (x1 , x2) (x1' , x2') (x1* , x2*) (y1 , y2) (y1' , y2') (y1* , y2*) =
    (λ x → (proj₁ (E* S x1* y1*) (proj₁ x)) , (proj₁ (E* S' x2* y2*) (proj₂ x))) ,
    (λ x → (proj₂ (E* S x1* y1*) (proj₁ x)) , (proj₂ (E* S' x2* y2*) (proj₂ x))) 

Fibra-SP-p1 : ∀ {S T : Setoid} → Fibra-SP (PRODS S T) → El T → Fibra-SP S
Fibra-SP-p1 {S} {T} F t = 
  record { Fib = λ s → Fib F (s , t); Sub = λ x y p → Sub F (x , t) (y , t) (p , (r T t)) }

Fibra-SP-p2 : ∀ {S T : Setoid} → Fibra-SP (PRODS S T) → El S → Fibra-SP T
Fibra-SP-p2 {S} {T} F s = 
  record { Fib = λ t → Fib F (s , t); Sub = λ x y p → Sub F (s , x) (s , y) (r S s , p) }

diagS : ∀ (S : Setoid) → Fibra-SP (PRODS S S) 
diagS = λ S → record {
  Fib = λ x → E S (proj₁ x) (proj₂ x);
  Sub = λ x y x₁ → E* S (proj₁ x₁) (proj₂ x₁) }

ax4S : ∀ (S : Setoid) → (x : El S) → ContrS (Sigma-SP S (Fibra-SP-p2 {S} {S} (diagS S) x) )
ax4S S x = record { c = x , r S x; p = λ x → sym S (proj₂ x) }

ax4S' : ∀ (S : Setoid) → (x : El S) → ContrS (Sigma-SP S (Fibra-SP-p1 {S} {S} (diagS S) x) )
ax4S' S x = record { c = x , r S x; p = proj₂ }

record Iso (S S' : Setoid) : Set where
  field
    R : Fibra-SP (PRODS S S')
    R+ : ∀ (x : El S)  → ContrS (Sigma-SP S' ((Fibra-SP-p2 {S} {S'} R x)))
    R- : ∀ (y : El S') → ContrS (Sigma-SP S  (Fibra-SP-p1 {S} {S'} R y))

ISO : ∀ (S S' : Setoid) → Setoid
ISO S S' = record {
  El = Iso S S';
  E = λ i j → ∀ x y → (Fib (Iso.R i) (x , y)) ⇔ (Fib (Iso.R j) (x , y));
  r = λ i → λ x y → refl_p;
--  E* = λ {f} {g} f-is-g {h} {k} h-is-k → ? }
  E* = λ {f} {g} f-is-g {h} {k} h-is-k →
  (λ f-is-h → λ x y → proj₁ (⇔* (f-is-g x y) (h-is-k x y)) (f-is-h x y) ),
  (λ g-is-k → λ x y → proj₂ (⇔* (f-is-g x y) (h-is-k x y)) (g-is-k x y) )}

id_iso : ∀ (S : Setoid) → Iso S S
id_iso = λ S → record { R = diagS S; R+ = ax4S S; R- = ax4S' S }

record FunS (S S' : Setoid) : Set where
  field
    app : El S → El S'
    app1 : ∀ (x y : El S) → Setoid.E S x y → Setoid.E S' (app x) (app y)

FUNS : ∀ (S S' : Setoid) → Setoid
FUNS S S' = record {
  El = FunS S S';
  E = λ f g → ∀ x x' → Setoid.E S x x' → Setoid.E S' (FunS.app f x) (FunS.app g x');
  r = FunS.app1 ;
  E* = λ {f} {f'} f* {g} {g'} g* →
    (λ  f=g  → λ x x' x* → proj₁
      (E* S' (f* x' x (sym S x*)) (g* x' x' (r S x')))
      (f=g x' x' (r S x'))) ,
    (λ f'=g' → λ x₁ x'' x*₁ → proj₂
      (E* S' (f* x₁ x'' x*₁) (g* x'' x'' (r S x''))) 
      (f'=g' x'' x'' (r S x''))) }


