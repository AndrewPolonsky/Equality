{-# OPTIONS --type-in-type #-}

module Setoid.Isomorphism where

open import prop
open import Setoid
open import Setoid.Product
open import Setoid.Function
open import Setoid.Fibra-SP
open import Setoid.Sigma-SP

record Iso (S S' : Setoid) : Set where
  field
    R : FibSP (PRODS S S')
    R+ : ∀ (x : El S)  → ContrS (Sigma-SP S' (FibSP-p2 {S} {S'} R x))
    R- : ∀ (y : El S') → ContrS (Sigma-SP S  (FibSP-p1 {S} {S'} R y))

infix 20 _~<_>_
_~<_>_ : ∀ {S S'} → El S → (i : Iso S S') → El S' → Set
a ~< i > b =  Fib (Iso.R i) (a , b)

iso-cong : ∀ {S S'} {x x' : El S} (i : Iso S S') {y y' : El S'} → E S x x' → E S' y y' → (x ~< i > y ⇔ x' ~< i > y')
iso-cong i x* y* = Sub (Iso.R i) _ _ (x* , y*)

transport : ∀ {S S'} → Iso S S' → El S → El S'
transport {S} {S'} e x = proj₁ (ContrS.c (Iso.R+ e x))

iso-transport : ∀ {S S'} (e : Iso S S') (x : El S) → x ~< e > transport e x
iso-transport {S} {Ś'} e x = proj₂ (ContrS.c (Iso.R+ e x))

transport-unique : ∀ {S S'} (e : Iso S S') (x : El S) (y : El S') → x ~< e > y → E S' y (transport e x)
transport-unique e x y xey = ContrS.p (Iso.R+ e x) (y , xey)

transport* : ∀ {S S'} (e : Iso S S') {x x' : El S} → E S x x' → E S' (transport e x) (transport e x')
transport* {S} {S'} e {x} {x'} x* = transport-unique e x' (transport e x) (proj₁ (iso-cong e x* (r S' (transport e x))) (iso-transport e x))

transport⁻¹ : ∀ {S S'} → Iso S S' → El S' → El S
transport⁻¹ e x = proj₁ (ContrS.c (Iso.R- e x))

transport⁻¹-iso : ∀ {S S'} (e : Iso S S') (y : El S') → transport⁻¹ e y ~< e > y
transport⁻¹-iso e x = proj₂ (ContrS.c (Iso.R- e x))

transport⁻¹-unique : ∀ {S S'} (e : Iso S S') (x : El S) (y : El S') → x ~< e > y → E S x (transport⁻¹ e y)
transport⁻¹-unique e x y xey = ContrS.p (Iso.R- e y) (x , xey)

transport⁻¹* : ∀ {S S'} (e : Iso S S') {y y' : El S'} → E S' y y' → E S (transport⁻¹ e y) (transport⁻¹ e y')
transport⁻¹* {S} {S'} e {y} {y'} y* = transport⁻¹-unique e (transport⁻¹ e y) y' (proj₁ (iso-cong e (r S (transport⁻¹ e y)) y*) (transport⁻¹-iso e y))

transport-transport⁻¹ : ∀ {S S'} (e : Iso S S') (y : El S') → E S' y (transport e (transport⁻¹ e y))
transport-transport⁻¹ e y = transport-unique e (transport⁻¹ e y) y (transport⁻¹-iso e y)

transport⁻¹-transport : ∀ {S S'} (e : Iso S S') (x : El S) → E S x (transport⁻¹ e (transport e x))
transport⁻¹-transport e x = transport⁻¹-unique e x (transport e x) (iso-transport e x)

ISO : Setoid → Setoid → Setoid
ISO S S' = record {
  El = Iso S S';
  E = λ i j → ∀ x y → (Fib (Iso.R i) (x , y)) ⇔ (Fib (Iso.R j) (x , y));
  r = λ i → λ x y → refl-p;
  E* = λ f-is-g h-is-k → flip f-is-g h-is-k }

_~*<_>_ : ∀ {S S'} {x x' : El S} {i i' : Iso S S'} {y y' : El S'} → E S x x' → E (ISO S S') i i' → E S' y y' → (x ~< i > y) ⇔ (x' ~< i' > y')
_~*<_>_ {S} {S'} {x} {x'} {i} {i'} {y} {y'} x* i* y* = trans Prop:Set (i* x y) (Sub (Iso.R i') (x , y) (x' , y') (x* , y*))

id-iso : ∀ (S : Setoid) → Iso S S
id-iso = λ S → record { R = diagS S; R+ = ax4S S; R- = ax4S' S }

inv-iso : ∀ {S S'} → Iso S S' → Iso S' S
inv-iso e = record { 
  R = record { 
    Fib = λ {(x , y) → y ~< e > x} ;
    Sub = λ {x x' (x* , y*) → iso-cong e y* x*} };
  R+ = λ x' → record { 
    c = (transport⁻¹ e x') , 
        (transport⁻¹-iso e x') ; 
    p = λ {(_ , p) → transport⁻¹-unique e _ x' p} } ; 
  R- = λ x → record { 
    c = transport e x , iso-transport e x ; 
    p = λ {(_ , p) → transport-unique e _ _ p} } }

square-commutes : ∀ {A A' B B'} → Iso A A' → Iso B B' → Iso A B → Iso A' B' → Set
square-commutes A* B* e e' = ∀ {x} {x'} → x ~< A* > x' → ∀ {y} {y'} → y ~< B* > y' → x ~< e > y ⇔ x' ~< e' > y'

square-commutes* : ∀ {A A' B B' i i' j j' e e' f f'} → E (ISO A A') i i' → E (ISO B B') j j' → E (ISO A B) e e' → E (ISO A' B') f f' → square-commutes i j e f ⇔ square-commutes i' j' e' f'
square-commutes* i* j* e* f* = ∀** (λ x → ∀** (λ x' → imp* (i* x x') (∀** (λ y → ∀** (λ y' → imp* (j* y y') (⇔* (e* x y) (f* x' y')))))))

SQUARE-COMMUTES : ∀ {A A' B B'} → Iso A A' → Iso B B' → FibSP (PRODS (ISO A B) (ISO A' B'))
SQUARE-COMMUTES {A} {A'} {B} {B'} A* B* = record { 
  Fib = λ {(e , e') → square-commutes A* B* e e'} ; 
  Sub = λ {(i , i') (j , j') (i=j , i'=j') → square-commutes* {A} {A'} {B} {B'} {A*} {A*} {B*} {B*} {i} {j} {i'} {j'} (r (ISO A A') A*) (r (ISO B B') B*) i=j i'=j'} }

TRANSPORT : ∀ {S S'} → Iso S S' → FunS S S'
TRANSPORT e = record { app = transport e ; app1 = λ _ _ → transport* e }

TRANSPORT⁻¹ : ∀ {S S'} → Iso S S' → FunS S' S
TRANSPORT⁻¹ e = record { app = transport⁻¹ e ; app1 = λ _ _ → transport⁻¹* e }

--TODO: Refactor as follows
--1. Define isomorphism of fibrations
--2. Prove FibSP-p2 (pullback (ProdF f g) P) x ~= pullback g (FibSP-p2 P (f · x))
--3. Prove that, if P is contractible and pullback g P is inhabited, then it is contractible
--3. Prove that, if P ~= Q then ContrS P → ContrS Q

fill-lm : ∀ {A B B'} (a : El A) (e : Iso A B) (B* : Iso B B') (b' : El B') →
  a ~< e > transport⁻¹ B* b' → E B' b' (transport B* (transport e a))
fill-lm {A} {B} {B'} a e B* b' aeb' = trans B' (transport-transport⁻¹ B* b') (transport* B* (transport-unique e a _ aeb'))

fill-lm' : ∀ {A A' B} (a' : El A') (e : Iso A B) (A* : Iso A A') (b : El B) →
  transport⁻¹ A* a' ~< e > b → E A' a' (transport A* (transport⁻¹ e b))
fill-lm' {A} {A'} {B} a' e A* b a'eb = trans A' (transport-transport⁻¹ A* a') (transport* A* (transport⁻¹-unique e _ _ a'eb))
--TODO Extract common pattern

fill : ∀ {A A' B B'} → Iso A A' → Iso B B' → Iso A B → Iso A' B'
fill {A} {A'} {B} {B'} A* B* e = record { 
  R = pullback (ProdF (TRANSPORT⁻¹ A*) (TRANSPORT⁻¹ B*)) (Iso.R e) ;
  R+ = λ a' → record { 
    c = (transport B* (transport e (transport⁻¹ A* a'))) , 
        (proj₁ (iso-cong e (r A _) (transport⁻¹-transport B* _)) (iso-transport e _)) ; 
    p = λ {(b' , p) → fill-lm _ e B* b' p}};
  R- = λ b' → record { 
    c = (transport A* (transport⁻¹ e (transport⁻¹ B* b'))) , 
        (proj₁ (iso-cong e (transport⁻¹-transport A* _) (r B _)) (transport⁻¹-iso e _)) ; 
    p = λ {(a' , p) → fill-lm' _ e A* _ p}}}

fill-commutes : ∀ {A A' B B'} (A* : Iso A A') (B* : Iso B B') (e : Iso A B) → square-commutes A* B* e (fill A* B* e)
fill-commutes A* B* e = λ {x} {x'} x~x' {y} {y'} y~y' → iso-cong e (transport⁻¹-unique A* x x' x~x') (transport⁻¹-unique B* y y' y~y')

fill-commutes' : ∀ {A A' B B'} (A* : Iso A A') (B* : Iso B B') (e : Iso A' B') → square-commutes A* B* (fill (inv-iso A*) (inv-iso B*) e) e
fill-commutes' {A} {A'} {B} {B'} A* B* e = λ {x} {x'} x~x' {y} {y'} y~y' → iso-cong e (sym A' (transport⁻¹-unique (inv-iso A*) x' x x~x')) (sym B' (transport⁻¹-unique (inv-iso B*) y' y y~y'))

Iso* : ∀ {A A' : Setoid} (A* : Iso A A') {B B' : Setoid} (B* : Iso B B') →
  Iso (ISO A B) (ISO A' B')
Iso* {A} {A'} A* {B} {B'} B* = record { 
  R = SQUARE-COMMUTES A* B*;
  R+ = λ e → record { 
    c = fill A* B* e , 
        fill-commutes A* B* e ;
    p = λ {(e' , p) x' y' → sym Prop:Set (p (transport⁻¹-iso A* x') (transport⁻¹-iso B* y'))} } ; 
  R- = λ e → record { 
    c = (fill (inv-iso A*) (inv-iso B*) e) , 
        fill-commutes' A* B* e ; 
    p = λ {(e' , p) x' y' → p (iso-transport A* x') (iso-transport B* y')} } }

sim* : ∀ {A A'} (A* : Iso A A') {B B'} (B* : Iso B B')
         (e : Iso A B) (e' : Iso A' B') (e* : e ~< Iso* A* B* > e')
         {x x'} (x* : x ~< A* > x') {y y'} (y* : y ~< B* > y')
         → (x ~< e > y) ⇔ (x' ~< e' > y')
sim* _ _ _ _ e* = e*
--TODO Inline this?
