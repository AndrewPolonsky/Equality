{-# OPTIONS --type-in-type #-}

module setoid where

open import prop

record Setoid : Set where
  field
    El : Set
    E : El → El → Set
    r : ∀ (x : El) → E x x
    E* : ∀ {x x' : El} → E x x' → ∀ {y y' : El} → E y y' → (E x y ⇔ E x' y')
  sym : ∀ {x y : El} → E x y → E y x
  sym {x} {y} p = proj₁ (E* p (r x)) (r x)
  trans : ∀ {x y z : El} → E x y → E y z → E x z
  trans {x} {y} {z} p q = proj₂ (E* p (r z)) q

open Setoid public

_⁻¹ : ∀ {S} {x} {y} → E S x y → E S y x
_⁻¹ {S} {x} {y} = sym S

Prop:Set : Setoid
Prop:Set = record {
  El = Set;
  E = _⇔_;
  r = λ S → refl_p;
  E* = ⇔* }
    
record ContrS (S : Setoid) : Set where
  field
    c : El S
    p : ∀ (x : El S) → E S x c

record FibSP (B : Setoid) : Set where
  field
    Fib : ∀ (x : El B) → Set
    Sub : ∀ (x y : El B) → E B x y → (Fib x ⇔ Fib y)
open FibSP
    
Sigma-SP : ∀ (S : Setoid) → (FibSP S) → Setoid
Sigma-SP S P = record {
  El = Σ[ s ∈ El S ] (FibSP.Fib P s);
  E = λ x y → E S (proj₁ x) (proj₁ y);
  r = λ x → r S (proj₁ x);
  E* = λ x* y* → E* S x* y*}

proj₁* : ∀ {S P x x'} → E (Sigma-SP S P) x x' → E S (proj₁ x) (proj₁ x')
proj₁* x* = x*

PRODS : ∀ (S S' : Setoid) → Setoid
PRODS S S' = record {
  El = El S × El S';
  E = λ x y → PRODP (E S (proj₁ x) (proj₁ y)) (E S' (proj₂ x) (proj₂ y)) ;
  r = λ { (x , x') → r S x , r S' x'};
  E* = λ { (x1* , x2*) (y1* , y2*) → PRODP* (E* S x1* y1*) (E* S' x2* y2*) }}

diagS : ∀ (S : Setoid) → FibSP (PRODS S S) 
diagS = λ S → record {
  Fib = λ x → E S (proj₁ x) (proj₂ x);
  Sub = λ x y x₁ → E* S (proj₁ x₁) (proj₂ x₁) }

FibSP-p1 : ∀ {S T : Setoid} → FibSP (PRODS S T) → El T → FibSP S
FibSP-p1 {S} {T} F t = 
  record { Fib = λ s → Fib F (s , t); Sub = λ x y p → Sub F (x , t) (y , t) (p , (r T t)) }

FibSP-p2 : ∀ {S T : Setoid} → FibSP (PRODS S T) → El S → FibSP T
FibSP-p2 {S} {T} F s = 
  record { Fib = λ t → Fib F (s , t); Sub = λ x y p → Sub F (s , x) (s , y) (r S s , p) }

ax4S : ∀ (S : Setoid) → (x : El S) → ContrS (Sigma-SP S (FibSP-p2 {S} {S} (diagS S) x) )
ax4S S x = record { c = x , r S x; p = λ x → sym S (proj₂ x) }

ax4S' : ∀ (S : Setoid) → (x : El S) → ContrS (Sigma-SP S (FibSP-p1 {S} {S} (diagS S) x) )
ax4S' S x = record { c = x , r S x; p = proj₂ }

record Iso (S S' : Setoid) : Set where
  field
    R : FibSP (PRODS S S')
    R+ : ∀ (x : El S)  → ContrS (Sigma-SP S' ((FibSP-p2 {S} {S'} R x)))
    R- : ∀ (y : El S') → ContrS (Sigma-SP S  (FibSP-p1 {S} {S'} R y))

infix 20 _~<_>_
_~<_>_ : ∀ {S S'} → El S → (i : Iso S S') → El S' → Set
a ~< i > b =  Fib (Iso.R i) (a , b)

_~*<_>_ : ∀ {S S'} {x x' : El S} → E S x x' → (i : Iso S S') → {y y' : El S'} → E S' y y' → (x ~< i > y) ⇔ (x' ~< i > y')
x* ~*< i > y* = Sub (Iso.R i) _ _ (x* , y*)

transport : ∀ {S S'} → Iso S S' → El S → El S'
transport {S} {S'} e x = proj₁ (ContrS.c (Iso.R+ e x))

iso-transport : ∀ {S S'} (e : Iso S S') (x : El S) → x ~< e > transport e x
iso-transport {S} {Ś'} e x = proj₂ (ContrS.c (Iso.R+ e x))

transport-unique : ∀ {S S'} (e : Iso S S') (x : El S) (y : El S') → x ~< e > y → E S' y (transport e x)
transport-unique e x y xey = ContrS.p (Iso.R+ e x) (y , xey)

transport* : ∀ {S S'} (e : Iso S S') {x x' : El S} → E S x x' → E S' (transport e x) (transport e x')
transport* {S} {S'} e {x} {x'} x* = transport-unique e x' (transport e x) (proj₁ (x* ~*< e > r S' (transport e x)) (iso-transport e x))

transport⁻¹ : ∀ {S S'} → Iso S S' → El S' → El S
transport⁻¹ e x = proj₁ (ContrS.c (Iso.R- e x))

transport⁻¹-iso : ∀ {S S'} (e : Iso S S') (y : El S') → transport⁻¹ e y ~< e > y
transport⁻¹-iso e x = proj₂ (ContrS.c (Iso.R- e x))

transport⁻¹-unique : ∀ {S S'} (e : Iso S S') (x : El S) (y : El S') → x ~< e > y → E S x (transport⁻¹ e y)
transport⁻¹-unique e x y xey = ContrS.p (Iso.R- e y) (x , xey)

transport⁻¹* : ∀ {S S'} (e : Iso S S') {y y' : El S'} → E S' y y' → E S (transport⁻¹ e y) (transport⁻¹ e y')
transport⁻¹* {S} {S'} e {y} {y'} y* = transport⁻¹-unique e (transport⁻¹ e y) y' (proj₁ (r S (transport⁻¹ e y) ~*< e > y*) (transport⁻¹-iso e y))

transport⁻¹-transport : ∀ {S S'} (e : Iso S S') (x : El S) → E S x (transport⁻¹ e (transport e x))
transport⁻¹-transport e x = transport⁻¹-unique e x (transport e x) (iso-transport e x)

transport-transport⁻¹ : ∀ {S S'} (e : Iso S S') (y : El S') → E S' y (transport e (transport⁻¹ e y))
transport-transport⁻¹ e y = transport-unique e (transport⁻¹ e y) y (transport⁻¹-iso e y)

ISO : ∀ (S S' : Setoid) → Setoid
ISO S S' = record {
  El = Iso S S';
  E = λ i j → ∀ x y → (Fib (Iso.R i) (x , y)) ⇔ (Fib (Iso.R j) (x , y));
  r = λ i → λ x y → refl_p;
  E* = λ f-is-g h-is-k → flip f-is-g h-is-k }

id-iso : ∀ (S : Setoid) → Iso S S
id-iso = λ S → record { R = diagS S; R+ = ax4S S; R- = ax4S' S }

inv-iso : ∀ {S S'} → Iso S S' → Iso S' S
inv-iso e = record { 
  R = record { 
    Fib = λ {(x , y) → y ~< e > x} ;
    Sub = λ {x x' (x* , y*) → y* ~*< e > x*} } ; 
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

record FunS (S S' : Setoid) : Set where
  field
    app : El S → El S'
    app1 : ∀ (x y : El S) → E S x y → E S' (app x) (app y)
infixl 10 _·_
_·_ : ∀ { S T : Setoid } → FunS S T → El S → El T
f · a = FunS.app f a
infixl 10 _•_
_•_ : ∀ { S T : Setoid } → (f : FunS S T) → {s s' : El S} → (E S s s') → (E T (f · s) (f · s'))
f • p = FunS.app1 f _ _ p

TRANSPORT : ∀ {S S'} → Iso S S' → FunS S S'
TRANSPORT e = record { app = transport e ; app1 = λ _ _ → transport* e }

TRANSPORT⁻¹ : ∀ {S S'} → Iso S S' → FunS S' S
TRANSPORT⁻¹ e = record { app = transport⁻¹ e ; app1 = λ _ _ → transport⁻¹* e }

ProdF : ∀ {A A' B B'} → FunS A A' → FunS B B' → FunS (PRODS A B) (PRODS A' B')
ProdF f g = record { 
  app = λ {(a , b) → f · a , g · b} ; 
  app1 = λ {(a , b) (a' , b') (a* , b*) → f • a* , g • b* }}

--The pullback of a fibration along a function is a fibration
pullback : ∀ {S} {S'} → FunS S S' → FibSP S' → FibSP S
pullback f F = record { 
  Fib = λ x → Fib F (f · x) ; 
  Sub = λ x x' x* → Sub F (f · x) (f · x') (f • x*) }

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
        (proj₁ (r A _ ~*< e > transport⁻¹-transport B* _) (iso-transport e _)) ; 
    p = λ {(b' , p) → fill-lm _ e B* b' p}};
  R- = λ b' → record { 
    c = (transport A* (transport⁻¹ e (transport⁻¹ B* b'))) , 
        (proj₁ (transport⁻¹-transport A* _ ~*< e > r B _) (transport⁻¹-iso e _)) ; 
    p = λ {(a' , p) → fill-lm' _ e A* _ p}}}

fill-commutes : ∀ {A A' B B'} (A* : Iso A A') (B* : Iso B B') (e : Iso A B) → square-commutes A* B* e (fill A* B* e)
fill-commutes A* B* e = λ {x} {x'} x~x' {y} {y'} y~y' → transport⁻¹-unique A* x x' x~x' ~*< e > transport⁻¹-unique B* y y' y~y'

fill-commutes' : ∀ {A A' B B'} (A* : Iso A A') (B* : Iso B B') (e : Iso A' B') → square-commutes A* B* (fill (inv-iso A*) (inv-iso B*) e) e
fill-commutes' {A} {A'} {B} {B'} A* B* e = λ {x} {x'} x~x' {y} {y'} y~y' → sym A' (transport⁻¹-unique (inv-iso A*) x' x x~x') ~*< e > sym B' (transport⁻¹-unique (inv-iso B*) y' y y~y')

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
sim* A* B* e e' e* x* y* = e* x* y*

FUNS : ∀ (S S' : Setoid) → Setoid
FUNS S S' = record {
  El = FunS S S';
  E = λ f g → ∀ x x' → E S x x' → E S' (FunS.app f x) (FunS.app g x');
  r = FunS.app1 ;
  E* = λ {f} {f'} f* {g} {g'} g* →
    (λ  f=g  → λ x x' x* → proj₁
      (E* S' (f* x' x (sym S x*)) (g* x' x' (r S x')))
      (f=g x' x' (r S x'))) ,
    (λ f'=g' → λ x₁ x'' x*₁ → proj₂
      (E* S' (f* x₁ x'' x*₁) (g* x'' x'' (r S x''))) 
      (f'=g' x'' x'' (r S x''))) }

record Fibra-SS (B : Setoid) : Set where
  field
    FibSS : ∀ (x : El B) → Setoid
    SubSS : ∀ {x y : El B} → E B x y → Iso (FibSS x) (FibSS y)
    SubSSr : ∀ {x : El B} → E (ISO (FibSS x) (FibSS x)) (SubSS (r B x)) (id-iso (FibSS x))
    SubSS* : ∀ {a a' b b' : El B} (a* : E B a a') (b* : E B b b') (e : E B a b) (e' : E B a' b') → 
      square-commutes (SubSS a*) (SubSS b*) (SubSS e) (SubSS e') 
--Changelog: Changed SubSS*

open Fibra-SS

_∋_~[_]_ : ∀ {B : Setoid} (F : Fibra-SS B) {x y : El B} (_ : El (FibSS F x)) → (p : E B x y) → El (FibSS F y) → Set
_∋_~[_]_ {B} F a p b = a ~< SubSS F p > b

simFib* : ∀ {B : Setoid} (F : Fibra-SS B) {x x'} (x* : E B x x') {y y'} (y* : E B y y')
         (e : E B x y) (e' : E B x' y') 
         {s s'} (s* : F ∋ s ~[ x* ] s') {t t'} (t* : F ∋ t ~[ y* ] t')
         → (F ∋ s ~[ e ] t) ⇔ (F ∋ s' ~[ e' ] t')
simFib* F x* y* e e' = sim* (SubSS F x*) (SubSS F y*) (SubSS F e) (SubSS F e') (SubSS* F x* y* e e')

Pi-SS : ∀ (B : Setoid) (F : Fibra-SS B) → Setoid

Pi-SS B F = record {
  El = Σ[ f ∈ (∀ (x : El B) → El (FibSS F x)) ] (∀ (x y : El B) → (p : E B x y) → F ∋ f x ~[ p ] f y );
  E = λ { (f , φ) (f' , φ') → {x y : El B} (p : E B x y) → F ∋ f x ~[ p ] f' y};
  r = λ {(f , φ) → φ _ _};
  E* = λ { {(f , φ)} {(f' , φ')} f* {(g , ψ)} {(g' , ψ')} g* →
    ∀** (λ x → ∀** (λ y → ∀* (λ p → simFib* F (r B x) (r B y) p p (f* (r B x)) (g* (r B y)))))
  } }
