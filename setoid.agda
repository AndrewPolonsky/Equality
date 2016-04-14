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

ISO : ∀ (S S' : Setoid) → Setoid
ISO S S' = record {
  El = Iso S S';
  E = λ i j → ∀ x y → (Fib (Iso.R i) (x , y)) ⇔ (Fib (Iso.R j) (x , y));
  r = λ i → λ x y → refl_p;
  E* = λ f-is-g h-is-k → flip f-is-g h-is-k }

infix 20 _~<_>_
_~<_>_ : ∀ {S S'} → El S → (i : Iso S S') → El S' → Set
a ~< i > b =  FibSP.Fib (Iso.R i) (a , b)

id-iso : ∀ (S : Setoid) → Iso S S
id-iso = λ S → record { R = diagS S; R+ = ax4S S; R- = ax4S' S }

Iso* : ∀ {A A' : Setoid} (A* : Iso A A') {B B' : Setoid} (B* : Iso B B') →
  Iso (ISO A B) (ISO A' B')
Iso* {A} {A'} A* {B} {B'} B* = record {
  R = record {
    Fib =  λ { (e , e') → ∀ {x} {x'} (_ : x ~< A* > x') {y} {y'} (_ : y ~< B* > y')
                            → (x ~< e > y) ⇔ (x' ~< e' > y')} ;
    Sub = λ { (i , i') (j , j') (i=j , i=j') →
      (λ i* → λ {x} {x'} x* {y} {y'} y* → proj₁ (⇔* (i=j x y) (i=j' x' y')) (i* x* y*)) ,
      (λ j* → λ {x} {x'} x* {y} {y'} y* → proj₂ (⇔* (i=j x y) (i=j' x' y')) (j* x* y*)) } };
  R+ = {!!}; {- λ e → record { c = (record {
                          R = {!λ x' y' → Σ !};
                          R+ = {!!};
                          R- = {!!} }) , {!!}; p = {!!} };-} 
  R- = {!!} }

sim* : ∀ {A A'} (A* : Iso A A') {B B'} (B* : Iso B B')
         (e : Iso A B) (e' : Iso A' B') (e* : e ~< Iso* A* B* > e')
         {x x'} (x* : x ~< A* > x') {y y'} (y* : y ~< B* > y')
         → (x ~< e > y) ⇔ (x' ~< e' > y')
sim* A* B* e e' e* x* y* = e* x* y*

{-
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
    SubSS* : ∀ {x y : El B} → (p q : E B x y) → E (ISO (FibSS x) (FibSS y)) (SubSS p) (SubSS q)

open Fibra-SS

_∋_~[_]_ : ∀ {B : Setoid} (F : Fibra-SS B) {x y : El B} (_ : El (FibSS F x)) → (p : E B x y) → El (FibSS F y) → Set
_∋_~[_]_ {B} F a p b = a ~< SubSS F p > b

simFib* : ∀ {B : Setoid} (F : Fibra-SS B) {x x'} (x* : E B x x') {y y'} (y* : E B y y')
         (e : E B x y) (e' : E B x' y') 
         {s s'} (s* : F ∋ s ~[ x* ] s') {t t'} (t* : F ∋ t ~[ y* ] t')
         → (F ∋ s ~[ e ] t) ⇔ (F ∋ s' ~[ e' ] t')
simFib* F x* y* e e' s* t* = sim* (SubSS F x*) (SubSS F y*) (SubSS F e) (SubSS F e') 
  (λ {a} {a'} a* {b} {b'} b* → {!!}) 
  s* t*

Pi-SS : ∀ (B : Setoid) (F : Fibra-SS B) → Setoid

Pi-SS B F = record {
  El = Σ[ f ∈ (∀ (x : El B) → El (FibSS F x)) ] (∀ (x y : El B) → (p : E B x y) → F ∋ f x ~[ p ] f y );
  E = λ { (f , φ) (f' , φ') → {x y : El B} (p : E B x y) → F ∋ f x ~[ p ] f' y};
  r = λ {(f , φ) → φ _ _};
  E* = λ { {(f , φ)} {(f' , φ')} f* {(g , ψ)} {(g' , ψ')} g* →
    (λ f=g {x} {y} p → proj₁ (sim* (id-iso B) (id-iso B) {!!} {!!} {!!} {!!} {!!}) {!!}) , {!!}
  } }

-}
