{-# OPTIONS --type-in-type #-}

module genSetoid where

open import Setoid
open import prop
open import Data.Product

record graphOver (X : Set) : Set where
  field
    Edg  : Set
    s : Edg → X
    t : Edg → X
open graphOver

data pathsIn {X : Set} (G : graphOver X) : X → X → Set where
  empty : ∀ (x : X) → pathsIn G x x
  plus  : ∀ {z : X} → (e : Edg G) → pathsIn G (t G e) z → pathsIn G (s G e) z
  minus : ∀ {z : X} → (e : Edg G) → pathsIn G (s G e) z → pathsIn G (t G e) z

{- append : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append (empty x) q = q
append (plus e p) q = plus e (append p q)
append (minus e p) q = minus e (append p q) -}

append-reverse : ∀ {X} {G : graphOver X} {x y z : X}
                → pathsIn G y x → pathsIn G y z → pathsIn G z x
append-reverse p (empty _) = p
append-reverse p (plus e q) = append-reverse (minus e p) q
append-reverse p (minus e q) = append-reverse (plus e p) q 

conjugate : ∀ {X} {G : graphOver X} {x x' y y' : X}
            → pathsIn G x x' → pathsIn G y y' → pathsIn G x y → pathsIn G x' y'
conjugate {X} {G} x* y* p = append-reverse y* (append-reverse x* p)

reverse  : ∀ {X} {G : graphOver X} {x y : X} → pathsIn G x y → pathsIn G y x
reverse' : ∀ {X} {G : graphOver X} {x y : X} → pathsIn G x y → pathsIn G y x
reverse  {X} {G} {x} {y} p = append-reverse  (empty x) p
reverse' p = conjugate p (empty _) (empty _)

append  : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append' : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append  p q = append-reverse q (reverse p)
append' p q = conjugate (empty _) q p

generateS : ∀ {X : Set} → graphOver X → Setoid
generateS {X} G = record { El = X; E = pathsIn G; r = empty;
  E* = λ x* y* → (λ xy   → conjugate x* y* xy) ,
                 (λ x'y' → conjugate (reverse x*) (reverse y*) x'y') }

genFun : ∀ {X Y : Set} (f : X → Y) (G : graphOver X) (H : graphOver Y) → Set
genFun f G H = (e : Edg G) → pathsIn H (f (s G e)) (f (t G e))

genFuns : ∀ {X Y} (G : graphOver X) (H : graphOver Y) : graphOver (genFun ? ?)

record genIso {X Y : Set} (fg : X ⇔ Y) (G : graphOver X) (H : graphOver Y) : Set where
  field
    I+ : genFun (proj₁ fg) G H
    I- : genFun (proj₂ fg) H G
    I= : ∀ (x : X) (y : Y) → pathsIn G x ((proj₂ fg) y) ⇔ pathsIn H ((proj₁ fg) x) y
open genIso

record genFibS {X : Set} (G : graphOver X) : Set where
  constructor fibra
  field
    Fam  : X → Set
    FamS : ∀ (x : X) → graphOver (Fam x)
    Fib  : ∀ (e : Edg G) → Fam (s G e) ⇔ Fam (t G e)
    FibI : ∀ (e : Edg G) → genIso (Fib e) (FamS (s G e)) (FamS (t G e))
open genFibS

Π-S-Base : ∀ {X : Set} (G : graphOver X) (F : genFibS G) → Set
Π-S-Base {X} G F = Σ[ f ∈ ((x : X) → Fam F x) ]
                    ((e : Edg G) →
                      pathsIn (FamS F (t G e)) (proj₁ (Fib F e) (f (s G e))) (f (t G e)))

Π-S-S : ∀ {X : Set} (G : graphOver X) (F : genFibS G) → graphOver (Π-S-Base G F)
Π-S-S G (fibra Fam FamS Fib FibI) =
  record {
   Edg = {!(e : Edg G X) → ?!};
   s = {!!};
   t = {!!} }
