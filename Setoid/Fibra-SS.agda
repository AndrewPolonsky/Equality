module Setoid.Fibra-SS where

open import Data.Product
open import Prop
open import Setoid

record Fibra-SS (B : Setoid) : Set where
  field
    FibSS : ∀ (x : El B) → Setoid
    SubSS : ∀ {x y : El B} → E B x y → Iso (FibSS x) (FibSS y)
    SubSSr : ∀ {x : El B} → E (ISO (FibSS x) (FibSS x)) (SubSS (r B x)) (id-iso (FibSS x))
    SubSS* : ∀ {a a' b b' : El B} (a* : E B a a') (b* : E B b b') (e : E B a b) (e' : E B a' b') → 
      square-commutes (SubSS a*) (SubSS b*) (SubSS e) (SubSS e') 

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
