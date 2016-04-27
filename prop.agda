module prop where

open import Data.Product public

_⇔_ : Set → Set → Set
p ⇔ q = (p → q) × (q → p)

id-iff : ∀ {p : Set} → p ⇔ p
id-iff = (λ x → x) , (λ x → x)

⇔* : ∀ {p1 p2} → (p1 ⇔ p2) → ∀ {q1 q2} → (q1 ⇔ q2) → (p1 ⇔ q1) ⇔ (p2 ⇔ q2)
⇔* {p1} {p2} p12 {q1} {q2} q12 = (
  (λ x → (λ z → proj₁ q12 (proj₁ x (proj₂ p12 z))) , (λ z → proj₁ p12 (proj₂ x (proj₂ q12 z)))) ,
  (λ x → (λ z → proj₂ q12 (proj₁ x (proj₁ p12 z))) , (λ z → proj₂ p12 (proj₂ x (proj₁ q12 z)))) )

flip : ∀ {A B : Set} {P Q R S : A → B → Set} → (∀ x y → (P x y ⇔ Q x y)) → (∀ x y → (R x y ⇔ S x y)) → ((∀ x y → (P x y ⇔ R x y)) ⇔ (∀ x y → (Q x y ⇔ S x y)))
flip {A} {B} {P} {Q} {R} {S} P⇔Q R⇔S = 
  (λ P⇔R a b → (λ z → proj₁ (R⇔S a b) (proj₁ (P⇔R a b) (proj₂ (P⇔Q a b) z))) , 
    (λ z → proj₁ (P⇔Q a b) (proj₂ (P⇔R a b) (proj₂ (R⇔S a b) z)))) , 
  (λ Q⇔S a b → (λ z → proj₂ (R⇔S a b) (proj₁ (Q⇔S a b) (proj₁ (P⇔Q a b) z))) , 
    (λ z → proj₂ (P⇔Q a b) (proj₂ (Q⇔S a b) (proj₁ (R⇔S a b) z))))

PRODP : Set → Set → Set
PRODP p q = p × q

PRODP* : ∀ {p p'} (p* : p ⇔ p') {q q'} (q* : q ⇔ q') → PRODP p q ⇔ PRODP p' q'
PRODP* (pp' , p'p) (qq' , q'q) = (λ {(x , y) → pp' x , qq' y}) , (λ {(x , y) → p'p x , q'q y})

FUNP : Set → Set → Set
FUNP p q = p → q

FUNP* : ∀ {p p'} (p* : p ⇔ p') {q q'} (q* : q ⇔ q') → FUNP p q ⇔ FUNP p' q'
FUNP* (pp' , p'p) (qq' , q'q) = (λ z z₁ → qq' (z (p'p z₁))) , (λ z z₁ → q'q (z (pp' z₁)))
