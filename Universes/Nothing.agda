module Nothing where

open import Data.Product

mutual
  data U : Set where
    π : ∀ (A : U) (B : T A → U) → (∀ x y → A ∋ x ≡ y → B x ≅ B y) → U

  record _≅_ (A B : U) : Set where
    field
      iso : T A → T B
      inv : T B → T A
      isowd : ∀ x y → A ∋ x ≡ y → B ∋ iso x ≡ iso y
      invwd : ∀ x y → B ∋ x ≡ y → A ∋ inv x ≡ inv y
      isoinv : ∀ y → B ∋ iso (inv y) ≡ y
      inviso : ∀ x → A ∋ inv (iso x) ≡ x

  T : U → Set
  T (π A B B*) = Σ[ f ∈ (∀ x → T (B x)) ] (∀ x y (e : A ∋ x ≡ y) → B y ∋ _≅_.iso (B* x y e) (f x) ≡ f y)

  _∋_≡_ : ∀ A → T A → T A → Set
  π A B B* ∋ (f , _) ≡ (g , _) = ∀ x → B x ∋ f x ≡ g x

ref : ∀ A a → A ∋ a ≡ a
ref (π A B B*) (f , f*) = λ x → ref (B x) (f x)

sym : ∀ A a b → A ∋ a ≡ b → A ∋ b ≡ a
sym (π A B B*) (f , f*) (g , g*) f-is-g = λ x → sym (B x) (f x) (g x) (f-is-g x)

trans : ∀ A a b c → A ∋ a ≡ b → A ∋ b ≡ c → A ∋ a ≡ c
trans (π A B B*) (f , f*) (g , g*) (h , h*) f-is-g g-is-h = λ x → trans (B x) (f x) (g x) (h x) (f-is-g x) (g-is-h x)

module Equational-Reasoning (A : U) where
  infix 2 ∵_
  ∵_ : ∀ a → A ∋ a ≡ a
  ∵ a = ref A a

  infixl 1 _≡_[_]
  _≡_[_] : ∀ {a} {b} → A ∋ a ≡ b → ∀ c → A ∋ b ≡ c → A ∋ a ≡ c
  δ ≡ c [ δ' ] = trans A _ _ c δ δ'

Id : ∀ A → A ≅ A
Id A = record { 
  iso = λ x → x; 
  inv = λ x → x;
  isowd = λ _ _ x-is-y → x-is-y;
  invwd = λ _ _ x-is-y → x-is-y;
  isoinv = λ x → ref A x; 
  inviso = λ x → ref A x }

_⁻¹ : ∀ {A} {B} → A ≅ B → B ≅ A
f ⁻¹ = record { 
  iso = _≅_.inv f; 
  inv = _≅_.iso f;
  isowd = _≅_.invwd f;
  invwd = _≅_.isowd f;
  isoinv = _≅_.inviso f; 
  inviso = _≅_.isoinv f }

_∘_ : ∀ {A} {B} {C} → B ≅ C → A ≅ B → A ≅ C
_∘_ {A} {B} {C} g f = record { 
  iso = λ x → _≅_.iso g (_≅_.iso f x); 
  inv = λ x → _≅_.inv f (_≅_.inv g x); 
  isowd = λ x y x-is-y → _≅_.isowd g (_≅_.iso f x) (_≅_.iso f y) (_≅_.isowd f x y x-is-y);
  invwd = λ x y x-is-y → _≅_.invwd f (_≅_.inv g x) (_≅_.inv g y) (_≅_.invwd g x y x-is-y);
  isoinv = λ y → let open Equational-Reasoning C in 
    ∵ _≅_.iso g (_≅_.iso f (_≅_.inv f (_≅_.inv g y)))
    ≡ _≅_.iso g (_≅_.inv g y)                          [ _≅_.isowd g _ (_≅_.inv g y) (_≅_.isoinv f _) ]
    ≡ y                                                [ _≅_.isoinv g y ]; 
  inviso = λ x → let open Equational-Reasoning A in 
    ∵ _≅_.inv f (_≅_.inv g (_≅_.iso g (_≅_.iso f x)))
    ≡ _≅_.inv f (_≅_.iso f x)                          [ _≅_.invwd f _ (_≅_.iso f x) (_≅_.inviso g _) ]
    ≡ x                                                [ _≅_.inviso f x ] }

_∼〈_〉_ : ∀ {A} {B} → T A → A ≅ B → T B → Set
_∼〈_〉_ {A} {B} a e b = B ∋ _≅_.iso e a ≡ b

π-wd : ∀ {A} {A'} (A* : A ≅ A') {B} {B'} {Bwd} {B'wd} (B* : ∀ x y → x ∼〈 A* 〉 y → B x ≅ B' y) → π A B Bwd ≅ π A' B' B'wd
π-wd {A} {A'} A* {B} {B'} {Bwd} {B'wd} B* = record {
  iso = λ f → (λ a' → _≅_.iso (B* (_≅_.inv A* a') a' (_≅_.isoinv A* a')) (proj₁ f (_≅_.inv A* a'))) , 
    {!!};
                                              inv = {!!};
                                              isowd = {!!};
                                              invwd = {!!};
                                              isoinv = {!!};
                                              inviso = {!!} }
