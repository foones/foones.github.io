open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
  
data _⊎_ (A B : Set) : Set where
  in₁ : A → A ⊎ B
  in₂ : B → A ⊎ B

cong-in₁ : {A B : Set} {a a' : A}
         → a ≡ a' → in₁ {_} {B} a ≡ in₁ a'
cong-in₁ refl = refl

no-confusion : {A B : Set} {a : A} {b : B}
             → in₁ a ≡ in₂ b
             → ⊥
no-confusion ()

----

transport : {A : Set} (B : A → Set) {a a' : A} (p : a ≡ a')
          → B a → B a'
transport _ refl x = x

----

record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : (a : A) → from (to a) ≡ a
    to∘from : (b : B) → to (from b) ≡ b
open _≃_

code : {A B : Set} (a0 : A) → A ⊎ B → Set
code a0 (in₁ a) = (a0 ≡ a)
code a0 (in₂ b) = ⊥

{-
transport (code a0) : {z z' : A ⊎ B} → (z ≡ z') → code z → code z'
-}

caracterizacion-de-in₁ :
               {A B : Set} {a0 : A} {z : A ⊎ B}
             → (in₁ a0 ≡ z) ≃ (code a0 z)
to (caracterizacion-de-in₁ {A} {B} {a0} {z}) p =
  transport (code a0) p refl
from (caracterizacion-de-in₁ {A} {B} {a0} {in₁ x}) q =
  cong in₁ q
from (caracterizacion-de-in₁ {A} {B} {a0} {in₂ x}) q =
  ⊥-elim q
from∘to (caracterizacion-de-in₁ {A} {B} {a0} {z}) refl =
  refl
to∘from (caracterizacion-de-in₁ {A} {B} {a0} {in₁ x}) refl =
  refl
to∘from (caracterizacion-de-in₁ {A} {B} {a0} {in₂ x}) q =
  ⊥-elim q


---------

data _≤_ : ℕ → ℕ → Set where
  z≤* : {n : ℕ} → zero ≤ n
  s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

dos-menor-o-igual-que-tres : suc (suc zero) ≤ suc (suc (suc zero))
dos-menor-o-igual-que-tres = s≤s (s≤s z≤*)

≤-trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
≤-trans z≤*     _       = z≤*
≤-trans (s≤s a) (s≤s b) = s≤s (≤-trans a b)
 
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

_≤?_ : (n : ℕ) (m : ℕ) → Dec (n ≤ m)
zero  ≤? _    = yes z≤*
suc n ≤? zero = no λ ()
suc n ≤? suc m with n ≤? m
... | yes p = yes (s≤s p)
... | no  p = no λ { (s≤s q) → p q }

-- Árbol Binario de Búsqueda

data AB : Set where
  nil : AB
  bin : AB → ℕ → AB → AB

insertar : ℕ → AB → AB
insertar n nil         = bin nil n nil
insertar n (bin i r d)
  with n ≤? r
... | yes p = bin (insertar n i) r d
... | no  p = bin i r (insertar n d)

data _∈_ : ℕ → AB → Set where
  ∈-raiz : ∀ {i r d}
           → r ∈ bin i r d
  ∈-izq  : ∀ {x i r d}
           → x ∈ i
           → x ∈ bin i r d
  ∈-der  : ∀ {x i r d}
           → x ∈ d
           → x ∈ bin i r d

data EsABB : AB → Set where
  abb-nil : EsABB nil
  abb-bin : ∀ {i r d}
          → EsABB i
          → EsABB d
          → (∀ x → x ∈ i → x ≤ r)
          → (∀ x → x ∈ d → ¬(x ≤ r))
          → EsABB (bin i r d)

insertar-prop :
  ∀ {P : ℕ → Set} {x a}
  → P x
  → (∀ y → y ∈ a → P y)
  → (∀ y → y ∈ insertar x a → P y)
insertar-prop {P} {_} {nil} x≤M a≤M y ∈-raiz = x≤M
insertar-prop {P} {x} {bin i r d} Px Pa y
  with x ≤? r
... | yes p =
      λ {
        ∈-raiz      → Pa r ∈-raiz
      ; (∈-izq y∈i) → insertar-prop Px
                                    (λ z z∈i → Pa z (∈-izq z∈i))
                                    y
                                    y∈i
      ; (∈-der y∈d) → Pa y (∈-der y∈d)
      }
... | no p  =
      λ {
        ∈-raiz      → Pa r ∈-raiz
      ; (∈-izq y∈i) → Pa y (∈-izq y∈i)
      ; (∈-der y∈d) → insertar-prop Px
                                    (λ z z∈d → Pa z (∈-der z∈d))
                                    y
                                    y∈d
      }

insertar-preserva-invariante :
  ∀ {x a}
  → EsABB a
  → EsABB (insertar x a)
insertar-preserva-invariante
  abb-nil = abb-bin abb-nil abb-nil (λ _ ()) (λ _ ())
insertar-preserva-invariante {x}
  (abb-bin {i} {r} {d} abb-izq abb-der izq≤raiz der>raiz)
  with x ≤? r
... | yes x≤r = abb-bin (insertar-preserva-invariante abb-izq)
                        abb-der
                        (insertar-prop x≤r izq≤raiz)
                        der>raiz
... | no x>r  = abb-bin abb-izq
                        (insertar-preserva-invariante abb-der)
                        izq≤raiz
                        (insertar-prop x>r der>raiz)

