open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_; Σ-syntax)

-- open import Relation.Binary.PropositionalEquality
--       using (_≡_; refl; sym; trans; cong)
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq.≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infix 60 _+_
infix 70 _*_

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m

uno    = suc zero
dos    = suc uno
tres   = suc dos
cuatro = suc tres

indℕ : (C : ℕ → Set)
     → C zero
     → ({n : ℕ} → C n → C (suc n))
     → (n : ℕ) → C n
indℕ C c0 cS zero    = c0
indℕ C c0 cS (suc n) = cS (indℕ C c0 cS n)

----

data _≡_ {A : Set} : (a b : A) → Set where
  refl : {a : A} → a ≡ a

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong _ refl = refl

infixr 20 _≡⟨_⟩_
infix  30 _∎

_≡⟨_⟩_ : {A : Set} (a : A) {b : A} (p : a ≡ b) {c : A} (q : b ≡ c)
       → a ≡ c
_ ≡⟨ p ⟩ q = trans p q

_∎ : {A : Set} (a : A) → a ≡ a
_ ∎ = refl

---- 

+-zero-right : {m : ℕ} → m + zero ≡ m
+-zero-right {zero}  = refl
+-zero-right {suc m} = cong suc (+-zero-right {m})

+-assoc : {n₁ n₂ n₃ : ℕ} → n₁ + (n₂ + n₃) ≡ (n₁ + n₂) + n₃
+-assoc {zero} {n₂} {n₃} =
    zero + (n₂ + n₃)
  ≡⟨ refl ⟩
    n₂ + n₃
  ≡⟨ refl ⟩
    (zero + n₂) + n₃
  ∎
+-assoc {suc n₁} = cong suc (+-assoc {n₁})

_≤_ : ℕ → ℕ → Set
n ≤ m = Σ[ k ∈ ℕ ] (k + n ≡ m)

≤-refl : {n : ℕ} → n ≤ n
≤-refl = zero , refl

≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans {a} {b} {c} (k₁ , p₁) (k₂ , p₂) =
  (k₂ + k₁) ,
  (  (k₂ + k₁) + a
    ≡⟨ sym (+-assoc {k₂}) ⟩
      k₂ + (k₁ + a)
    ≡⟨ cong (_+_ k₂) p₁ ⟩
      k₂ + b
    ≡⟨ p₂ ⟩
      c
    ∎)

_≤?_ : ℕ → ℕ → Bool
zero  ≤? m     = true
suc n ≤? zero  = false
suc n ≤? suc m = n ≤? m

≤?-correcto : {n m : ℕ} → (n ≤? m) ≡ true
                        → n ≤ m
≤?-correcto {zero}  {m}     _ = m , +-zero-right
≤?-correcto {suc n} {zero}  ()
≤?-correcto {suc n} {suc m} p with ≤?-correcto {n} {m} p
... | (k , k+n≡m) = k , {!!}


data ⊤ : Set where
  tt : ⊤
