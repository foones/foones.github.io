
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

{-
postulate Nat : Set

postulate zero : Nat

postulate suc : Nat -> Nat

postulate EsPar : Nat -> Set

postulate ParZ : EsPar zero

postulate ParS : {n : Nat} -> EsPar n -> EsPar (suc (suc n))

el-4-es-par : EsPar (suc (suc (suc (suc zero))))
el-4-es-par = ParS (ParS ParZ)
-}

data Bool : Set where
  false : Bool
  true  : Bool

indBool : (C : Bool → Set) → C false → C true → (b : Bool) → C b
indBool C cFalse cTrue false = cFalse
indBool C cFalse cTrue true  = cTrue

not : Bool → Bool
not = indBool C cFalse cTrue
  where
     C : Bool → Set
     C = λ _ → Bool
     cTrue = true
     cFalse = false

infixr 80 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-length : {A : Set} {xs ys : List A}
          → length (xs ++ ys) ≡ length xs + length ys
++-length {xs = []}     = refl
++-length {xs = _ ∷ xs} = cong suc (++-length {xs = xs})

{-
-- open import Data.Product using (_×_; _,_)
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

π₁ : {A B : Set} → A × B → A
π₁ (a , _) = a

π₂ : {A B : Set} → A × B → B
π₂ (_ , b) = b

×-assoc-right : {A B C : Set} → (A × B) × C → A × (B × C)
-- ×-assoc-right ((x , y) , z) = x , (y , z)
-- ×-assoc-right p = π₁ (π₁ p) , (π₂ (π₁ p) , π₂ p)
-- ×-assoc-right = λ p → π₁ (π₁ p) , (π₂ (π₁ p) , π₂ p)
×-assoc-right = λ { ((x , y) , z) → x , (y , z) }

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

×+-distr : {A B C : Set} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
×+-distr (a , inj₁ b) = inj₁ (a , b)
×+-distr (a , inj₂ c) = inj₂ (a , c)
-}

data Sig (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Sig A B

postulate esPrimo : ℕ → Set
postulate esPrimoElDos : esPrimo (suc (suc zero))
postulate esPrimoElTres : esPrimo (suc (suc (suc zero)))

Primo : Set
Primo = Sig ℕ esPrimo

dosComoPrimo : Primo
dosComoPrimo = suc (suc zero) , esPrimoElDos
