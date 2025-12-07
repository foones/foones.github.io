open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≰⇒≥)
open import Relation.Binary.PropositionalEquality
      using (_≡_; refl; sym; trans; cong)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infix  3 _~_
infixr 3 _~⟨_⟩_
infix  4 _~∎
infix  3 _≤*_

----------

record OrdenDecidible (A : Set) : Set₁ where
  field
    _<=_ : A → A → Set
    <=-refl    : {a : A} → a <= a
    <=-antisym : {a b : A} → a <= b → b <= a → a ≡ b
    <=-trans   : {a b c : A} → a <= b → b <= c → a <= c
    _<=?_      : (a b : A) → Dec (a <= b)
open OrdenDecidible

ℕ-orden : OrdenDecidible ℕ
_<=_       ℕ-orden = _≤_
<=-refl    ℕ-orden = ≤-refl
<=-antisym ℕ-orden = ≤-antisym
<=-trans   ℕ-orden = ≤-trans
_<=?_      ℕ-orden = _≤?_

----------

insertG : {A : Set} → OrdenDecidible A → A → List A → List A
insertG o x []       = x ∷ []
insertG o x (y ∷ ys) with _<=?_ o x y
... | yes _ = x ∷ y ∷ ys
... | no  _ = y ∷ insertG o x ys

insertion-sortG : {A : Set} → OrdenDecidible A → List A → List A
insertion-sortG o []       = []
insertion-sortG o (x ∷ xs) = insertG o x (insertion-sortG o xs)

----------

insert : ℕ → List ℕ → List ℕ
insert x []       = x ∷ []
insert x (y ∷ ys) with x ≤? y
... | yes _ = x ∷ y ∷ ys
... | no  _ = y ∷ insert x ys

insertion-sort : List ℕ → List ℕ
insertion-sort []       = []
insertion-sort (x ∷ xs) = insert x (insertion-sort xs)

-- Vamos a querer probar que insertion-sort devuelve
-- una permutación ordenada de su entrada.

---- Permuta ----

data _~_ : List ℕ → List ℕ → Set where
  ~-refl : {xs : List ℕ} → xs ~ xs
  ~-dip  : {x : ℕ} {xs ys : List ℕ}
         → xs ~ ys
         → x ∷ xs ~ x ∷ ys
  ~-swap : {x y : ℕ} {xs ys : List ℕ}
         → xs ~ ys
         → x ∷ y ∷ xs ~ y ∷ x ∷ ys
  ~-trans : {xs ys zs : List ℕ}
          → xs ~ ys
          → ys ~ zs
          → xs ~ zs

_~⟨_⟩_ : (xs : List ℕ)
       → {ys : List ℕ} → xs ~ ys
       → {zs : List ℕ} → ys ~ zs
       → xs ~ zs
_ ~⟨ p ⟩ q = ~-trans p q

_~∎ : (xs : List ℕ) → xs ~ xs
_ ~∎ = ~-refl

insert-permuta : {x : ℕ} {ys : List ℕ}
               → insert x ys ~ x ∷ ys
insert-permuta {x} {[]}     = ~-refl
insert-permuta {x} {y ∷ ys} with x ≤? y
... | yes p = ~-refl
... | no  p =
    y ∷ insert x ys
  ~⟨ ~-dip insert-permuta ⟩
    y ∷ x ∷ ys
  ~⟨ ~-swap ~-refl ⟩
    x ∷ y ∷ ys
  ~∎

insertion-sort-permuta : {xs : List ℕ}
                       → insertion-sort xs ~ xs
insertion-sort-permuta {[]}     = ~-refl
insertion-sort-permuta {x ∷ xs} =
    insert x (insertion-sort xs)
  ~⟨ insert-permuta ⟩
    x ∷ insertion-sort xs
  ~⟨ ~-dip insertion-sort-permuta ⟩
    x ∷ xs
  ~∎

---- Ordena ----

{-
-- Esta versión define la noción de lista ordenada
-- pero es difícil trabajar con ella.
--
data Ordenada : List ℕ → Set where
  o-nil       : Ordenada []
  o-singleton : {x : ℕ} → Ordenada (x ∷ [])
  o-cons      : {x y : ℕ} {xs : List ℕ}
              → x ≤ y
              → Ordenada (y ∷ xs)
              → Ordenada (x ∷ y ∷ xs)
-}

data _≤*_ : ℕ → List ℕ → Set where
  ≤*-[]  : {x : ℕ} → x ≤* []
  _≤*-∷_ : {x y : ℕ} {ys : List ℕ}
         → x ≤ y
         → x ≤* ys
         → x ≤* y ∷ ys

≤-≤*-trans : {x y : ℕ} {zs : List ℕ}
           → x ≤ y
           → y ≤* zs
           → x ≤* zs
≤-≤*-trans x≤y ≤*-[]            = ≤*-[]
≤-≤*-trans x≤y (y≤z ≤*-∷ y≤*zs) = (≤-trans x≤y y≤z)
                                  ≤*-∷ (≤-≤*-trans x≤y y≤*zs)

data Ordenada : List ℕ → Set where
  o-nil  : Ordenada []
  o-cons : {x : ℕ} {xs : List ℕ}
         → x ≤* xs
         → Ordenada xs
         → Ordenada (x ∷ xs)

insert-≤* : {x y : ℕ} {zs : List ℕ}
          → x ≤ y
          → x ≤* zs
          → x ≤* insert y zs
insert-≤* {x} {y} {[]}     x≤y x≤*zs = x≤y ≤*-∷ ≤*-[]
insert-≤* {x} {y} {z ∷ zs} x≤y (x≤z ≤*-∷ x≤*zs)
  with y ≤? z
... | yes y≤z = x≤y ≤*-∷ (x≤z ≤*-∷ x≤*zs)
... | no  _   = x≤z ≤*-∷ insert-≤* {x} {y} {zs} x≤y x≤*zs

insert-preserva-orden : {x : ℕ} {ys : List ℕ}
                      → Ordenada ys
                      → Ordenada (insert x ys)
insert-preserva-orden {x} {[]}     o-nil = o-cons ≤*-[] o-nil
insert-preserva-orden {x} {y ∷ ys} (o-cons y≤*ys ys-ord)
  with x ≤? y
...  | yes x≤y = o-cons (x≤y ≤*-∷ ≤-≤*-trans x≤y y≤*ys)
                        (o-cons y≤*ys ys-ord)
...  | no ¬x≤y = o-cons (insert-≤* (≰⇒≥ ¬x≤y) y≤*ys)
                        (insert-preserva-orden {x} {ys} ys-ord)

insertion-sort-ordena : {xs : List ℕ}
                      → Ordenada (insertion-sort xs)
insertion-sort-ordena {[]}     = o-nil
insertion-sort-ordena {x ∷ xs} =
  insert-preserva-orden (insertion-sort-ordena {xs})

----

insertion-sort-CC : (xs : List ℕ)
                  → Σ[ ys ∈ List ℕ ] (ys ~ xs) × Ordenada ys
insertion-sort-CC xs = insertion-sort xs
                     , insertion-sort-permuta
                     , insertion-sort-ordena {xs}

test = insertion-sort-CC (2 ∷ 1 ∷ [])
