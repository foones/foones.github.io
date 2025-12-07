
----
---- Práctica 5: Programas correctos por construcción
----

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_)
open import Data.Nat.Properties using (≤-step; ≤-refl; ≤-trans; +-monoʳ-≤)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- Recordemos la definición de algunas funciones básicas sobre listas:

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

---- Parte A ----

-- A.1) Demostrar que dada una lista xs y un entero k ≤ length xs,
-- es posible partir la lista xs en un prefijo ys de longitud k
-- seguido de un sufijo zs.

split : {A : Set} (xs : List A) (k : ℕ)
      → k ≤ length xs
      → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] ((xs ≡ ys ++ zs) × k ≡ length ys)
split = {!!}

-- Definimos un predicado "x ∈ ys" que es verdadero si x aparece en ys:

data _∈_ : ℕ → List ℕ → Set where
  zero : {x : ℕ} {xs : List ℕ} → x ∈ (x ∷ xs)
  suc  : {x y : ℕ} {xs : List ℕ} → x ∈ xs → x ∈ (y ∷ xs)

-- A.2) Demostrar que es posible decidir si un número natural aparece en una lista.
-- (Usar _≟_ para decidir la igualdad de números naturales).

∈-decidible : {x : ℕ} {ys : List ℕ} → Dec (x ∈ ys)
∈-decidible = {!!}

-- A.3) Demostrar que la igualdad de listas es decidible
-- asumiendo que es decidible la igualdad de sus elementos.

List-igualdad-decidible : {A : Set}
                        → ((x y : A) → Dec (x ≡ y))
                        → ((xs ys : List A) → Dec (xs ≡ ys))
List-igualdad-decidible dec-eq-A xs ys = {!!}

---- Parte B ----

infix  3 _~_
infix  3 _<<_
infixr 3 _~⟨_⟩_
infix  4 _~∎

-- Considerar el siguiente tipo de las permutaciones:

data _~_ : List ℕ → List ℕ → Set where
  ~-empty : [] ~ []
  ~-cons  : {x : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ xs ~ x ∷ ys
  ~-swap  : {x y : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ y ∷ xs ~ y ∷ x ∷ ys
  ~-trans : {xs ys zs : List ℕ}
          → xs ~ ys
          → ys ~ zs
          → xs ~ zs

-- B.1) Demostrar que "~" es reflexiva:

~-refl : {xs : List ℕ} → xs ~ xs
~-refl = {!!}

-- Definimos operadores auxiliares para poder hacer razonamiento ecuacional
-- con permutaciones:

_~⟨_⟩_ : (xs : List ℕ)
       → {ys : List ℕ} → xs ~ ys
       → {zs : List ℕ} → ys ~ zs
       → xs ~ zs
_ ~⟨ p ⟩ q = ~-trans p q

_~∎ : (xs : List ℕ) → xs ~ xs
_ ~∎ = ~-refl

-- B.2) Demostrar que "~" es simétrica:

~-sym : {xs ys : List ℕ} → xs ~ ys → ys ~ xs
~-sym ~-empty       = {!!}
~-sym (~-cons p)    = {!!}
~-sym (~-swap p)    = {!!}
~-sym (~-trans p q) = {!!}

-- B.3) Demostrar que "~" es una congruencia con respecto a la concatenación de listas:

~-++ : {xs ys xs' ys' : List ℕ}
     → xs ~ xs'
     → ys ~ ys'
     → xs ++ ys ~ xs' ++ ys'
~-++ p q = {!!}

-- B.4) Demostrar que una lista invertida es permutación de la lista original:

~-reverse : {xs : List ℕ} → reverse xs ~ xs
~-reverse {[]}     = ~-empty
~-reverse {x ∷ xs} =
    reverse (x ∷ xs)
  ~⟨ ~-refl ⟩
    reverse xs ++ (x ∷ [])
  ~⟨ {!!} ⟩
    xs ++ (x ∷ [])
  ~⟨ {!!} ⟩
    x ∷ xs
  ~∎

----

-- Definimos una función que vale 1 si dos números son iguales, y 0 si no.
iguales? : ℕ → ℕ → ℕ
iguales? x y with x ≟ y
... | yes _ = 1
... | no  _ = 0

-- Definimos una función que cuenta el número de apariciones de un
-- número natural en una lista.
cantidad-apariciones : ℕ → List ℕ → ℕ
cantidad-apariciones x []       = zero
cantidad-apariciones x (y ∷ ys) = iguales? x y + cantidad-apariciones x ys

-- Definimos un predicado xs << ys
-- que es verdadero si cada natural z
-- aparece en xs a lo sumo tantas veces como aparece en ys:

_<<_ : List ℕ → List ℕ → Set
xs << ys = (z : ℕ) → cantidad-apariciones z xs ≤ cantidad-apariciones z ys

-- B.5) Demostrar las siguientes propiedades de "<<":

<<-empty : [] << []
<<-empty = {!!}

<<-refl : {xs : List ℕ} → xs << xs
<<-refl z = {!!}    -- útil: Data.Nat.Properties.≤-refl 

<<-cons : {x : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ xs << x ∷ ys
<<-cons {x} xs<<ys z = {!!}    -- útil:   +-monoʳ-≤ (iguales? z x) ?

<<-swap : {x y : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ y ∷ xs << y ∷ x ∷ ys
<<-swap xs<<ys z = {!!}    -- útil: Data.Nat.Properties.+-monoʳ-≤

<<-trans : {xs ys zs : List ℕ} → xs << ys → ys << zs → xs << zs
<<-trans xs<<ys ys<<zs z = {!!}    -- útil: Data.Nat.Properties.≤-trans

-- B.6) Usando los lemas de B.5, demostrar que la relación "~" es
-- correcta con respecto a "<<".

~-correcta : {xs ys : List ℕ}
           → xs ~ ys 
           → xs << ys 
~-correcta ~-empty       = {!!}
~-correcta (~-cons p)    = {!!}
~-correcta (~-swap p)    = {!!}
~-correcta (~-trans p q) = {!!}
