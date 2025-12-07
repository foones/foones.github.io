
----
---- Práctica 3: Estructura de ω-grupoide y transporte
----

open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
       using (+-comm)
open import Data.Product
       using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

---- Parte A ----

-- Considerar las siguientes definiciones de la composición de caminos (transitividad)
-- e inversa de un camino (simetría). Son equivalentes a sym y trans pero cambiando
-- la notación.

_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

-- A.1) Demostrar que la reflexividad es el neutro de la composición de caminos
-- a izquierda y a derecha.

∙-refl-left : {A : Set} {x y : A} {p : x ≡ y}
            → refl ∙ p ≡ p
∙-refl-left = {!!}

∙-refl-right : {A : Set} {x y : A} {p : x ≡ y}
             → p ∙ refl ≡ p
∙-refl-right = {!!}

-- A.2) Demostrar que la composición de caminos es asociativa.

∙-assoc : {A : Set} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
        → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc = {!!}

-- A.3) Demostrar que la inversa es efectivamente la inversa, a izquierda y a derecha.

∙-⁻¹-left : {A : Set} {x y : A} {p : x ≡ y}
            → (p ⁻¹) ∙ p ≡ refl
∙-⁻¹-left = {!!}

∙-⁻¹-right : {A : Set} {x y : A} {p : x ≡ y}
            → p ∙ (p ⁻¹) ≡ refl
∙-⁻¹-right = {!!}

-- A.4) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- completar la demostración de que la inversa es involutiva:

⁻¹-involutive : {A : Set} {x y : A} {p : x ≡ y}
              → (p ⁻¹) ⁻¹ ≡ p
⁻¹-involutive {A} {x} {y} {p} =
    (p ⁻¹) ⁻¹
  ≡⟨ {!!} ⟩
    ((p ⁻¹) ⁻¹) ∙ refl
  ≡⟨ {!!} ⟩
    ((p ⁻¹) ⁻¹) ∙ ((p ⁻¹) ∙ p)
  ≡⟨ {!!} ⟩
    (((p ⁻¹) ⁻¹) ∙ (p ⁻¹)) ∙ p
  ≡⟨ {!!} ⟩
    refl ∙ p
  ≡⟨ {!!} ⟩
    p
  ∎

-- A.5) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar las siguientes propiedades de cancelación a izquierda y a derecha:

∙-cancel-left : {A : Set} {x y z : A} {p : x ≡ y} {q q' : y ≡ z}
             → p ∙ q ≡ p ∙ q'
             → q ≡ q'
∙-cancel-left {A} {x} {y} {z} {p} {q} {q'} pq≡pq' =
  begin
    q
  ≡⟨ {!!} ⟩
    ((p ⁻¹) ∙ p) ∙ q      -- (ayuda)
  ≡⟨ {!!} ⟩
    q'
  ∎

∙-cancel-right : {A : Set} {x y z : A} {p p' : x ≡ y} {q : y ≡ z}
               → p ∙ q ≡ p' ∙ q
               → p ≡ p'
∙-cancel-right = {!!}

-- A.6) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar las siguientes propiedades, que caracterizan a la inversa a izquierda y
-- a derecha:

⁻¹-univ-left : {A : Set} {x y : A} {p : x ≡ y} {q : y ≡ x}
             → p ∙ q ≡ refl
             → p ≡ q ⁻¹
⁻¹-univ-left = {!!}

⁻¹-univ-right : {A : Set} {x y : A} {p : x ≡ y} {q : y ≡ x}
              → p ∙ q ≡ refl
              → q ≡ p ⁻¹
⁻¹-univ-right = {!!}

-- A.7) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar la siguiente propiedad de conmutación entre la composición de caminos y
-- la inversa:

∙-⁻¹-comm : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ z}
             → (p ∙ q)⁻¹ ≡ (q ⁻¹) ∙ (p ⁻¹)
∙-⁻¹-comm = {!!}

---- Parte B ----

-- Usamos los booleanos para representar bits (false = 0 ; true = 1).
-- Consideramos la siguiente función auxiliar:
_+bit_ : Bool → ℕ → ℕ
false +bit n = n
true  +bit n = suc n

-- Consideramos el siguiente tipo de datos para codificar naturales en binario:
data Bin : Set where
  binzero : Bin
  addbit  : Bin → Bool → Bin

-- Donde:
-- ─ b0 representa el 0
-- ─ Si x : Bin, entonces addbit x b es el número que resulta de agregar el bit b a la derecha
--   (es decir, "b +bit (2 * x)").
-- Por ejemplo,
--   addbit (addbit (addbit binzero true) false) false
-- codifica el número (100)₂ = 4.

-- B.1) Definir la función que convierte un número representado en binario a natural:
bin2nat : Bin → ℕ
bin2nat binzero      = {!!}
bin2nat (addbit x b) = {!!}

-- B.2) Definir la función sucesor sobre números naturales representados en binario:
binsuc : Bin → Bin
binsuc binzero          = {!!}
binsuc (addbit x false) = {!!}
binsuc (addbit x true)  = {!!}

-- B.3) Usando binsuc, definir la función que convierte un número natural a su representación binaria:
nat2bin : ℕ → Bin
nat2bin = {!!}

-- B.4) Demostrar que bin2nat es la inversa a izquierda de nat2bin:
nat2bin2nat : (n : ℕ) → bin2nat (nat2bin n) ≡ n
nat2bin2nat = {!!}

-- B.5) Definir la siguiente función, que descompone un número natural en su cociente y su resto
-- en la división por 2:
divmod2 : (n : ℕ) → Σ[ q ∈ ℕ ] Σ[ r ∈ Bool ] n ≡ r +bit (q + q)
divmod2 zero          = {!!}
divmod2 (suc zero)    = {!!}
divmod2 (suc (suc n)) = let (q' , r' , n≡q+q+r') = divmod2 n in
                          {!!}

---- Parte C ----

-- Recordemos el operador de transporte:
transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport _ refl b = b

-- C.1) Demostrar que transportar por la familia (B ∘ f) vía el camino p
-- equivale a transportar por la familia B vía el camino (cong f p).
transport-compose : {A A' : Set} (f : A → A') (B : A' → Set) {x y : A} (p : x ≡ y) (b : B (f x))
           → transport (λ x → B (f x)) p b ≡ transport B (cong f p) b
transport-compose = {!!}

-- C.2) Demostrar que transportar vía la composición de dos caminos
-- equivale a transportar separadamente vía cada uno de ellos.
transport-∙ : {A : Set} (B : A → Set) {x y z : A} (p : x ≡ y) (q : y ≡ z) (b : B x)
           → transport B (p ∙ q) b ≡ transport B q (transport B p b)
transport-∙ = {!!}

-- C.3) Demostrar que transportar por una familia constante es la identidad.
transport-const : {A : Set} (B₀ : Set) {x y : A} (p : x ≡ y) (b : B₀)
                → transport (λ _ → B₀) p b ≡ b
transport-const = {!!}

-- C.4) Demostrar que transportar por una familia de caminos corresponde a componer: 
transport-path-left : {A : Set} {x y z : A} (p : x ≡ y) (q : x ≡ z)
                    → transport (λ a → a ≡ z) p q ≡ (p ⁻¹) ∙ q
transport-path-left = {!!}

-- C.5) Similar pero con la composición a derecha:
transport-path-right : {A : Set} {x y z : A} (p : x ≡ y) (q : z ≡ x)
                     → transport (λ a → z ≡ a) p q ≡ q ∙ p
transport-path-right = {!!}

---- Parte D ----

-- Definimos una familia `Fin n` indexada por `n : ℕ`.
-- Informalmente, `Fin n` es el tipo finito cuyos elementos son {0, 1, ..., n}.
data Fin : (n : ℕ) → Set where
  -- finZero es el único habitante de Fin 1
  finZero : Fin zero
  -- Si x es un habitante de Fin n,
  -- entonces finSuc x es un habitante de Fin (suc n).
  finSucc  : {n : ℕ} → Fin n → Fin (suc n)

-- D.1) Definir la suma:
sumaFin : {n m : ℕ} → Fin n → Fin m → Fin (n + m)
sumaFin finZero     y = {!!}
sumaFin (finSucc x) y = {!!}

-- D.2) Demostrar que la suma es conmutativa:
sumaFin-comm : {n m : ℕ} (x : Fin n) (y : Fin m) → sumaFin x y ≡ transport Fin (+-comm m n) (sumaFin y x)
sumaFin-comm = {!!}
