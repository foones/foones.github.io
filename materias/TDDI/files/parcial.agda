open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

infix  4 _~_
infixl 5 _U_
infixl 6 _∙_
infix  7 _*

-- El siguiente tipo de datos sirve para representar palabras en el alfabeto {0, 1}.
-- Por ejemplo, cons1 (cons1 (cons0 [])) represnta la cadena "110".
data Word : Set where
  []    : Word
  cons0 : Word → Word
  cons1 : Word → Word

-- Concatenación de palabras:
_++_ : Word -> Word -> Word
[]       ++ w2 = w2
cons0 w1 ++ w2 = cons0 (w1 ++ w2)
cons1 w1 ++ w2 = cons1 (w1 ++ w2)

-- El siguiente tipo de datos sirve para representar expresiones regulares en el alfabeto {0, 1}.
-- [Nota: el símbolo "∙" típicamente se puede ingresar tecleando "\."].
data RE : Set where
  ∅    : RE            -- Denota el lenguaje vacío.
  m[]  : RE            -- Denota el lenguaje que tiene sólo a la cadena vacía.
  m0   : RE            -- Denota el lenguaje que tiene sólo a la cadena "0".
  m1   : RE            -- Denota el lenguaje que tiene sólo a la cadena "1".
  _U_  : RE → RE → RE  -- (R U S) denota la unión de los lenguajes denotados por R y S.
  _∙_  : RE → RE → RE  -- (R ∙ S) denota la concatenación de los lenguajes denotados por R y S.
  _*   : RE → RE       -- (R *) denota la clausura de Kleene del lenguaje denotado por R.

-- El predicado (Match R w) está habitado cuando w está en el lenguaje denotado por R.
data Match : RE → Word → Set where
  Match-[] : Match m[] []
  Match-0  : Match m0 (cons0 [])
  Match-1  : Match m1 (cons1 [])
  Match-U1 : {R S : RE} {w : Word}
           → Match R w
           → Match (R U S) w
  Match-U2 : {R S : RE} {w : Word}
           → Match S w
           → Match (R U S) w
  Match-∙  : {R S : RE} {w1 w2 : Word}
           → Match R w1
           → Match S w2
           → Match (R ∙ S) (w1 ++ w2)
  Match-*1 : {R : RE} → Match (R *) []
  Match-*2 : {R : RE} {w1 w2 : Word}
           → Match R w1
           → Match (R *) w2
           → Match (R *) (w1 ++ w2)

---

-- Ejercicio 1: demostrar que la expresión regular (m0 U m1)* matchea a cualquier palabra.
-- Sugerencia: proceder por inducción en w.
lenguaje-completo : {w : Word} → Match ((m0 U m1) *) w
lenguaje-completo {w} = ?

---

-- Decimos que dos expresiones regulares son equivalentes si denotan el mismo lenguaje,
-- es decir, matchean las mismas palabras.
_~_ : RE → RE → Set
R ~ S = (w : Word) → ((Match R w → Match S w) × (Match S w → Match R w))

-- Ejercicio 2: demostrar que _~_ es una relación de equivalencia.

~-refl : {R : RE} → R ~ R
~-refl w = ?
         , ?

~-sym : {R S : RE} → R ~ S → S ~ R
~-sym = ?

~-trans : {R S T : RE} → R ~ S → S ~ T → R ~ T
~-trans = ?

----

-- Ejercicio 3: demostrar que la unión es conmutativa y asociativa
-- y que el vacío es el elemento neutro.

U-comm : {R S : RE} → R U S ~ S U R
U-comm w = (λ { (Match-U1 p) → {! !}
              ; (Match-U2 p) → {! !}
              })
         , ?

U-assoc : {R S T : RE} → (R U S) U T ~ R U (S U T)
U-assoc = ?

U-neut : {R : RE} → R U ∅ ~ R
U-neut w = ?

----

-- Ejercicio 4: demostrar que la concatenación es asociativa
-- y que el lenguaje que incluye sólo a la palabra vacía es el elemento neutro.
-- Para hacer este ejercicio puede ser necesario probar lemas auxiliares
-- sobre la concatenación de palabras y usar transportes.

∙-assoc : {R S T : RE} → (R ∙ S) ∙ T ~ R ∙ (S ∙ T)
∙-assoc = ?

∙-neut : {R : RE} → R ∙ m[] ~ R
∙-neut = ?

----

-- La siguiente operación invierte una palabra.
reverse : Word → Word
reverse []        = []
reverse (cons0 w) = reverse w ++ cons0 []
reverse (cons1 w) = reverse w ++ cons1 []

-- Ejercicio 5: definir una expresión regular que reconozca el reverso del lenguaje original,
-- es decir, vale (Match R w) si y sólo si vale (Match (rev R) (reverse w))
rev : RE → RE
rev ∅       = ?
rev m[]     = ?
rev m0      = ?
rev m1      = ?
rev (R U S) = rev R U rev S
rev (R ∙ S) = ?
rev (R *)   = ?

-- Ejercicio 6: demostrar que el lenguaje de (rev R) incluye el reverso de todas las palabras de R.
-- Sugerencia: proceder por inducción en la derivación de (Match R w).
-- Para hacer este ejercicio puede ser necesario probar lemas auxiliares sobre palabras
-- y usar transportes.
match-rev : {R : RE} {w : Word} → Match R w → Match (rev R) (reverse w)
match-rev Match-[]       = ?
match-rev Match-0        = ?
match-rev Match-1        = ?
match-rev (Match-U1 p)   = Match-U1 (match-rev p)
match-rev (Match-U2 p)   = ?
match-rev (Match-∙ p q)  = ?
match-rev Match-*1       = ?
match-rev (Match-*2 p q) = {! !}

