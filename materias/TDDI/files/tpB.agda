
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≟_; _≤_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- El objetivo de esta parte del TP es definir un pequeño lenguaje
-- imperativo, dar su semántica con triplas de Hoare y probar la
-- corrección parcial de pequeños programas imperativos.

-- Declaramos algunos operadores:
infix  40 _<<_>>_
infixr 60 _AND_
infixr 60 _&_
infix  70 _:=_
infix  70 WHILE_DO_

IsZero : ℕ → Set
IsZero n = n ≡ zero

NonZero : ℕ → Set
NonZero n = ¬ IsZero n

-------------------------------------------------------------------------------

---- Sintaxis de los programas y trazas de ejecución ----

-- Los programas usan variables cuyos nombres son identificadores.
-- Un <identificador> es un número natural.
Id : Set
Id = ℕ

-- El estado de la memoria es una lista de números naturales.
Memoria : Set
Memoria = List ℕ

-- Si M es una memoria, (valor M x) es el valor que le otorga
-- M a la variable x.
-- Si la memoria es una lista de la forma v(0) ∷ ... ∷ v(n-1) ∷ [],
-- le otorga el valor v(i) a cada variable i cuando 0 ≤ i < n
-- y le otorga el valor 0 a cualquier otra variable.
valor : Memoria → Id → ℕ
valor []      _       = zero
valor (v ∷ _) zero    = v
valor (_ ∷ M) (suc x) = valor M x

-- Si M es una memoria, (almacenar M x vx) es la memoria
-- que resulta de sobreescribir el valor del identificador x
-- con el valor vx indicado.
-- Si la variable excede las dimensiones de la memoria,
-- la memoria no se ve modificada.
almacenar : Memoria → Id → ℕ → Memoria
almacenar []      _       _  = []
almacenar (_ ∷ M) zero    vx = vx ∷ M
almacenar (v ∷ M) (suc x) vx = v ∷ almacenar M x vx

-- Una <expresión> puede ser:
-- - Una constante numérica.
-- - Una variable.
-- - Una función unaria aplicada a una expresión.
-- - Una función binaria aplicada a una expresión.
data Expr : Set where
  e-const   : ℕ → Expr
  e-var     : Id → Expr
  e-unaria  : (ℕ → ℕ) → Expr → Expr
  e-binaria : (ℕ → ℕ → ℕ) → Expr → Expr → Expr

-- Una expresión se puede evaluar en un estado de la memoria,
-- lo que da lugar a un número natural.
--
-- [Ejercicio 1]
-- Completar la función que evalúa una expresión.
--
evaluar : Memoria → Expr → ℕ
evaluar M (e-const c)         = {!!}
evaluar M (e-var x)           = {!!}
evaluar M (e-unaria f e)      = {!!}
evaluar M (e-binaria f e₁ e₂) = {!!}

-- Un <programa> imperativo puede ser:
--
-- - Una asignación, de la forma <identificador> := <expresión>.
--   Su semántica informal consiste en evaluar la expresión hasta
--   arrojar un número natural n y actualizar el estado de la memoria
--   modificando el valor de la variable, para asociarla al número n.
--
-- - La composición secuencial de dos programas.
--   Es de la forma <programa1> & <programa2>.
--   Su semántica informal consiste en evaluar el primer programa
--   hasta terminar, y a continuación evaluar el segundo programa.
--
-- - Un ciclo, de la forma WHILE <expresión> DO <programa>.
--   Su semántica informal consiste en evaluar el "bloque" mientras
--   la condición sea un número natural distinto de 0.
--
data Programa : Set where
  _:=_      : Id → Expr → Programa
  _&_       : Programa → Programa → Programa
  WHILE_DO_ : Expr → Programa → Programa

-- Definimos un tipo
--    Traza S M₁ M₂
-- cuyos habitantes son trazas de ejecución del programa S
-- que inician en la memoria inicial M₁ y terminan en la memoria M₂.
--
-- El tipo se puede entender desde el punto de vista lógico como un
-- juicio que es válido cuando al ejecutar el programa P sobre la
-- memoria inicial M1, el programa termina y la memoria final es M2.
--
data Traza : Programa → Memoria → Memoria → Set where
  T-:=      : {x : Id} {e : Expr} {M₁ M₂ : Memoria}
            → M₂ ≡ almacenar M₁ x (evaluar M₁ e)
            → Traza (x := e) M₁ M₂
  T-&       : {S T : Programa} {M₁ M₂ M₃ : Memoria}
            → Traza S M₁ M₂
            → Traza T M₂ M₃
            → Traza (S & T) M₁ M₃
  T-WHILE-0 : {e : Expr} {S : Programa} {M : Memoria}
            → IsZero (evaluar M e)
            → Traza (WHILE e DO S) M M
  T-WHILE-S : {e : Expr} {S : Programa} {M₁ M₂ M₃ : Memoria}
            → NonZero (evaluar M₁ e)
            → Traza S M₁ M₂
            → Traza (WHILE e DO S) M₂ M₃
            → Traza (WHILE e DO S) M₁ M₃

-- Definimos el siguiente programa, que calcula el factorial de
-- la variable N (en la posición 0 de la memoria)
-- usando un contador auxiliar I (en la posición 1 de la memoria)
-- y lo almacena en la variable R (en la posición 2 de la memoria).
FACTORIAL : Programa
FACTORIAL =
      I := e-const 0
    & R := e-const 1
    & WHILE (e-binaria _∸_ (e-var N) (e-var I)) DO (
        I := e-unaria suc (e-var I)
      & R := e-binaria _*_ (e-var R) (e-var I)
      )
  where N = 0 ; I = 1 ; R = 2

-- [Ejercicio 2]
-- Demostrar que hay una ejecución del factorial que
-- inicia con la memoria en el estado {N=0, I=0, R=0}
-- y finaliza en el estado {N=0, I=0, R=1}.
traza-factorial-0 : Traza FACTORIAL
                          (0 ∷ 0 ∷ 0 ∷ [])  -- Memoria inicial
                          (0 ∷ 0 ∷ 1 ∷ [])  -- Memoria final
traza-factorial-0 =
  T-&
    (T-:= refl)
    (T-&
      (T-:= refl)
      {!!})

-- [Ejercicio 3]
-- Demostrar que hay una ejecución del factorial que
-- inicia con la memoria en el estado {N=3, I=0, R=0}
-- y finaliza en el estado {N=3, I=3, R=6}.
traza-factorial-3 : Traza FACTORIAL
                              (3 ∷ 0 ∷ 0 ∷ [])  -- Memoria inicial
                              (3 ∷ 3 ∷ 6 ∷ [])  -- Memoria final
traza-factorial-3 =
  T-&
    {!!}
    (T-&
      {!!}
      (T-WHILE-S
        {!!}
        {!!}
        {!!}))

--------------------------------------------------------------------------------

---- Ejecución de programas ----

-- Nos gustaría contar con una función:
--   ejecutar : Programa → Memoria → Memoria
-- que dado un programa y un estado inicial de la memoria calcule
-- el estado final de la memoria. Más aún, nos gustaría que la función devuelva
-- la traza de ejecución del programa.
--
-- El problema es que la teoría de tipos de Agda sólo nos permite
-- definir funciones totales, y la función `ejecutar` no sería total, porque un
-- programa se puede colgar. Por ejemplo, no hay ninguna traza de ejecución
-- para el siguiente programa (ya que las trazas son finitas).

ciclo-infinito : Programa
ciclo-infinito = WHILE (e-const 1) DO (X := e-var X)
  where
    X = 0

-- No hay manera de subsanar este problema, debido a que, como mostró Alan
-- Turing en 1936, no es decidible determinar si un programa se detendrá.
--
-- Para implementar una función parcial computable f : A → B,
-- lo que podemos hacer es definir una variante g : ℕ → A → Maybe B.
-- La función g recibe un primer parámetro adicional, que es un número natural,
-- a veces llamado "gas" en inglés (en el sentido de "nafta" o "gasolina").
--
-- Cada vez que g hace un llamado recursivo, decrementa el valor de la "nafta".
-- En caso de que se acabe la nafta (es decir, el primer parámetro llegue a 0),
-- la función g devuelve nothing.

-- [Ejercicio 4]
-- Completar la función ejecutar-acotado, que ejecuta el programa S
-- sobre la memoria M y usando la "nafta" para asegurar la terminación.
-- En caso de que la nafta se acabe, devuelve nothing.
ejecutar-acotado : (nafta : ℕ) (S : Programa) (M : Memoria)
                 → Maybe (Σ[ M' ∈ Memoria ] Traza S M M')
ejecutar-acotado zero    _ _ = nothing
ejecutar-acotado (suc n) (X := e) M = just (M' , {!!})
   where M' = almacenar M X (evaluar M e)
ejecutar-acotado (suc n) (S & T) M
  with ejecutar-acotado n S M
...  | nothing            = nothing
...  | just (M1 , traza1) = {!!}
ejecutar-acotado (suc n) (WHILE x DO S) M = {! !}

-- [Ejercicio 5]
-- Completar el valor necesario de la "nafta" para que se pueda calcular
-- el factorial de n.
-- Evaluar algunas expresiones para probarlo; por ejemplo (ejecutar-factorial 10).
ejecutar-factorial : ℕ → ℕ
ejecutar-factorial n with ejecutar-acotado {!!} FACTORIAL (n ∷ 0 ∷ 0 ∷ [])
... | just ((_ ∷ _ ∷ r ∷ []) , _) = r
... | _ = 0 -- (Nunca se debería alcanzar este caso).

--------------------------------------------------------------------------------

---- Triplas de Hoare ----

-- Una condición es un predicado sobre la memoria:

Condición : Set₁
Condición = Memoria → Set

-- Definimos algunos operadores lógicos para definir condiciones:

TRUE : Condición
TRUE = λ _ → ⊤

_AND_ : Condición → Condición → Condición
C1 AND C2 = λ M → C1 M × C2 M

_==>_ : Condición → Condición → Set
C1 ==> C2 = {M : Memoria} → C1 M → C2 M

NOT : Condición → Condición
NOT C = λ M → ¬ (C M)

VALE : Expr → Condición
VALE e = λ M → NonZero (evaluar M e)

SUSTITUIR : Condición → Id → Expr → Condición
SUSTITUIR P x e = λ M → P (almacenar M x (evaluar M e))

-- El siguiente tipo de datos inductivo tiene como habitantes a
-- las demostraciones de que un programa verifica un contrato.
--
-- Más precisamente, si P, Q son condiciones (la pre y la post-condición)
-- y S es un programa, la tripla:
--    P << S >> Q
-- es válida si se puede derivar usando las reglas de la lógica de Hoare.
--
-- Recordemos informalmente las reglas de la lógica de Hoare:
--
-- * La asignación (x := e) valida un contrato (P, Q)
--   si P resulta de sustituir x por e en Q.
-- 
-- * La composición secuencial (S & T) valida un contrato (P, Q)
--   si hay una condición intermedia R
--   tal que S valida (P, R) y T valida (R, Q).
--
-- * Un ciclo (WHILE e DO S) valida el contrato (I, I AND NOT (VALE e)),
--   donde I es el invariante del ciclo, si el programa S valida el contrato
--   (I AND (VALE e), I).
--
-- * Todo programa que satisface un contrato (P, Q) también
--   satisface cualquier contrato con una precondición más fuerte.
--
-- * Todo programa que satisface un contrato (P, Q) también
--   satisface cualquier contrato con una postcondición más débil.
--

data _<<_>>_ : Condición → Programa → Condición → Set₁ where
  Hoare-:= : {x : Id} {e : Expr} {Q : Condición}
           → SUSTITUIR Q x e << x := e >> Q
  Hoare-&  : {P Q : Condición} {S T : Programa}
           → (R : Condición)
           → P << S >> R
           → R << T >> Q
           → P << S & T >> Q
  Hoare-WHILE : {e : Expr} {I : Condición} {S : Programa}
              → I AND (VALE e) << S >> I
              → I << WHILE e DO S >> I AND (NOT (VALE e))
  Hoare-pre  : {P P' Q : Condición} {S : Programa}
             → (P' ==> P)
             → P << S >> Q
             → P' << S >> Q
  Hoare-post : {P Q Q' : Condición} {S : Programa}
             → (Q ==> Q')
             → P << S >> Q
             → P << S >> Q'

-- [Ejercicio 6]
-- Demostrar que la lógica de Hoare es correcta, es decir,
-- asumiendo que:
--   * Se puede demostrar la tripla de Hoare (P << S >> Q).
--   * Hay una traza de ejecución del programa S que inicia
--     en la memoria M y termina en la memoria M'.
--   * M verifica la precondición.
-- Entonces:
--   * M' verifica la postcondición.
--
Hoare-correcta : {P Q : Condición} {S : Programa} {M M' : Memoria}
               → P << S >> Q
               → Traza S M M'
               → P M
               → Q M'
Hoare-correcta Hoare-:=             traza pre = {!!}
Hoare-correcta (Hoare-& _ H1 H2)    traza pre = {!!}
Hoare-correcta (Hoare-WHILE H)      traza pre = {!!}
Hoare-correcta (Hoare-pre P'=>P H)  traza pre = {!!}
Hoare-correcta (Hoare-post Q=>Q' H) traza pre = {!!}

-- [Ejercicio 7]
-- Demostrar que cada paso del ciclo del factorial es correcto.

module CicloFactorial where

  factorial : ℕ → ℕ
  factorial zero    = suc zero
  factorial (suc n) = factorial n * suc n

  paso : Programa
  paso =
        I := e-unaria suc (e-var I)
      & R := e-binaria _*_ (e-var R) (e-var I)
    where N = 0 ; I = 1 ; R = 2

  invariante : Condición
  invariante =
      λ M → valor M I ≤ valor M N
          × valor M R ≡ factorial (valor M I)
    where N = 0 ; I = 1 ; R = 2

  guarda : Expr
  guarda = e-binaria _∸_ (e-var N) (e-var I)
    where N = 0 ; I = 1 ; R = 2

  paso-correcto : invariante AND (VALE guarda)
                  << paso >>
                  invariante
  paso-correcto =
      Hoare-& {!!}
              (Hoare-pre {!!} Hoare-:=)
              (Hoare-pre {!!} Hoare-:=)
    where N = 0 ; I = 1 ; R = 2

