open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_)

infix  60 _⊢_ _∋_
infixl 70 _,_

-- El objetivo de esta parte del TP es demostrar que el sistema de
-- deducción natural para la lógica proposicional clásica es correcto
-- con respecto a la semántica bivaluada. Nos restringimos al fragmento
-- con implicación y absurdo.

---- Sintaxis de la lógica proposicional ----

-- Las fórmulas se construyen inductivamente:
data Form : Set where
  PVAR  : String → Form       -- variable proposicional
  FALSE : Form                -- absurdo
  IMP   : Form → Form → Form  -- implicación

ejemplo-formula : Form
ejemplo-formula = IMP (PVAR "P") (IMP (PVAR "Q") (PVAR "P"))

-- Definimos conectivos derivados: negación, disyunción y conjunción.
-- Estas abreviaturas no definirían conectivos equivalentes en lógica
-- intuicionista, pero trabajaremos en el marco clásico.

NOT : Form → Form
NOT a = IMP a FALSE

OR : Form → Form → Form
OR a b = IMP (NOT a) b

AND : Form → Form → Form
AND a b = NOT (IMP a (NOT b))

-- Un contexto es una lista de fórmulas:
data Ctx : Set where
  []  : Ctx
  _,_ : Ctx → Form → Ctx

-- Un contexto incluye a una fórmula si la fórmula aparece en el contexto.
-- Se define inductivamente.
-- [El símbolo "∋" se puede ingresar con "\ni"].
data _∋_ : Ctx → Form → Set where
  zero : {Γ : Ctx} {A : Form} → (Γ , A) ∋ A
  suc  : {Γ : Ctx} {A B : Form} → Γ ∋ A → (Γ , B) ∋ A

---- Deducción natural para lógica proposicional ----

-- Definimos un juicio "Γ ⊢ A".
-- [El símbolo "⊢" se puede ingresar con "\|-"].
data _⊢_ : Ctx → Form → Set where
  AX : {Γ : Ctx} {A : Form}
     → Γ ∋ A
     → Γ ⊢ A

  -- Eliminación del falso.
  FALSE-e : {Γ : Ctx} {A : Form}
          → Γ ⊢ FALSE
          → Γ ⊢ A
    
  -- Introducción de la implicación.
  IMP-i : {Γ : Ctx} {A B : Form}
        → Γ , A ⊢ B
        → Γ ⊢ IMP A B

  -- Eliminación de la implicación.
  IMP-e : {Γ : Ctx} {A B : Form}
        → Γ ⊢ IMP A B
        → Γ ⊢ A
        → Γ ⊢ B

  -- Eliminación de la doble negación:
  -- de Γ ⊢ ¬¬A se puede concluir Γ ⊢ A.
  DNEG : {Γ : Ctx} {A : Form}
       → Γ ⊢ IMP (IMP A FALSE) FALSE
       → Γ ⊢ A

-- [Ejercicio 1]
--
-- Si Γ y Δ son listas de fórmulas, una inclusión (de tipo `Inclusion Γ Δ`)
-- es una función que atestigua que cada fórmula que aparece en Γ
-- también aparece en Δ:
--
Inclusion : Ctx → Ctx → Set
Inclusion Γ Δ = {A : Form} → Γ ∋ A → Δ ∋ A

-- Demostrar que si Γ está incluido en Δ, entonces (Γ , A) está incluido en (Δ , A).
extender-inclusion : {Γ Δ : Ctx} {A : Form}
                   → Inclusion Γ Δ
                   → Inclusion (Γ , A) (Δ , A)
extender-inclusion = ?

-- [Ejercicio 2]
-- Demostrar la siguiente propiedad de debilitamiento (o weakening),
-- que afirma que si una lista de hipótesis Γ está incluida en una lista Δ,
-- entonces cada vez que se puede probar Γ ⊢ A también es posible probar Δ ⊢ A.
--
-- Proceder por inducción en la derivación de Γ ⊢ A.
-- La mayor parte de los casos son fáciles recurriendo a la hipótesis inductiva.
-- El caso IMP-i requiere extender la inclusión.
debilitamiento : {Γ Δ : Ctx} {A : Form}
               → Inclusion Γ Δ
               → Γ ⊢ A
               → Δ ⊢ A
debilitamiento incl (AX x)      = {! !}
debilitamiento incl (FALSE-e p) = {! !}
debilitamiento incl (IMP-i p)   = {! !}
debilitamiento incl (IMP-e p q) = {! !}
debilitamiento incl (DNEG p)    = {! !}

-- Como caso particular de debilitamiento, se obtienen los siguientes lemas:

wk : {Γ : Ctx} {A B : Form}
   → Γ ⊢ A
   → Γ , B ⊢ A
wk = debilitamiento ?

wk1 : {Γ : Ctx} {A B C : Form}
    → Γ , C ⊢ A
    → Γ , B , C ⊢ A
wk1 = debilitamiento ?

-- [Ejercicio 3]
-- Demostrar el siguiente lema de sustitución.
-- No requiere hacer inducción, sólo usar IMP-i e IMP-e.

subst : {Γ : Ctx} {A B : Form}
      → Γ , A ⊢ B
      → Γ ⊢ A
      → Γ ⊢ B
subst p q = ?

-- [Ejercicio 4]
-- Demostrar los siguientes principios de razonamiento clásicos.
-- No requieren usar inducción, pero sí DNEG.

-- La regla de reducción al absurdo afirma que para demostrar Γ ⊢ A
-- siempre alcanza con demostrar Γ , ¬A ⊢ FALSE
reductio-ad-absurdum : {Γ : Ctx} {A : Form}
                     → Γ , NOT A ⊢ FALSE
                     → Γ ⊢ A
reductio-ad-absurdum p = ?

-- El principio de "consecuencia milagrosa" afirma que para demostrar Γ ⊢ A
-- siempre alcanza con demostrar Γ , ¬A ⊢ A.
consequentia-mirabilis : {Γ : Ctx} {A : Form}
                       → Γ , NOT A ⊢ A
                       → Γ ⊢ A
consequentia-mirabilis p = ?

-- [Ejercicio 5]
-- Demostrar las siguientes reglas derivadas.
-- Algunas de ellas requieren usar el lema de debilitamiento ("wk").

NOT-i : {Γ : Ctx} {A : Form}
      → Γ , A ⊢ FALSE
      → Γ ⊢ NOT A
NOT-i p = ?

NOT-e : {Γ : Ctx} {A : Form}
      → Γ ⊢ NOT A
      → Γ ⊢ A
      → Γ ⊢ FALSE
NOT-e p q = ?

AND-i : {Γ : Ctx} {A B : Form}
      → Γ ⊢ A
      → Γ ⊢ B
      → Γ ⊢ AND A B
AND-i p q = ?

AND-e1 : {Γ : Ctx} {A B : Form}
       → Γ ⊢ AND A B
       → Γ ⊢ A
AND-e1 p = ?   -- Recordar que es posible razonar clásicamente usando DNEG.

AND-e2 : {Γ : Ctx} {A B : Form}
       → Γ ⊢ AND A B
       → Γ ⊢ B
AND-e2 p = ?

OR-i1 : {Γ : Ctx} {A B : Form}
      → Γ ⊢ A
      → Γ ⊢ OR A B
OR-i1 p = ?

OR-i2 : {Γ : Ctx} {A B : Form}
      → Γ ⊢ B
      → Γ ⊢ OR A B
OR-i2 p = ?

-- El siguiente lema es un poco más difícil que los anteriores.
-- Se sugiere usar la siguiente estructura:
-- 1) Para probar Γ ⊢ C, usar consequentia-mirabilis
--    para reducir el problema a demostrar Γ , ¬C ⊢ C.
-- 2) Para demostrar Γ , ¬C ⊢ C, usar la hipótesis Γ , A ⊢ C
--    para reducir el problema a demostrar Γ , ¬C ⊢ A.
-- 3) Para demostrar Γ , ¬C ⊢ A, usar reducción al absurdo
--    para reducir el problema a demostrar Γ , ¬C , ¬A ⊢ FALSE.
-- 4) (El resto queda como ejercicio para completar).
OR-e : {Γ : Ctx} {A B C : Form}
     → Γ ⊢ OR A B
     → Γ , A ⊢ C
     → Γ , B ⊢ C
     → Γ ⊢ C
OR-e p q r = consequentia-mirabilis (subst (wk1 q) (reductio-ad-absurdum ?))

LEM : {Γ : Ctx} {A : Form}
    → Γ ⊢ OR A (NOT A)
LEM = ?

---- Semántica bivaluada de la lógica proposicional ----

-- Una valuación es una función que le asigna un booleano a cada variable
-- proposicional:
Valuacion : Set
Valuacion = String → Bool

-- El valor de verdad de una fórmula bajo una valuación se calcula recursivamente:
valor-Form : Valuacion → Form → Bool
valor-Form v (PVAR x)  = v x
valor-Form v FALSE     = false
valor-Form v (IMP A B) with valor-Form v A
... | false = true
... | true  = valor-Form v B

-- Una valuación satisface una fórmula si le da valor verdadero:
satisface-Form : Valuacion → Form → Set
satisface-Form v A = (valor-Form v A ≡ true)

-- Una valuación satisface un contexto si hace verdaderas a todas sus fórmulas:
satisface-Ctx : Valuacion → Ctx → Set
satisface-Ctx v Γ = ∀ {A : Form} → Γ ∋ A → satisface-Form v A

-- Una valuación satisface a un secuente "Γ ⊢ A" si, asumiendo que
-- satisface al contexto, satisface también a la fórmula.
satisface : Valuacion → Ctx → Form → Set
satisface v Γ A = (satisface-Ctx v Γ → satisface-Form v A)

-- Un secuente es válido si todas las valuaciones lo satisfacen.
esSecuenteValido : Ctx → Form → Set
esSecuenteValido Γ A = ((v : Valuacion) → satisface v Γ A)

---- Corrección de la deducción natural ----

-- [Ejercicio 6]
-- Demostrar que el sistema de deducción natural clásico es correcto
-- con respecto a la semántica bivaluada.
deduccion-natural-correcta : {Γ : Ctx} {A : Form}
                           → Γ ⊢ A
                           → esSecuenteValido Γ A
deduccion-natural-correcta = ?

