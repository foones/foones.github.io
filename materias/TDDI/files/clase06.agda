open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
      using (_≡_; refl; sym; trans; cong)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

{-
open import Agda.Primitive using (lsuc)
LEM : ∀ {l} → Set (lsuc l)
LEM {l} = ∀ {A : Set l} → A ⊎ ¬ A
-}

DNEG : Set₁
DNEG = {A : Set} → ¬ ¬ A → A

PEIRCE : Set₁
PEIRCE = {A B : Set} → ((A → B) → A) → A

IMPL : Set₁
IMPL = {A B : Set} → (A → B) → ¬ A ⊎ B

DM : Set₁
DM = {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B

LEM : Set₁
LEM = {A : Set} → A ⊎ ¬ A

DM=>LEM : DM → LEM
DM=>LEM dm {A} = dm {A} {¬ A} (λ { (na , nna) → nna na })

----

¬A⊎B=>A→B : {A B : Set} → ¬ A ⊎ B → A → B
¬A⊎B=>A→B (inj₁ na) = λ a → ⊥-elim (na a)
¬A⊎B=>A→B (inj₂ b)  = λ _ → b

A⊎B=>¬[¬A×¬B] : {A B : Set} → A ⊎ B → ¬(¬ A × ¬ B)
A⊎B=>¬[¬A×¬B] {A} {B} (inj₁ a) = λ { (na , _) → na a }
A⊎B=>¬[¬A×¬B] {A} {B} (inj₂ b) = λ { (_ , nb) → nb b }

----

LEM=>DNEG : LEM → DNEG
LEM=>DNEG lem {A} with lem {A}
... | inj₁ a  = λ _ → a
... | inj₂ na = λ nna → ⊥-elim (nna na)

{-
LEM=>PEIRCE : LEM → PEIRCE
LEM=>PEIRCE lem {A} {B} with lem {A → B}
... | inj₁ p = λ f → f p
... | inj₂ q = λ f → ⊥-elim (q (λ a → ⊥-elim (q {!!})))
LEM=>PEIRCE lem {A} {B} with lem {A}
... | inj₁ a  = λ _ → a
... | inj₂ na = λ f → f (λ a → ⊥-elim (na a))
-}

DNEG=>PEIRCE : DNEG → PEIRCE
DNEG=>PEIRCE dneg {A} {B} = λ f → dneg λ na →
                              na (f λ a → ⊥-elim (na a))

PEIRCE=>IMPL : PEIRCE → IMPL
PEIRCE=>IMPL = {!!} -- Ejercicio

IMPL=>DM : IMPL → DM
IMPL=>DM impl {A} {B} f with impl {A} {A} (λ x → x)
... | inj₂ a  = inj₁ a
... | inj₁ na
    with impl {B} {B} (λ x → x)
...    | inj₂ b  = inj₂ b
...    | inj₁ nb = ⊥-elim (f (na , nb))

------------------------------------

data Expr : Set where
  e-const : ℕ → Expr
  e-add   : Expr → Expr → Expr

eval : Expr → ℕ
eval (e-const n)   = n
eval (e-add e₁ e₂) = eval e₁ + eval e₂

data Instr : Set where
  i-push : ℕ → Instr
  i-add  : Instr

run : List Instr → List ℕ → List ℕ
run []                s           = s
run (i-push n ∷ prog) s           = run prog (n ∷ s)
run (i-add ∷ prog)    []          = run prog []
run (i-add ∷ prog)    (n ∷ [])    = run prog (n ∷ [])
run (i-add ∷ prog)    (m ∷ n ∷ s) = run prog ((n + m) ∷ s)

compile : Expr → List Instr
compile (e-const n)   = i-push n ∷ []
compile (e-add e₁ e₂) = compile e₁ ++ compile e₂ ++ i-add ∷ []

run-++ : ∀ {p q s}
       → run (p ++ q) s ≡ run q (run p s)
run-++ {[]}                           = refl
run-++ {i-push n ∷ p} {q} {s}         = run-++ {p}
run-++ {i-add ∷ p}    {q} {[]}        = run-++ {p}
run-++ {i-add ∷ p}    {q} {n ∷ []}    = run-++ {p}
run-++ {i-add ∷ p}    {q} {m ∷ n ∷ s} = run-++ {p}

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ g f x = g (f x)

compile-correcto : {e : Expr} {s : List ℕ}
                 → run (compile e) s ≡ eval e ∷ s
compile-correcto {e-const n} = refl
compile-correcto {e-add e₁ e₂} {s} =
  begin
    run (compile e₁ ++ (compile e₂ ++ i-add ∷ [])) s
  ≡⟨ run-++ {compile e₁} ⟩
    run (compile e₂ ++ i-add ∷ []) (run (compile e₁) s)
  ≡⟨ run-++ {compile e₂} ⟩
    run (i-add ∷ []) (run (compile e₂) (run (compile e₁) s))
  ≡⟨ cong (run (i-add ∷ []) ∘ run (compile e₂))
          (compile-correcto {e₁}) ⟩
    run (i-add ∷ []) (run (compile e₂) (eval e₁ ∷ s))
  ≡⟨ cong (run (i-add ∷ [])) (compile-correcto {e₂}) ⟩
    run (i-add ∷ []) (eval e₂ ∷ eval e₁ ∷ s)
  ≡⟨ refl ⟩
    eval e₁ + eval e₂ ∷ s
  ∎

----

ejemplo : Expr
ejemplo = e-add (e-const 1) (e-const 2)

----

data Form : Set where
  VAR   : ℕ → Form
  TRUE  : Form
  FALSE : Form
  AND   : Form → Form → Form
  OR    : Form → Form → Form
  IMP   : Form → Form → Form
  NEG   : Form → Form

data Ctx : Set where
  ∅   : Ctx
  _,,_ : Ctx → Form → Ctx
  
data _∋_ : Ctx → Form → Set where 
  zero : ∀ {Γ A}
         → (Γ ,, A) ∋ A
  suc  : ∀ {Γ A B}
         → Γ ∋ A
         → (Γ ,, B) ∋ A

data _⊢_ : Ctx → Form → Set where 
  ax : ∀ {Γ A}
       → Γ ∋ A
       → Γ ⊢ A
  and-i : ∀ {Γ A B}
          → (Γ ⊢ A)
          → (Γ ⊢ B)
          → (Γ ⊢ AND A B)
  imp-i : ∀ {Γ A B}
          → ((Γ ,, A) ⊢ B)
          → (Γ ⊢ IMP A B)
  imp-e : ∀ {Γ A B}
          → (Γ ⊢ IMP A B)
          → (Γ ⊢ A)
          → (Γ ⊢ B)

ejemplo2 : ∀ {A B C} →
          ∅ ⊢ IMP (IMP A (IMP B C))
                   (IMP (IMP A B) (IMP A C))
ejemplo2 {A} {B} {C} =
  imp-i (imp-i (imp-i
             (imp-e (imp-e
                       (ax (suc (suc zero)))
                       (ax zero))
                    (imp-e
                      (ax (suc zero))
                      (ax zero)))))
  
