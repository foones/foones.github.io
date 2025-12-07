open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_)
open import Data.String using (String; _≟_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

BTy : Set
BTy = ℕ

infixl 30 _,,_
infixr 40 _=>_

data Ty : Set where
  base : BTy → Ty
  _=>_ : Ty → Ty → Ty

data Ctx : Set where
  ∅   : Ctx
  _,,_ : Ctx → Ty → Ctx

data _∋_ : Ctx → Ty → Set where
  zero : ∀ {Γ A} → (Γ ,, A) ∋ A
  suc  : ∀ {Γ A B}
         → Γ ∋ A
         → (Γ ,, B) ∋ A

data _⊢_ : Ctx → Ty → Set where
  var : ∀ {Γ A}
        → Γ ∋ A
        → Γ ⊢ A
  lam : ∀ {Γ A B}
        → Γ ,, A ⊢ B
        → Γ ⊢ A => B
  app : ∀ {Γ A B}
        → Γ ⊢ A => B
        → Γ ⊢ A
        → Γ ⊢ B

ejemplo-I : {A : Ty} → ∅ ⊢ A => A
ejemplo-I = lam (var zero)

ejemplo-K : {A B : Ty} → ∅ ⊢ A => B => A
ejemplo-K = lam (lam (var (suc zero)))

ejemplo-S : {A B C : Ty} → ∅ ⊢ (A => B => C)
                             => (A => B)
                             => (A => C)
ejemplo-S = lam (lam (lam
              (app (app (var (suc (suc zero))) (var zero))
                   (app (var (suc zero)) (var zero)))))

ejemplo-Rafa = app {∅} {base 0 => base 0}
                 (lam (var zero))   -- A => B
                 (lam (var zero))   -- A

----

Renombre : Ctx → Ctx → Set 
Renombre Γ Δ = {A : Ty} → Γ ∋ A → Δ ∋ A

shift : ∀ {Γ Δ A} → Renombre Γ Δ → Renombre (Γ ,, A) (Δ ,, A)
shift ρ zero    = zero
shift ρ (suc q) = suc (ρ q)

renombrar : ∀ {Γ Δ A} → Renombre Γ Δ → Γ ⊢ A → Δ ⊢ A
renombrar ρ (var x)   = let x' = ρ x
                         in var x'
renombrar ρ (lam M)   = let M' = renombrar (shift ρ) M
                         in lam M'
renombrar ρ (app M N) = let M' = renombrar ρ M
                            N' = renombrar ρ N
                         in app M' N'

----

Sustitución : Ctx → Ctx → Set 
Sustitución Γ Δ = {A : Ty} → Γ ∋ A → Δ ⊢ A

ejemplo-sust :
  let Γ = ∅ ,, base 1
      Δ = ∅ ,, base 0 ,, base 0 => base 1
   in Sustitución Γ Δ
ejemplo-sust zero = app (var zero) (var (suc zero))

shiftS : ∀ {Γ Δ A} → Sustitución Γ Δ → Sustitución (Γ ,, A) (Δ ,, A)
shiftS σ zero    = var zero
shiftS σ (suc q) = let N = σ q
                    in renombrar suc N

sustitución : ∀ {Γ Δ A} → Sustitución Γ Δ → Γ ⊢ A → Δ ⊢ A
sustitución σ (var x)   = σ x
sustitución σ (lam M)   = let M' = sustitución (shiftS σ) M
                           in lam M'
sustitución σ (app M N) = let M' = sustitución σ M
                              N' = sustitución σ N
                           in app M' N'

----

sust0 : ∀ {Γ A}
        → (Γ ⊢ A)
        → Sustitución (Γ ,, A) Γ
sust0 N zero    = N
sust0 N (suc x) = var x

data _~>_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ~>β : ∀ {Γ A B}
        → {M : Γ ,, A ⊢ B}
        → {N : Γ ⊢ A}
        → app (lam M) N ~> sustitución (sust0 N) M
  ~>µ : ∀ {Γ A B}
        → {M M' : Γ ⊢ A => B}
        → {N : Γ ⊢ A}
        → M ~> M'
        → app M N ~> app M' N
  ~>ν : ∀ {Γ A B}
        → {M : Γ ⊢ A => B}
        → {N N' : Γ ⊢ A}
        → N ~> N'
        → app M N ~> app M N'
  ~>ξ : ∀ {Γ A B}
        → {M M' : Γ ,, A ⊢ B}
        → M ~> M'
        → lam M ~> lam M'

reducción-ejemplo-Rafa
  :
    app {∅} {base 0 => base 0} (lam (var zero)) (lam (var zero))
    ~>
    lam (var zero)
reducción-ejemplo-Rafa = ~>β
