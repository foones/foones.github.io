
open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc)
open import Data.Product
       using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infixr 80 _∘_

id : {A : Set} → A → A
id x = x

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) a = g (f a)

_~_ : {A : Set} {B : A → Set}
    → (f g : (a : A) → B a)
    → Set
(f ~ g) = ∀ a → f a ≡ g a

~-refl : {A : Set} {B : A → Set} {f : (a : A) → B a}
       → f ~ f
~-refl _ = refl

~-sym : {A : Set} {B : A → Set} {f g : (a : A) → B a}
       → f ~ g
       → g ~ f
~-sym f~g a = sym (f~g a)

~-trans : {A : Set} {B : A → Set} {f g h : (a : A) → B a}
        → f ~ g
        → g ~ h
        → f ~ h
~-trans f~g g~h a = trans (f~g a) (g~h a)

~-cong-∘-left : {A B C : Set} (h : B → C) {f g : A → B}
              → (f ~ g)
              → ((h ∘ f) ~ (h ∘ g))
~-cong-∘-left h f~g x = cong h (f~g x)

~-cong-∘-right : {A B C : Set} {f g : A → B} (h : C → A)
               → (f ~ g)
               → ((f ∘ h) ~ (g ∘ h))
~-cong-∘-right h f~g x = f~g (h x)

-----------

-- Razonamiento ecuacional para homotopías:

infixr 60 _~⟨_⟩_
infixr 70 _□

_□ : {A : Set} {B : A → Set} → (f : (a : A) → B a) → f ~ f
_ □ = ~-refl

_~⟨_⟩_ : {A : Set} {B : A → Set}
       → (f : (a : A) → B a)
       → {g : (a : A) → B a}
       → (f ~ g)
       → {h : (a : A) → B a}
       → (g ~ h)
       → (f ~ h)
_ ~⟨ α ⟩ β = ~-trans α β

-----------

record qinv {A B : Set} (f : A → B) : Set where
  field
    inv : B → A
    inv∘f : (inv ∘ f) ~ id
    f∘inv : (f ∘ inv) ~ id
open qinv

record isEquiv {A B : Set} (f : A → B) : Set where
  field
    izq : B → A
    izq∘f : (izq ∘ f) ~ id
    der : B → A
    f∘der : (f ∘ der) ~ id
open isEquiv

qinv⇒isEquiv : {A B : Set} {f : A → B}
              → qinv f
              → isEquiv f
izq   (qinv⇒isEquiv qinvF) = inv   qinvF
izq∘f (qinv⇒isEquiv qinvF) = inv∘f qinvF
der   (qinv⇒isEquiv qinvF) = inv   qinvF
f∘der (qinv⇒isEquiv qinvF) = f∘inv qinvF

isEquiv⇒qinv : {A B : Set} {f : A → B}
              → isEquiv f
              → qinv f
inv   (isEquiv⇒qinv isEquivF) = izq isEquivF
inv∘f (isEquiv⇒qinv isEquivF) = izq∘f isEquivF
f∘inv (isEquiv⇒qinv {A} {B} {f} isEquivF) =
    (f ∘ inv (isEquiv⇒qinv isEquivF))
  ~⟨ ~-refl ⟩
    (f ∘ izq isEquivF)
  ~⟨ ~-refl ⟩
    ((f ∘ izq isEquivF) ∘ id)
  ~⟨ (~-cong-∘-left (f ∘ izq isEquivF) (~-sym (f∘der isEquivF))) ⟩
    ((f ∘ izq isEquivF) ∘ (f ∘ der isEquivF))
  ~⟨ ~-refl ⟩
    (f ∘ ((izq isEquivF ∘ f) ∘ der isEquivF))
  ~⟨ ~-cong-∘-left f (~-cong-∘-right (der isEquivF) (izq∘f isEquivF)) ⟩
    (f ∘ (id ∘ der isEquivF))
  ~⟨ ~-refl ⟩
    (f ∘ der isEquivF)
  ~⟨ f∘der isEquivF ⟩
    id
  □

record _≃_ (A B : Set) : Set where
  field
    iso : A → B
    eqv : isEquiv iso
open _≃_

≃-refl : {A : Set} → A ≃ A
iso ≃-refl = id
izq   (eqv ≃-refl) = id
izq∘f (eqv ≃-refl) = ~-refl
der   (eqv ≃-refl) = id
f∘der (eqv ≃-refl) = ~-refl

≃-sym : {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record {
              iso = g
            ; eqv = qinv⇒isEquiv (
                      record {
                        inv = f
                      ; inv∘f = f∘g~id
                      ; f∘inv = g∘f~id
                      }
                    )
            }
  where            
    f         = iso A≃B
    f-isEquiv = eqv A≃B
    f-qinv    = isEquiv⇒qinv f-isEquiv
    g         = inv f-qinv
    g∘f~id    = inv∘f f-qinv
    f∘g~id    = f∘inv f-qinv
