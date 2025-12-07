
{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (lsuc)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

----

transport : {A : Set} (B : A → Set)
            {a1 a2 : A} (p : a1 ≡ a2)
          → B a1 → B a2
transport B refl x = x

ap : {A B : Set} (f : A → B)
   → {a1 a2 : A} → a1 ≡ a2
   → f a1 ≡ f a2
ap _ refl = refl

apd : {A : Set} {B : A → Set} (f : (a : A) → B a)
    → {a1 a2 : A} (p : a1 ≡ a2)
    → transport B p (f a1) ≡ f a2
apd _ refl = refl

transportconst : {A B : Set} {a1 a2 : A} (p : a1 ≡ a2) {b : B}
               → transport (λ _ → B) p b ≡ b
transportconst refl = refl

apd-transportconst : {A B : Set} (f : A → B)
                   → {a1 a2 : A} (p : a1 ≡ a2)
                   → apd f p ≡ trans (transportconst p) (ap f p)
apd-transportconst f refl = refl

----

infixr 4 _~_

data _~_ {A : Set} : List A → List A → Set where
  ~-refl : {xs : List A} → xs ~ xs
  ~-dip  : {x : A} {xs ys : List A}
         → xs ~ ys
         → x ∷ xs ~ x ∷ ys
  ~-swap : {x y : A} {xs ys : List A}
         → xs ~ ys
         → x ∷ y ∷ xs ~ y ∷ x ∷ ys
  ~-trans : {xs ys zs : List A}
          → xs ~ ys
          → ys ~ zs
          → xs ~ zs

postulate Multiconj : Set → Set
postulate π : {A : Set} → List A → Multiconj A
postulate perm : {A : Set} {xs ys : List A}
               → xs ~ ys
               → π xs ≡ π ys
postulate ind-Multiconj :
                 {A : Set} (C : Multiconj A → Set)
               → (f : (xs : List A) → C (π xs))
               → ({xs ys : List A}
                  → (xs~ys : xs ~ ys)
                  → transport C (perm xs~ys) (f xs) ≡ f ys)
               → (M : Multiconj A) → C M
postulate ind-Multiconj-computo :
                 {A : Set} {C : Multiconj A → Set}
                 {f : (xs : List A) → C (π xs)}
                 {coh : {xs ys : List A}
                      → (xs~ys : xs ~ ys)
                      → transport C (perm xs~ys) (f xs) ≡ f ys}
                 {xs : List A}
               → ind-Multiconj C f coh (π xs) ≡ f xs
{-# REWRITE ind-Multiconj-computo #-}

postulate Multiconj-isSet : {A : Set} {M N : Multiconj A} {p q : M ≡ N}
                          → p ≡ q

rec-Multiconj : {A : Set} (B : Set)
              → (f : List A → B)
              → ({xs ys : List A} → xs ~ ys → f xs ≡ f ys)
              → Multiconj A → B
rec-Multiconj B f coh =
  ind-Multiconj (λ _ → B)
                f
                (λ xs~ys → trans (transportconst (perm xs~ys))
                                 (coh xs~ys))

~-preserva-length : {A : Set} {xs ys : List A}
                  → xs ~ ys
                  → length xs ≡ length ys
~-preserva-length ~-refl        = refl
~-preserva-length (~-dip p)     = cong suc (~-preserva-length p)
~-preserva-length (~-swap p)    = cong suc (cong suc (~-preserva-length p))
~-preserva-length (~-trans p q) = trans (~-preserva-length p)
                                        (~-preserva-length q)

size : Multiconj ℕ → ℕ
size = rec-Multiconj ℕ length ~-preserva-length

ejemplo = size (π (2 ∷ 1 ∷ []))

add : {A : Set} → A → Multiconj A → Multiconj A
add x M = rec-Multiconj (Multiconj _)
                        (λ xs → π (x ∷ xs))
                        (λ xs~ys → perm (~-dip xs~ys))
                        M
                        
----

ejemplito : add 1 (π (2 ∷ 3 ∷ [])) ≡ π (1 ∷ 2 ∷ 3 ∷ [])
ejemplito = refl

----

add-list : {A : Set} → List A → Multiconj A → Multiconj A
add-list []       M = M
add-list (x ∷ xs) M = add x (add-list xs M)

add-swap : {A : Set} {x y : A} {M : Multiconj A}
         → add x (add y M) ≡ add y (add x M)
add-swap {A} {x} {y} {M} =
  ind-Multiconj (λ M → add x (add y M) ≡ add y (add x M))
                (λ xs → perm (~-swap ~-refl))
                (λ _ → Multiconj-isSet)
                M

add-list-coh : {A : Set} {xs ys : List A} {M : Multiconj A}
             → xs ~ ys
             → add-list xs M ≡ add-list ys M
add-list-coh ~-refl             = refl
add-list-coh (~-dip {x} p)      = cong (add x) (add-list-coh p)
add-list-coh (~-swap {x} {y} {xs} p) =
  trans (add-swap {_} {x} {y} {add-list xs _})
        (cong (add y) (cong (add x) (add-list-coh p)))
add-list-coh (~-trans p q)      = trans (add-list-coh p)
                                        (add-list-coh q)

_∪_ : {A : Set} → Multiconj A → Multiconj A → Multiconj A
M ∪ N = rec-Multiconj (Multiconj _)
                      (λ xs → add-list xs N)
                      add-list-coh
                      M

