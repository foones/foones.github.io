{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite

open import Data.Nat      using (ℕ; zero; suc; _+_; _*_)
open import Data.List     using (List; []; _∷_)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; proj₁; proj₂)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
                          using (_≡_; refl)

-- F(X) = A × X

postulate Stream : Set → Set
postulate head : {A : Set} → Stream A → A
postulate tail : {A : Set} → Stream A → Stream A
postulate unfold : {A : Set} → (B : Set) → (B → A) → (B → B) → B → Stream A
postulate head-unfold : {A B : Set} {h : B → A} {t : B → B} {b0 : B}
                      → head (unfold B h t b0) ≡ h b0
postulate tail-unfold : {A B : Set} {h : B → A} {t : B → B} {b0 : B}
                      → tail (unfold B h t b0) ≡ unfold B h t (t b0)

{-# REWRITE head-unfold #-}
{-# REWRITE tail-unfold #-}

zeros : Stream ℕ
zeros = unfold ⊤
               (λ _ → zero)
               (λ _ → tt)
               tt

desde : ℕ → Stream ℕ
desde n = unfold ℕ (λ m → m) suc n

take : {A : Set} → ℕ → Stream A → List A
take zero    s = []
take (suc n) s = head s ∷ take n (tail s)

map : {A B : Set} → (A → B) → Stream A → Stream B
map {A} {B} f s = unfold (Stream A) (λ s' → f (head s')) tail s

---------

postulate _≈_ : {A : Set} → Stream A → Stream A → Set
postulate ≈-head : {A : Set} {s1 s2 : Stream A}
                 → s1 ≈ s2
                 → head s1 ≡ head s2
postulate ≈-tail : {A : Set} {s1 s2 : Stream A}
                 → s1 ≈ s2
                 → tail s1 ≈ tail s2
postulate
  ≈-unfold :
        {A : Set}
    → (P : Stream A → Stream A → Set)
    → ((s1 s2 : Stream A) → P s1 s2 → head s1 ≡ head s2)
    → ((s1 s2 : Stream A) → P s1 s2 → P (tail s1) (tail s2))
    → {s1 s2 : Stream A}
    → P s1 s2
    → s1 ≈ s2

---------

drop : {A : Set} → ℕ → Stream A → Stream A
drop zero    s = s
drop (suc n) s = drop n (tail s)

map-compose* : {A B C : Set} {f : A → B} {g : B → C} {s : Stream A}
               (n : ℕ)
             → head (drop n (map g (map f s))) ≡
               head (drop n (map (λ x → g (f x)) s))
map-compose* zero    = refl
map-compose* {A} {B} {C} {f} {g} {s} (suc n) =
  map-compose* {A} {B} {C} {f} {g} {tail s} n

map-compose : {A B C : Set} {f : A → B} {g : B → C} {s : Stream A}
            → map g (map f s) ≈ map (λ x → g (f x)) s
map-compose {A} {B} {C} {f} {g} {s}
  = ≈-unfold (λ s1 s2 → (n : ℕ)
                → head (drop n s1) ≡ head (drop n s2))
             (λ s1 s2 Ps1s2 → Ps1s2 zero)
             (λ s1 s2 Ps1s2 n → Ps1s2 (suc n))
             (map-compose* {A} {B} {C} {f} {g} {s})

ejemplo = take 10
               (map (λ x → x * x) (map (λ x → x * x) (desde 1)))
