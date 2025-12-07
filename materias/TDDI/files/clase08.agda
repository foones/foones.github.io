open import Data.Sum
    using (_⊎_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary
    using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

record AnilloConmutativo : Set₁ where
  infixr 40 _+_
  infix  45 -_
  infixr 50 _*_
  field
    R   : Set
    ----
    _+_ : R → R → R
    𝟘   : R
    -_  : R → R
    _*_ : R → R → R
    𝟙   : R 
    ----
    +-neut-l : {x : R} → 𝟘 + x ≡ x
    +-comm   : {x y : R} → x + y ≡ y + x
    +-assoc  : {x y z : R} → (x + y) + z ≡ x + (y + z)
    +-inv    : {x : R} → x + - x ≡ 𝟘
    ----
    *-neut-l : {x : R} → 𝟙 * x ≡ x
    *-comm   : {x y : R} → x * y ≡ y * x
    *-assoc  : {x y z : R} → (x * y) * z ≡ x * (y * z)
    ----
    *-+-distr-r : {x y z : R} → x * (y + z) ≡ (x * y) + (x * z)
    ----
    𝟘≢𝟙 : 𝟘 ≢ 𝟙

module TeoríaDeAnillos (K : AnilloConmutativo) where
  open AnilloConmutativo K

  _-_ : R → R → R
  x - y = x + - y

  +-neut-r : {x : R} → x + 𝟘 ≡ x
  +-neut-r {x} =
      x + 𝟘
    ≡⟨ +-comm ⟩
      𝟘 + x
    ≡⟨ +-neut-l ⟩
      x
    ∎

  *-neut-r : {x : R} → x * 𝟙 ≡ x
  *-neut-r {x} =
      x * 𝟙
    ≡⟨ *-comm ⟩
      𝟙 * x
    ≡⟨ *-neut-l ⟩
      x
    ∎

  *-+-distr-l : {x y z : R} → (x + y) * z ≡ x * z + y * z
  *-+-distr-l {x} {y} {z} =
      (x + y) * z
    ≡⟨ *-comm ⟩
      z * (x + y)
    ≡⟨ *-+-distr-r ⟩
      (z * x) + (z * y)
    ≡⟨ cong (_+ (z * y)) *-comm ⟩
      (x * z) + (z * y)
    ≡⟨ cong (_+_ (x * z)) *-comm ⟩
      (x * z) + (y * z)
    ∎

  *-𝟘 : {x : R} → 𝟘 * x ≡ 𝟘
  *-𝟘 {x} =
      𝟘 * x
    ≡⟨ sym +-neut-r ⟩
      𝟘 * x + 𝟘 
    ≡⟨ cong (_+_ (𝟘 * x)) (sym +-inv) ⟩
      𝟘 * x + (𝟘 * x + (- (𝟘 * x)))
    ≡⟨ sym +-assoc ⟩
      (𝟘 * x + 𝟘 * x) + (- (𝟘 * x))
    ≡⟨ cong (_+ (- (𝟘 * x))) (sym *-+-distr-l) ⟩
      (𝟘 + 𝟘) * x + (- (𝟘 * x))
    ≡⟨ cong (_+ (- (𝟘 * x))) (cong (_* x) +-neut-l) ⟩
      𝟘 * x + (- (𝟘 * x))
    ≡⟨ +-inv ⟩
      𝟘
    ∎

  𝟚 : R
  𝟚 = 𝟙 + 𝟙

  *-𝟚 : {x : R} → 𝟚 * x ≡ x + x
  *-𝟚 {x} =
      (𝟙 + 𝟙) * x
    ≡⟨ *-+-distr-l ⟩
      𝟙 * x + 𝟙 * x
    ≡⟨ cong (_+ (𝟙 * x)) *-neut-l ⟩
      x + 𝟙 * x
    ≡⟨ cong (_+_ x) *-neut-l ⟩
      x + x
    ∎

module GeometriaSinteticaDiferencial (Anillo : AnilloConmutativo) where
  open AnilloConmutativo Anillo
  open TeoríaDeAnillos Anillo

  esPendiente0 : (R → R) → R → Set   
  esPendiente0 f a = {ε : R}
                   → ε * ε ≡ 𝟘
                   → f ε ≡ f 𝟘 + a * ε

  postulate pendiente0 : (R → R) → R
  postulate Kock-Lawvere0 : {f : R → R} → esPendiente0 f (pendiente0 f)
  postulate Kock-Lawvere0-uniq : {f : R → R} {a : R} → esPendiente0 f a → a ≡ pendiente0 f

  postulate 1/𝟚 : R
  postulate 1/𝟚-inv : 1/𝟚 * 𝟚 ≡ 𝟙

  ----

  trasladar : R → (R → R) → (R → R)
  trasladar x0 f = λ x → f (x0 + x)

  pendiente : R → (R → R) → R
  pendiente x0 f = pendiente0 (trasladar x0 f)

  esPendiente : R → (R → R) → R → Set
  esPendiente x0 f a = {ε : R}
                     → ε * ε ≡ 𝟘
                     → f (x0 + ε) ≡ f x0 + a * ε

  Kock-Lawvere : {x0 : R} {f : R → R}
               → esPendiente x0 f (pendiente x0 f)
  Kock-Lawvere {x0} {f} {ε} ε-inf =
      f (x0 + ε)
    ≡⟨ refl ⟩
      trasladar x0 f ε
    ≡⟨ Kock-Lawvere0 ε-inf ⟩
      trasladar x0 f 𝟘 + pendiente0 (trasladar x0 f) * ε
    ≡⟨ refl ⟩
      f (x0 + 𝟘) + pendiente x0 f * ε
    ≡⟨ cong (_+ (pendiente x0 f * ε)) (cong f +-neut-r) ⟩
      f x0 + pendiente x0 f * ε
    ∎

  Kock-Lawvere-uniq : {x0 : R} {f : R → R} {a : R}
                    → esPendiente x0 f a
                    → a ≡ pendiente x0 f
  Kock-Lawvere-uniq {x0} {f} {a} a-pend =
        a
      ≡⟨ Kock-Lawvere0-uniq {trasladar x0 f} lema ⟩
        pendiente0 (trasladar x0 f)
      ≡⟨ refl ⟩
        pendiente x0 f
      ∎
    where
      lema : {ε : R} → ε * ε ≡ 𝟘
           → trasladar x0 f ε ≡ trasladar x0 f 𝟘 + a * ε
      lema {ε} ε-inf =
          trasladar x0 f ε
        ≡⟨ refl ⟩
          f (x0 + ε)
        ≡⟨ a-pend ε-inf ⟩
          f x0 + a * ε
        ≡⟨ cong (_+ (a * ε)) (cong f (sym +-neut-r)) ⟩
          f (x0 + 𝟘) + a * ε
        ≡⟨ refl ⟩
          trasladar x0 f 𝟘 + a * ε
        ∎

  esÁrea : ((R → R) → R → R) → Set
  esÁrea área = {ε : R}
              → ε * ε ≡ 𝟘
              → {f : R → R} {x : R}
              → área f (x + ε) ≡ área f x
                               + 1/𝟚 * ε * (f x + f (x + ε))

  TFC : {área : (R → R) → R → R} {f : R → R}
      → esÁrea área
      → {x0 : R}
      → pendiente x0 (área f) ≡ f x0
  TFC {área} {f} área-es-área {x0} =
    sym (Kock-Lawvere0-uniq λ {ε} ε-inf →
      begin
        área f (x0 + ε)
      ≡⟨ área-es-área ε-inf ⟩
        área f x0 + (1/𝟚 * (ε * (f x0 + f (x0 + ε))))
      ≡⟨ cong (λ ■ → área f x0 + (1/𝟚 * (ε * (f x0 + ■))))
              (Kock-Lawvere {x0} {f} ε-inf) ⟩
        área f x0 + (1/𝟚 * (ε * (f x0 + (f x0 + (pendiente x0 f * ε)))))
      ≡⟨ cong (_+_ (área f x0)) (lema ε-inf) ⟩
        área f x0 + f x0 * ε
      ≡⟨ cong (_+ (f x0 * ε)) (cong (área f) (sym +-neut-r)) ⟩
        área f (x0 + 𝟘) + f x0 * ε
      ∎)
    where
      lema : {ε : R} (ε-inf : ε * ε ≡ 𝟘)
           → 1/𝟚 * (ε * (f x0 + (f x0 + (pendiente x0 f * ε)))) ≡ f x0 * ε
      lema {ε} ε-inf =
        begin
          1/𝟚 * (ε * (f x0 + (f x0 + (pendiente x0 f * ε))))
        ≡⟨ cong (_*_ 1/𝟚) *-+-distr-r ⟩
          1/𝟚 * (ε * f x0 + ε * (f x0 + (pendiente x0 f * ε)))
        ≡⟨ cong (λ ■ → 1/𝟚 * (ε * f x0 + ■)) *-+-distr-r ⟩
          1/𝟚 * (ε * f x0 + ε * f x0 + ε * pendiente x0 f * ε)
        ≡⟨ cong (λ ■ → 1/𝟚 * (ε * f x0 + ε * f x0 + ε * ■)) *-comm ⟩
          1/𝟚 * (ε * f x0 + ε * f x0 + ε * ε * pendiente x0 f)
        ≡⟨ cong (λ ■ → 1/𝟚 * (ε * f x0 + ε * f x0 + ■)) (sym *-assoc) ⟩
          1/𝟚 * (ε * f x0 + ε * f x0 + (ε * ε) * pendiente x0 f)
        ≡⟨ cong (λ ■ → 1/𝟚 * (ε * f x0 + ε * f x0 + ■ * pendiente x0 f)) ε-inf ⟩
          1/𝟚 * (ε * f x0 + ε * f x0 + 𝟘 * pendiente x0 f)
        ≡⟨ cong (λ ■ → 1/𝟚 * (ε * f x0 + ε * f x0 + ■)) *-𝟘 ⟩
          1/𝟚 * (ε * f x0 + ε * f x0 + 𝟘)
        ≡⟨ cong (λ ■ → 1/𝟚 * (ε * f x0 + ■)) +-neut-r ⟩
          1/𝟚 * (ε * f x0 + ε * f x0)
        ≡⟨ cong (λ ■ → 1/𝟚 * ■) (sym *-+-distr-l) ⟩
          1/𝟚 * (ε + ε) * f x0
        ≡⟨ cong (λ ■ → 1/𝟚 * ■ * f x0) (sym *-𝟚) ⟩
          1/𝟚 * (𝟚 * ε) * f x0
        ≡⟨ sym *-assoc ⟩
          (1/𝟚 * (𝟚 * ε)) * f x0
        ≡⟨ cong (_* (f x0)) (sym *-assoc) ⟩
          ((1/𝟚 * 𝟚) * ε) * f x0
        ≡⟨ cong (_* (f x0)) (cong (_* ε) 1/𝟚-inv) ⟩
          (𝟙 * ε) * f x0
        ≡⟨ cong (_* (f x0)) *-neut-l ⟩
          ε * f x0
        ≡⟨ *-comm ⟩
          f x0 * ε
        ∎
