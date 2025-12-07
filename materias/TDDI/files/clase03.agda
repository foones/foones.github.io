open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<_; _<?_; _∸_)
open import Data.Product
  using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary
   using (yes; no)

div-mod : (n m : ℕ)
        → 0 < m
        → Σ[ q ∈ ℕ ] Σ[ r ∈ ℕ ]
            ((q * m + r ≡ n) × (r < m))
div-mod n m 0<m with n <? m
... | yes p = zero , n , refl , p
... | no  q =
      let (q' , r' , q'*m+r'≡n' , r'<m) =
              div-mod (n ∸ m) m 0<m
       in suc q'
        , r'
        , {!!}
        , r'<m
