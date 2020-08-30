module Logic.Linear.Properties where

open import Logic.Linear using (LinearProp; _⊢_; Proof
                               ; _^⊥; _⊗_; _⊕_; _&_; _⅋_; _⊸_; _≡_
                               ; ^⊥-i; ⊗-i; ⊕-i₁; ⊕-i₂; &-i; ⅋-i; swap
                               )
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; _++_; map)

-- Proof of distributivity of _⊗_ over _⊕_: p ⊗ (q ⊕ r) ≡ p ⊗ q ⊕ p ⊗ r.
⊕⊗-dist : ∀ {a}
          {A : Set a}
          (S : LinearProp A → Set a)
          {p q r : LinearProp A} →
          Proof S (p ⊗ (q ⊕ r) ≡ p ⊗ q ⊕ p ⊗ r)
⊕⊗-dist {_} {_} S {p} {q} {r} = &-i left⊸right right⊸left where
  one : {n : ℕ} → Fin (suc (suc n))
  one = suc zero
  two : {n : ℕ} → Fin (suc (suc (suc n)))
  two = suc one
  left⊸right : S ⊢ (p ⊗ (q ⊕ r) ⊸ p ⊗ q ⊕ p ⊗ r ∷ [])
  left⊸right = ⅋-i (⅋-i (swap zero one q&r)) where
    q&r : S ⊢ (q ^⊥ & r ^⊥ ∷ p ^⊥ ∷ p ⊗ q ⊕ p ⊗ r ∷ [])
    q&r = &-i q-side r-side where
      q-side : S ⊢ (q ^⊥ ∷ p ^⊥ ∷ p ⊗ q ⊕ p ⊗ r ∷ [])
      q-side = swap one two (swap zero one disj)
        where
          conj : S ⊢ (p ⊗ q ∷ p ^⊥ ∷ q ^⊥ ∷ [])
          conj = ⊗-i (^⊥-i p) (^⊥-i q)
          disj : S ⊢ (p ⊗ q ⊕ p ⊗ r ∷ q ^⊥ ∷ p ^⊥ ∷ [])
          disj = ⊕-i₁ (swap one two conj)
      r-side : S ⊢ (r ^⊥ ∷ p ^⊥ ∷ p ⊗ q ⊕ p ⊗ r ∷ [])
      r-side = swap one two (swap zero one disj)
        where
          conj : S ⊢ (p ⊗ r ∷ p ^⊥ ∷ r ^⊥ ∷ [])
          conj = ⊗-i (^⊥-i p) (^⊥-i r)
          disj : S ⊢ (p ⊗ q ⊕ p ⊗ r ∷ r ^⊥ ∷ p ^⊥ ∷ [])
          disj = ⊕-i₂ (swap one two conj)
  right⊸left : S ⊢ (p ⊗ q ⊕ p ⊗ r ⊸ p ⊗ (q ⊕ r) ∷ [])
  right⊸left = ⅋-i (&-i q-side r-side) where
    q-side : S ⊢ (p ^⊥ ⅋ q ^⊥ ∷ p ⊗ (q ⊕ r) ∷ [])
    q-side = ⅋-i (swap one two (swap zero one conj)) where
      disj : S ⊢ (q ⊕ r ∷ q ^⊥ ∷ [])
      disj = ⊕-i₁ (^⊥-i q)
      conj : S ⊢ (p ⊗ (q ⊕ r) ∷ p ^⊥ ∷ q ^⊥ ∷ [])
      conj = ⊗-i (^⊥-i p) disj
    r-side : S ⊢ (p ^⊥ ⅋ r ^⊥ ∷ p ⊗ (q ⊕ r) ∷ [])
    r-side = ⅋-i (swap one two (swap zero one conj)) where
      disj : S ⊢ (q ⊕ r ∷ r ^⊥ ∷ [])
      disj = ⊕-i₂ (^⊥-i r)
      conj : S ⊢ (p ⊗ (q ⊕ r) ∷ p ^⊥ ∷ r ^⊥ ∷ [])
      conj = ⊗-i (^⊥-i p) disj
