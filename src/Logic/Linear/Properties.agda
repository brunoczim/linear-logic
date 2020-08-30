module Logic.Linear.Properties where

open import Logic.Linear using 
  (LinearProp; _⊢_; Proof
  ; _^⊥; _⊗_; _⊕_; _&_; _⅋_; _⊸_; _≡_; e!_; e?_
  ; ^⊥-i; ⊗-i; ⊕-i₁; ⊕-i₂; &-i; ⅋-i; e?-i₂; e!-i; e?-e; swap
  )
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; _++_; map)

one : {n : ℕ} → Fin (suc (suc n))
one = suc zero
two : {n : ℕ} → Fin (suc (suc (suc n)))
two = suc one

-- Proof of distributivity of _⊗_ over _⊕_: p ⊗ (q ⊕ r) ≡ p ⊗ q ⊕ p ⊗ r.
⊕⊗-dist : ∀ {a}
          {A : Set a}
          (S : LinearProp A → Set a)
          {p q r : LinearProp A} →
          Proof S (p ⊗ (q ⊕ r) ≡ p ⊗ q ⊕ p ⊗ r)
⊕⊗-dist {_} {_} S {p} {q} {r} = &-i left⊸right right⊸left where
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

e!-iso : ∀ {a}
         {A : Set a}
         (S : LinearProp A → Set a)
         {p q : LinearProp A} →
         Proof S (e! (p & q) ≡ e! p ⊗ e! q)
e!-iso {_} {_} S {p} {q} = &-i left⊸right right⊸left where
  left⊸right : S ⊢ (e! (p & q) ⊸ e! p ⊗ e! q ∷ [])
  left⊸right = ⅋-i (e?-e (swap zero two conj)) where
    p-side : S ⊢ (p ∷ e? (p ^⊥ ⊕ q ^⊥) ∷ [])
    p-side = swap zero one (e?-i₂ disj) where
      disj : S ⊢ (p ^⊥ ⊕ q ^⊥ ∷ p ∷ [])
      disj = ⊕-i₁ (swap zero one (^⊥-i p))
    q-side : S ⊢ (q ∷ e? (p ^⊥ ⊕ q ^⊥) ∷ [])
    q-side = swap zero one (e?-i₂ disj) where
      disj : S ⊢ (p ^⊥ ⊕ q ^⊥ ∷ q ∷ [])
      disj = ⊕-i₂ (swap zero one (^⊥-i q))
    conj : S ⊢ (e! p ⊗ e! q ∷ e? (p ^⊥ ⊕ q ^⊥) ∷ e? (p ^⊥ ⊕ q ^⊥) ∷ [])
    conj = ⊗-i (e!-i p-side) (e!-i q-side)
  right⊸left : S ⊢ (e! p ⊗ e! q ⊸ e! (p & q) ∷ [])
  right⊸left = {!!}
