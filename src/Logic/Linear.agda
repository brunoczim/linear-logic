module Logic.Linear where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; _++_; map)

-- Operator precedences.
infix 10 _^⊥ e?_ e!_
infixl 9 _⊗_ _&_
infixl 8 _⊕_ _⅋_
infixl 7 _⊸_
infixl 6 _≡_

-- Primitive linear propositions.
data LinearProp {a} (A : Set a) : Set a where
  atom : A → LinearProp A
  atom^⊥ : A → LinearProp A
  _⊗_ : LinearProp A → LinearProp A → LinearProp A
  _⊕_ : LinearProp A → LinearProp A → LinearProp A
  _&_ : LinearProp A → LinearProp A → LinearProp A
  _⅋_ : LinearProp A → LinearProp A → LinearProp A
  u0 : LinearProp A
  u1 : LinearProp A
  u⊥ : LinearProp A
  u⊤ : LinearProp A
  e!_ : LinearProp A → LinearProp A
  e?_ : LinearProp A → LinearProp A

-- The equivalent of the propositional negation, called "dual".
_^⊥ : ∀ {a} {A : Set a} → LinearProp A → LinearProp A
(atom p) ^⊥ = atom^⊥ p
(atom^⊥ p) ^⊥ = atom p
(p ⊗ q) ^⊥ = (p ^⊥) ⅋ (q ^⊥)
(p ⊕ q) ^⊥ = (p ^⊥) & (q ^⊥)
(p ⅋ q) ^⊥ = (p ^⊥) ⊗ (q ^⊥)
(p & q) ^⊥ = (p ^⊥) ⊕ (q ^⊥)
u1 ^⊥ = u⊥
u0 ^⊥ = u⊤
u⊥ ^⊥ = u1
u⊤ ^⊥ = u0
(e! p) ^⊥ = e? (p ^⊥)
(e? p) ^⊥ = e! (p ^⊥)

-- The linear implication, also called "lollipop operator".
_⊸_ : ∀ {a} {A : Set a} → LinearProp A → LinearProp A → LinearProp A
p ⊸ q = p ^⊥ ⅋ q

-- The equivalent of the propositional equivalence (lmao).
_≡_ : ∀ {a} {A : Set a} → LinearProp A → LinearProp A → LinearProp A
p ≡ q = (p ⊸ q) & (q ⊸ p)

-- Swaps the first element with a given position. Just a helper of `swap`.
swap-vec-first : ∀ {a} {A : Set a}
               {n : ℕ} →
               Fin n →
               Vec A n →
               Vec A n
swap-vec-first zero xs = xs
swap-vec-first (suc m) (x ∷ y ∷ xs) = y ∷ swap-vec-first m (x ∷ xs)

-- Swaps two elements with two given positions. Just a helper of `swap`.
swap-vec : ∀ {a} {A : Set a}
          {n : ℕ} →
          Fin n →
          Fin n →
          Vec A n →
          Vec A n
swap-vec zero zero xs = xs
swap-vec zero (suc m) xs = swap-vec-first (suc m) xs 
swap-vec (suc m) zero xs = swap-vec-first (suc m) xs 
swap-vec (suc k) (suc m) (x ∷ xs) = x ∷ swap-vec k m xs

-- List of inference rules.
-- To prove somthing, it must be the only proposition in the sequent.
data ⊢ {a} {A : Set a} : {n : ℕ} → Vec (LinearProp A) n → Set a where
  swap : {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         (i j : Fin n) →
         ⊢ ps →
         ⊢ (swap-vec i j ps)

  ^⊥-i : (p : LinearProp A) → ⊢ (p ∷ p ^⊥ ∷ [])

  ^⊥-e : {p : LinearProp A}
        {m n : ℕ}
        {ps : Vec (LinearProp A) m} →
        {qs : Vec (LinearProp A) n} →
        ⊢ (p ∷ ps) →
        ⊢ (p ^⊥ ∷ qs) →
        ⊢ (ps ++ qs)

  ⊗-i : {p q : LinearProp A}
        {m n : ℕ}
        {ps : Vec (LinearProp A) m} →
        {qs : Vec (LinearProp A) n} →
        ⊢ (p ∷ ps) →
        ⊢ (q ∷ qs) →
        ⊢ (p ⊗ q ∷ ps ++ qs)

  ⅋-i : {p q : LinearProp A}
        {n : ℕ}
        {ps : Vec (LinearProp A) n} →
        ⊢ (p ∷ q ∷ ps) →
        ⊢ (p ⅋ q ∷ ps)

  u1-i : ⊢ (u1 ∷ [])

  u⊥-i : {n : ℕ} {ps : Vec (LinearProp A) n} → ⊢ ps →  ⊢ (u⊥ ∷ ps)

  &-i : {p q : LinearProp A}
        {n : ℕ}
        {ps : Vec (LinearProp A) n} →
        ⊢ (p ∷ ps) →
        ⊢ (q ∷ ps) →
        ⊢ (p & q ∷ ps)

  ⊕-i₁ : {p q : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         ⊢ (p ∷ ps) →
         ⊢ (p ⊕ q ∷ ps)

  ⊕-i₂ : {p q : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         ⊢ (p ∷ ps) →
         ⊢ (q ⊕ p ∷ ps)

  u⊤-i : {n : ℕ}
        {ps : Vec (LinearProp A) n} →
        ⊢ (u⊤ ∷ ps)
 
  e?-i₁ : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         ⊢ ps →
         ⊢ (e? p ∷ ps)
         
  e?-i₂ : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         ⊢ (p ∷ ps) →
         ⊢ (e? p ∷ ps)

  e?-e : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         ⊢ (e? p ∷ e? p ∷ ps) →
         ⊢ (e? p ∷ ps)

  e!-i : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         ⊢ (p ∷ map e?_ ps) →
         ⊢ (e! p ∷ ps)

-- Just a helper to hint something has been proven.
Proof : ∀ {a} {A : Set a} → LinearProp A → Set a
Proof p = ⊢ (p ∷ [])
