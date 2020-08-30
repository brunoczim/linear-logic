module Logic.Linear where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; _++_; map)
open import Data.Empty using (⊥)

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

-- Swaps two elements with two given positions. Just a helper of `swap`.
swap-vec : ∀ {a} {A : Set a}
          {n : ℕ} →
          Fin n →
          Fin n →
          Vec A n →
          Vec A n
swap-vec = do-swap where
  insert : ∀ {a} {A : Set a}
              {n : ℕ} →
              A → 
              Vec A (suc n) →
              Vec A (suc (suc n))
  insert y (x ∷ xs) = x ∷ y ∷ xs
  swap-first : ∀ {a} {A : Set a}
              {n : ℕ} →
              Fin n →
              Vec A n →
              Vec A n
  swap-first zero xs = xs
  swap-first (suc zero) (x ∷ y ∷ xs) = y ∷ x ∷ xs
  swap-first (suc m) (x ∷ y ∷ xs) = insert y (swap-first m (x ∷ xs))
  do-swap : ∀ {a} {A : Set a}
            {n : ℕ} →
            Fin n →
            Fin n →
            Vec A n →
            Vec A n
  do-swap zero zero xs = xs
  do-swap zero (suc m) xs = swap-first (suc m) xs 
  do-swap (suc m) zero xs = swap-first (suc m) xs 
  do-swap (suc k) (suc m) (x ∷ xs) = x ∷ do-swap k m xs

-- List of inference rules.
-- The S parameter is an axiom scheme.
-- To prove somthing, it must be the only proposition in the sequent.
data _⊢_ {a}
         {A : Set a}
         (S : LinearProp A → Set a) :
         {n : ℕ} →
         Vec (LinearProp A) n
         → Set a
         where

  empty : S ⊢ []

  axiom : {p : LinearProp A} → S p → S ⊢ (p ∷ [])

  swap : {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         (i j : Fin n) →
         S ⊢ ps →
         S ⊢ (swap-vec i j ps)

  ^⊥-i : (p : LinearProp A) → S ⊢ (p ∷ p ^⊥ ∷ [])

  ^⊥-e : {p : LinearProp A}
        {m n : ℕ}
        {ps : Vec (LinearProp A) m} →
        {qs : Vec (LinearProp A) n} →
        S ⊢ (p ∷ ps) →
        S ⊢ (p ^⊥ ∷ qs) →
        S ⊢ (ps ++ qs)

  ⊗-i : {p q : LinearProp A}
        {m n : ℕ}
        {ps : Vec (LinearProp A) m} →
        {qs : Vec (LinearProp A) n} →
        S ⊢ (p ∷ ps) →
        S ⊢ (q ∷ qs) →
        S ⊢ (p ⊗ q ∷ ps ++ qs)

  ⅋-i : {p q : LinearProp A}
        {n : ℕ}
        {ps : Vec (LinearProp A) n} →
        S ⊢ (p ∷ q ∷ ps) →
        S ⊢ (p ⅋ q ∷ ps)

  u1-i : S ⊢ (u1 ∷ [])

  u⊥-i : {n : ℕ} {ps : Vec (LinearProp A) n} → S ⊢ ps →  S ⊢ (u⊥ ∷ ps)

  &-i : {p q : LinearProp A}
        {n : ℕ}
        {ps : Vec (LinearProp A) n} →
        S ⊢ (p ∷ ps) →
        S ⊢ (q ∷ ps) →
        S ⊢ (p & q ∷ ps)

  ⊕-i₁ : {p q : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         S ⊢ (p ∷ ps) →
         S ⊢ (p ⊕ q ∷ ps)

  ⊕-i₂ : {p q : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         S ⊢ (p ∷ ps) →
         S ⊢ (q ⊕ p ∷ ps)

  u⊤-i : {n : ℕ}
        {ps : Vec (LinearProp A) n} →
        S ⊢ (u⊤ ∷ ps)
 
  e?-i₁ : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         S ⊢ ps →
         S ⊢ (e? p ∷ ps)
         
  e?-i₂ : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         S ⊢ (p ∷ ps) →
         S ⊢ (e? p ∷ ps)

  e?-e : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         S ⊢ (e? p ∷ e? p ∷ ps) →
         S ⊢ (e? p ∷ ps)

  e!-i : {p : LinearProp A}
         {n : ℕ}
         {ps : Vec (LinearProp A) n} →
         S ⊢ (p ∷ map e?_ ps) →
         S ⊢ (e! p ∷ map e?_ ps)

-- Empty axiom scheme.
data NoAxioms {a} {A : Set a} : LinearProp A → Set a where

-- Just a helper to hint something has been proven.
Proof : ∀ {a} {A : Set a} → (LinearProp A → Set a) → LinearProp A → Set a
Proof S p = S ⊢ (p ∷ [])
