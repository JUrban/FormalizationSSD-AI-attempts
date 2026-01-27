{-# OPTIONS --cubical --guardedness #-}

module work where

-- =============================================================================
-- Formalization of "A Foundation for Synthetic Stone Duality"
-- Based on main-monolithic.tex
-- =============================================================================

-- Basic imports from Cubical Agda library
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

-- =============================================================================
-- Section 1: Preliminaries and Basic Definitions
-- =============================================================================

-- A binary sequence is a function from ℕ to Bool (2)
binarySequence : Type₀
binarySequence = ℕ → Bool

-- The type 2^ℕ is the Cantor space (see Example iii in the paper)
CantorSpace : Type₀
CantorSpace = binarySequence

-- Biconditional (logical equivalence)
_↔_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

infixr 3 _↔_

-- =============================================================================
-- Section 2: Open and Closed Propositions (Definition from tex file)
-- =============================================================================

-- Definition: A proposition P is open if there exists α : 2^ℕ such that
-- P ↔ ∃ n : ℕ, α n = true (equivalently, α n = 1)

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = Σ[ α ∈ binarySequence ] (⟨ P ⟩ → Σ[ n ∈ ℕ ] α n ≡ true) × (Σ[ n ∈ ℕ ] α n ≡ true → ⟨ P ⟩)

-- Definition: A proposition P is closed if there exists α : 2^ℕ such that
-- P ↔ ∀ n : ℕ, α n = false (equivalently, α n = 0)

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = Σ[ α ∈ binarySequence ] (⟨ P ⟩ → ((n : ℕ) → α n ≡ false)) × (((n : ℕ) → α n ≡ false) → ⟨ P ⟩)

-- The type of open propositions
Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

-- The type of closed propositions
Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P

-- =============================================================================
-- Section 3: Basic properties of Open and Closed propositions
-- =============================================================================

-- Helper to construct the negation as an hProp
¬hProp : hProp ℓ-zero → hProp ℓ-zero
¬hProp P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

-- The negation of an open proposition is closed
-- If P ↔ ∃ n, α n = true, then ¬P ↔ ∀ n, α n = false

negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬hProp P)
negOpenIsClosed P (α , P→∃ , ∃→P) = α , forward , backward
  where
  forward : ¬ ⟨ P ⟩ → (n : ℕ) → α n ≡ false
  forward ¬p n with α n =B true
  ... | yes αn=t = ex-falso (¬p (∃→P (n , αn=t)))
  ... | no αn≠t = ¬true→false (α n) αn≠t

  backward : ((n : ℕ) → α n ≡ false) → ¬ ⟨ P ⟩
  backward all-false p with P→∃ p
  ... | (n , αn=t) = false≢true (sym (all-false n) ∙ αn=t)

-- Every decidable proposition is open
decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = (λ _ → true) , (λ _ → 0 , refl) , (λ _ → p)
decIsOpen P (no ¬p) = (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , (λ x → ex-falso (false≢true (snd x)))

-- Every decidable proposition is closed
decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = (λ _ → false) , (λ _ _ → refl) , (λ _ → p)
decIsClosed P (no ¬p) = (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , (λ f → ex-falso (true≢false (f 0)))

-- =============================================================================
-- Section 4: Stone Spaces and Stone Duality Axiom
-- =============================================================================

-- Recall from Axioms.StoneDuality:
-- Stone = TypeWithStr ℓ-zero hasStoneStr
-- where hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S
--
-- The Stone Duality Axiom states that for all B : Booleω,
-- the evaluation map B → 2^(Sp B) is an isomorphism.

-- =============================================================================
-- Section 5: Key Lemmas connecting Stone Duality and Open/Closed propositions
-- =============================================================================

-- Lemma (ClosedPropAsSpectrum from tex):
-- Given α : 2^ℕ, we have:
-- (∀ n : ℕ, α n = false) ↔ Sp(2/(α_n)_{n:ℕ})
--
-- The proof uses that there is only one Boolean morphism 2 → 2,
-- and it satisfies x(α_n) = 0 for all n iff α_n = 0 for all n.

-- =============================================================================
-- Section 6: Markov's Principle (MP)
--
-- For all α : 2^ℕ, we have:
-- ¬(∀ n : ℕ, α n = false) → Σ[ n ∈ ℕ ] α n = true
-- =============================================================================

-- Markov's Principle type
MarkovPrinciple : Type₀
MarkovPrinciple = (α : binarySequence) → ¬ ((n : ℕ) → α n ≡ false) → Σ[ n ∈ ℕ ] α n ≡ true

-- =============================================================================
-- Section 7: ¬WLPO (Negation of Weak Limited Principle of Omniscience)
--
-- ¬ ∀ α : 2^ℕ, ((∀ n, α n = false) ∨ ¬(∀ n, α n = false))
--
-- This is proved in WLPO.agda using Stone Duality
-- =============================================================================

-- Type for WLPO
WLPO : Type₀
WLPO = (α : binarySequence) → Dec ((n : ℕ) → α n ≡ false)

-- ¬WLPO follows from Stone Duality (proved in WLPO.agda)
-- The key insight is that any decidable property of binary sequences
-- is determined by a finite prefix of fixed length.

-- =============================================================================
-- Section 8: LLPO (Lesser Limited Principle of Omniscience)
--
-- For all α : ℕ_∞ (sequences hitting 1 at most once),
-- (∀ k, α_{2k} = 0) ∨ (∀ k, α_{2k+1} = 0)
-- =============================================================================

-- ℕ_∞ is the type of sequences hitting true at most once
-- This corresponds to Sp(B_∞) where B_∞ is generated by (g_n)
-- with relations g_m ∧ g_n = 0 for m ≠ n

-- A sequence hits true at most once
hitsAtMostOnce : binarySequence → Type₀
hitsAtMostOnce α = (m n : ℕ) → α m ≡ true → α n ≡ true → m ≡ n

-- The type ℕ_∞
ℕ∞ : Type₀
ℕ∞ = Σ[ α ∈ binarySequence ] hitsAtMostOnce α

-- Statement of LLPO
LLPO : Type₀
LLPO = (α : ℕ∞) → ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false)

-- =============================================================================
-- End of current formalization
-- TODO: Continue with more theorems from the paper
-- =============================================================================


