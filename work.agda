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
open import Cubical.Data.Nat.Properties using (discreteℕ)
import Cubical.Induction.WellFounded as WF
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

-- Note: Axioms.StoneDuality import removed due to library issues
-- The key definitions are provided locally below

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

-- Note: isOpenProp P is NOT a proposition (multiple witnesses possible),
-- but it IS a set since binarySequence is a set.

isSetBinarySequence : isSet binarySequence
isSetBinarySequence = isSetΠ (λ _ → isSetBool)

isSetIsOpenProp : (P : hProp ℓ-zero) → isSet (isOpenProp P)
isSetIsOpenProp P = isSetΣ isSetBinarySequence
  (λ α → isSet× (isSetΠ (λ _ → isSetΣ isSetℕ (λ n → isProp→isSet (isSetBool _ _))))
                 (isSetΠ (λ _ → isProp→isSet (snd P))))

isSetIsClosedProp : (P : hProp ℓ-zero) → isSet (isClosedProp P)
isSetIsClosedProp P = isSetΣ isSetBinarySequence
  (λ α → isSet× (isProp→isSet (isPropΠ (λ _ → isPropΠ (λ _ → isSetBool _ _))))
                 (isProp→isSet (isPropΠ (λ _ → snd P))))

-- The property version: P merely has an openness witness
-- This is the "exists α such that P ↔ ∃n. αn = true" formulation
isOpen : hProp ℓ-zero → hProp ℓ-zero
isOpen P = ∥ isOpenProp P ∥₁ , squash₁

isClosed : hProp ℓ-zero → hProp ℓ-zero
isClosed P = ∥ isClosedProp P ∥₁ , squash₁

-- Projections from Open and Closed
openProp : Open → hProp ℓ-zero
openProp = fst

closedProp : Closed → hProp ℓ-zero
closedProp = fst

-- The underlying type of an open/closed proposition
openType : Open → Type₀
openType O = ⟨ fst O ⟩

closedType : Closed → Type₀
closedType C = ⟨ fst C ⟩

-- Coercion: Open includes into hProp
open→hProp : Open → hProp ℓ-zero
open→hProp = fst

-- Coercion: Closed includes into hProp
closed→hProp : Closed → hProp ℓ-zero
closed→hProp = fst

-- ⊥ and ⊤ as Open/Closed (defined later: ⊥-isOpen, ⊤-isOpen, ⊥-isClosed, ⊤-isClosed)
-- Meet (∧) and Join (∨) operations on Open/Closed are defined after the basic lemmas

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

-- ⊥ (false) is both open and closed
⊥-hProp : hProp ℓ-zero
⊥-hProp = ⊥ , isProp⊥

⊥-isOpen : isOpenProp ⊥-hProp
⊥-isOpen = decIsOpen ⊥-hProp (no (λ x → x))

⊥-isClosed : isClosedProp ⊥-hProp
⊥-isClosed = decIsClosed ⊥-hProp (no (λ x → x))

-- ⊤ (true/Unit) is both open and closed
⊤-hProp : hProp ℓ-zero
⊤-hProp = Unit , (λ _ _ → refl)

⊤-isOpen : isOpenProp ⊤-hProp
⊤-isOpen = decIsOpen ⊤-hProp (yes tt)

⊤-isClosed : isClosedProp ⊤-hProp
⊤-isClosed = decIsClosed ⊤-hProp (yes tt)

-- Bundled versions: ⊥ and ⊤ as elements of Open and Closed
⊥-Open : Open
⊥-Open = ⊥-hProp , ⊥-isOpen

⊥-Closed : Closed
⊥-Closed = ⊥-hProp , ⊥-isClosed

⊤-Open : Open
⊤-Open = ⊤-hProp , ⊤-isOpen

⊤-Closed : Closed
⊤-Closed = ⊤-hProp , ⊤-isClosed

-- Canonical closed proposition: (∀n. α n ≡ false) is closed with witness α
-- This is the defining property of closed propositions
allFalseIsClosed : (α : binarySequence) → isClosedProp (((n : ℕ) → α n ≡ false) , isPropΠ (λ n → isSetBool (α n) false))
allFalseIsClosed α = α , (λ p → p) , (λ p → p)

-- Canonical open proposition: (∃n. α n ≡ true) is open with witness α
-- This is the defining property of open propositions
-- Note: someTrueIsOpen is defined after the mp postulate (requires MP)

-- Equality in Bool is decidable (hence both open and closed)
Bool-equality-decidable : (a b : Bool) → Dec (a ≡ b)
Bool-equality-decidable = _=B_

Bool-equality-open : (a b : Bool) → isOpenProp ((a ≡ b) , isSetBool a b)
Bool-equality-open a b = decIsOpen ((a ≡ b) , isSetBool a b) (Bool-equality-decidable a b)

Bool-equality-closed : (a b : Bool) → isClosedProp ((a ≡ b) , isSetBool a b)
Bool-equality-closed a b = decIsClosed ((a ≡ b) , isSetBool a b) (Bool-equality-decidable a b)

-- Equality in ℕ is decidable (hence both open and closed)
ℕ-equality-decidable : (m n : ℕ) → Dec (m ≡ n)
ℕ-equality-decidable = discreteℕ

ℕ-equality-open : (m n : ℕ) → isOpenProp ((m ≡ n) , isSetℕ m n)
ℕ-equality-open m n = decIsOpen ((m ≡ n) , isSetℕ m n) (ℕ-equality-decidable m n)

ℕ-equality-closed : (m n : ℕ) → isClosedProp ((m ≡ n) , isSetℕ m n)
ℕ-equality-closed m n = decIsClosed ((m ≡ n) , isSetℕ m n) (ℕ-equality-decidable m n)

-- Equality in CantorSpace (= binarySequence = 2^ℕ) is closed
-- (Special case of: equality in Stone spaces is closed)
-- Proof: α = β ↔ ∀n. α n = β n (pointwise equality)
-- Each (α n = β n) is decidable (Bool has decidable equality)
-- So α = β is a countable conjunction of decidable propositions, hence closed.
CantorSpace-equality-closed : (α β : CantorSpace)
                             → isClosedProp ((α ≡ β) , isSetBinarySequence α β)
CantorSpace-equality-closed α β = γ , forward , backward
  where
  -- Witness: γ n = true iff α n ≠ β n
  γ : binarySequence
  γ n with α n =B β n
  ... | yes _ = false
  ... | no _ = true

  forward : α ≡ β → (n : ℕ) → γ n ≡ false
  forward α=β n with α n =B β n
  ... | yes _ = refl
  ... | no αn≠βn = ex-falso (αn≠βn (cong (λ f → f n) α=β))

  backward : ((n : ℕ) → γ n ≡ false) → α ≡ β
  backward all-false = funExt pointwise
    where
    pointwise : (n : ℕ) → α n ≡ β n
    pointwise n with α n =B β n | all-false n
    ... | yes αn=βn | _ = αn=βn
    ... | no _ | γn=f = ex-falso (true≢false γn=f)

-- Negation of decidable proposition is decidable
decNeg : {P : Type₀} → isProp P → Dec P → Dec (¬ P)
decNeg _ (yes p) = no (λ ¬p → ¬p p)
decNeg _ (no ¬p) = yes ¬p

-- Product of decidable propositions is decidable
decProd : {P Q : Type₀} → isProp P → isProp Q → Dec P → Dec Q → Dec (P × Q)
decProd _ _ (no ¬p) _ = no (λ pq → ¬p (fst pq))
decProd _ _ (yes _) (no ¬q) = no (λ pq → ¬q (snd pq))
decProd _ _ (yes p) (yes q) = yes (p , q)

-- Coproduct of decidable propositions is decidable (as ∥ P ⊎ Q ∥₁)
-- Note: Without truncation, P ⊎ Q is not a proposition
decCoprod : {P Q : Type₀} → isProp P → isProp Q → Dec P → Dec Q → Dec ∥ P ⊎ Q ∥₁
decCoprod _ _ (yes p) _ = yes ∣ inl p ∣₁
decCoprod _ _ (no _) (yes q) = yes ∣ inr q ∣₁
decCoprod _ _ (no ¬p) (no ¬q) = no (PT.rec isProp⊥ λ { (inl p) → ¬p p ; (inr q) → ¬q q })

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

-- hitsAtMostOnce is a proposition (it's a Π-type into ℕ which is a set)
isPropHitsAtMostOnce : (α : binarySequence) → isProp (hitsAtMostOnce α)
isPropHitsAtMostOnce α = isPropΠ λ m → isPropΠ λ n → isPropΠ λ _ → isPropΠ λ _ → isSetℕ m n

-- The type ℕ_∞
ℕ∞ : Type₀
ℕ∞ = Σ[ α ∈ binarySequence ] hitsAtMostOnce α

-- Statement of LLPO
LLPO : Type₀
LLPO = (α : ℕ∞) → ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false)

-- =============================================================================
-- Section 9: Additional properties of Open and Closed propositions
-- =============================================================================

-- The negation of a closed proposition is open (requires Markov's Principle)
-- If P ↔ ∀ n, α n = false, then ¬P ↔ ∃ n, α n = true

negClosedIsOpen : MarkovPrinciple → (P : hProp ℓ-zero) → isClosedProp P → isOpenProp (¬hProp P)
negClosedIsOpen mp P (α , P→∀ , ∀→P) = α , forward , backward
  where
  forward : ¬ ⟨ P ⟩ → Σ[ n ∈ ℕ ] α n ≡ true
  forward ¬p = mp α (λ all-false → ¬p (∀→P all-false))

  backward : Σ[ n ∈ ℕ ] α n ≡ true → ¬ ⟨ P ⟩
  backward (n , αn=t) p = true≢false (sym αn=t ∙ P→∀ p n)

-- Bundled negation: Open → Closed (negation of open is closed)
¬-Open : Open → Closed
¬-Open O = ¬hProp (fst O) , negOpenIsClosed (fst O) (snd O)

-- Bundled negation: Closed → Open (requires MP)
-- Note: ¬-Closed is defined after the mp postulate

-- ¬¬-stability of closed propositions
-- If P is closed, then ¬¬P → P
closedIsStable : (P : hProp ℓ-zero) → isClosedProp P → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
closedIsStable P (α , P→∀ , ∀→P) ¬¬p = ∀→P all-false
  where
  all-false : (n : ℕ) → α n ≡ false
  all-false n with α n =B true
  ... | yes αn=t = ex-falso (¬¬p (λ p → true≢false (sym αn=t ∙ P→∀ p n)))
  ... | no αn≠t = ¬true→false (α n) αn≠t

-- ¬¬-stability of open propositions (requires Markov's Principle)
-- If P is open, then ¬¬P → P
openIsStable : MarkovPrinciple → (P : hProp ℓ-zero) → isOpenProp P → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
openIsStable mp P (α , P→∃ , ∃→P) ¬¬p = ∃→P (mp α ¬all-false)
  where
  ¬all-false : ¬ ((n : ℕ) → α n ≡ false)
  ¬all-false all-false = ¬¬p (λ p → false≢true (sym (all-false (fst (P→∃ p))) ∙ snd (P→∃ p)))

-- Double negation of open proposition is open (requires MP)
-- P open → ¬P closed → ¬¬P open
¬¬hProp : hProp ℓ-zero → hProp ℓ-zero
¬¬hProp P = (¬ ¬ ⟨ P ⟩) , isProp¬ (¬ ⟨ P ⟩)

doubleNegOpenIsOpen : MarkovPrinciple → (P : hProp ℓ-zero) → isOpenProp P → isOpenProp (¬¬hProp P)
doubleNegOpenIsOpen mp P Popen = negClosedIsOpen mp (¬hProp P) (negOpenIsClosed P Popen)

-- Double negation of closed proposition is closed
-- P closed → ¬P open → ¬¬P closed
doubleNegClosedIsClosed : MarkovPrinciple → (P : hProp ℓ-zero) → isClosedProp P → isClosedProp (¬¬hProp P)
doubleNegClosedIsClosed mp P Pclosed = negOpenIsClosed (¬hProp P) (negClosedIsOpen mp P Pclosed)

-- =============================================================================
-- Section 10: Closure properties
-- =============================================================================

-- We use the pairing function from Cubical.Data.Nat to interleave sequences
-- For simplicity, we use a direct interleaving: γ (2k) = α k, γ (2k+1) = β k

-- Helper: extract the index from an interleaved sequence
private
  -- Given n, compute whether n = 2k (returning k) or n = 2k+1 (returning k)
  half : ℕ → ℕ
  half zero = zero
  half (suc zero) = zero
  half (suc (suc n)) = suc (half n)

  isEvenB : ℕ → Bool
  isEvenB zero = true
  isEvenB (suc zero) = false
  isEvenB (suc (suc n)) = isEvenB n

  -- 2 ·ℕ (suc k) = suc (suc (2 ·ℕ k))
  2·suc : (k : ℕ) → 2 ·ℕ (suc k) ≡ suc (suc (2 ·ℕ k))
  2·suc k = cong suc (+-suc k (k +ℕ zero))

  -- Key lemmas about isEvenB and half
  isEvenB-2k : (k : ℕ) → isEvenB (2 ·ℕ k) ≡ true
  isEvenB-2k zero = refl
  isEvenB-2k (suc k) = subst (λ n → isEvenB n ≡ true) (sym (2·suc k)) (isEvenB-2k k)

  isEvenB-2k+1 : (k : ℕ) → isEvenB (suc (2 ·ℕ k)) ≡ false
  isEvenB-2k+1 zero = refl
  isEvenB-2k+1 (suc k) = subst (λ n → isEvenB (suc n) ≡ false) (sym (2·suc k)) (isEvenB-2k+1 k)

  half-2k : (k : ℕ) → half (2 ·ℕ k) ≡ k
  half-2k zero = refl
  half-2k (suc k) = subst (λ n → half n ≡ suc k) (sym (2·suc k)) (cong suc (half-2k k))

  half-2k+1 : (k : ℕ) → half (suc (2 ·ℕ k)) ≡ k
  half-2k+1 zero = refl
  half-2k+1 (suc k) = subst (λ n → half (suc n) ≡ suc k) (sym (2·suc k)) (cong suc (half-2k+1 k))

  -- If n is even (isEvenB n ≡ true), then 2 · (half n) ≡ n
  2·half-even : (n : ℕ) → isEvenB n ≡ true → 2 ·ℕ (half n) ≡ n
  2·half-even zero _ = refl
  2·half-even (suc zero) even-f = ex-falso (false≢true even-f)
  2·half-even (suc (suc n)) even-ssn =
    2 ·ℕ (suc (half n))      ≡⟨ 2·suc (half n) ⟩
    suc (suc (2 ·ℕ (half n))) ≡⟨ cong (suc ∘ suc) (2·half-even n even-ssn) ⟩
    suc (suc n)              ∎

  -- If n is odd (isEvenB n ≡ false), then suc (2 · (half n)) ≡ n
  suc-2·half-odd : (n : ℕ) → isEvenB n ≡ false → suc (2 ·ℕ (half n)) ≡ n
  suc-2·half-odd zero odd-f = ex-falso (true≢false odd-f)
  suc-2·half-odd (suc zero) _ = refl
  suc-2·half-odd (suc (suc n)) odd-ssn =
    suc (2 ·ℕ (suc (half n)))      ≡⟨ cong suc (2·suc (half n)) ⟩
    suc (suc (suc (2 ·ℕ (half n)))) ≡⟨ cong (suc ∘ suc) (suc-2·half-odd n odd-ssn) ⟩
    suc (suc n)                    ∎

-- Interleave two sequences: γ(2k) = α(k), γ(2k+1) = β(k)
interleave : binarySequence → binarySequence → binarySequence
interleave α β n = if isEvenB n then α (half n) else β (half n)

-- Correctness of interleave
interleave-2k : (α β : binarySequence) (k : ℕ) → interleave α β (2 ·ℕ k) ≡ α k
interleave-2k α β k =
  interleave α β (2 ·ℕ k)          ≡⟨ refl ⟩
  (if isEvenB (2 ·ℕ k) then α (half (2 ·ℕ k)) else β (half (2 ·ℕ k)))
    ≡⟨ cong (λ x → if x then α (half (2 ·ℕ k)) else β (half (2 ·ℕ k))) (isEvenB-2k k) ⟩
  α (half (2 ·ℕ k))                ≡⟨ cong α (half-2k k) ⟩
  α k                              ∎

interleave-2k+1 : (α β : binarySequence) (k : ℕ) → interleave α β (suc (2 ·ℕ k)) ≡ β k
interleave-2k+1 α β k =
  interleave α β (suc (2 ·ℕ k))    ≡⟨ refl ⟩
  (if isEvenB (suc (2 ·ℕ k)) then α (half (suc (2 ·ℕ k))) else β (half (suc (2 ·ℕ k))))
    ≡⟨ cong (λ x → if x then α (half (suc (2 ·ℕ k))) else β (half (suc (2 ·ℕ k)))) (isEvenB-2k+1 k) ⟩
  β (half (suc (2 ·ℕ k)))          ≡⟨ cong β (half-2k+1 k) ⟩
  β k                              ∎

-- Generalized versions: given n and proof of evenness/oddness
interleave-even : (α β : binarySequence) (n : ℕ) → isEvenB n ≡ true
                 → interleave α β n ≡ α (half n)
interleave-even α β n n-even =
  interleave α β n
    ≡⟨ refl ⟩
  (if isEvenB n then α (half n) else β (half n))
    ≡⟨ cong (λ x → if x then α (half n) else β (half n)) n-even ⟩
  α (half n) ∎

interleave-odd : (α β : binarySequence) (n : ℕ) → isEvenB n ≡ false
                → interleave α β n ≡ β (half n)
interleave-odd α β n n-odd =
  interleave α β n
    ≡⟨ refl ⟩
  (if isEvenB n then α (half n) else β (half n))
    ≡⟨ cong (λ x → if x then α (half n) else β (half n)) n-odd ⟩
  β (half n) ∎

-- Closed propositions are closed under finite conjunction
closedAnd : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
          → isClosedProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
closedAnd P Q (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) = γ , forward , backward
  where
  γ : binarySequence
  γ = interleave α β

  forward : ⟨ P ⟩ × ⟨ Q ⟩ → (n : ℕ) → γ n ≡ false
  forward (p , q) n with isEvenB n =B true
  ... | yes even = subst (λ x → (if x then α (half n) else β (half n)) ≡ false) (sym even) (P→∀α p (half n))
  ... | no notEven = subst (λ x → (if x then α (half n) else β (half n)) ≡ false) (sym (¬true→false (isEvenB n) notEven)) (Q→∀β q (half n))

  backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ × ⟨ Q ⟩
  backward all-zero = (∀α→P α-zero) , (∀β→Q β-zero)
    where
    α-zero : (k : ℕ) → α k ≡ false
    α-zero k = sym (interleave-2k α β k) ∙ all-zero (2 ·ℕ k)

    β-zero : (k : ℕ) → β k ≡ false
    β-zero k = sym (interleave-2k+1 α β k) ∙ all-zero (suc (2 ·ℕ k))

-- Open propositions are closed under finite disjunction (requires Markov's Principle)
-- The forward direction needs MP to extract a concrete witness from ∥ P ⊎ Q ∥₁
openOrMP : MarkovPrinciple → (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
openOrMP mp P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = γ , forward , backward
  where
  γ : binarySequence
  γ = interleave α β

  backward : Σ[ n ∈ ℕ ] γ n ≡ true → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  backward (n , γn=t) with isEvenB n =B true
  ... | yes even = ∣ inl (∃α→P (half n , claim)) ∣₁
    where
    claim : α (half n) ≡ true
    claim = subst (λ x → (if x then α (half n) else β (half n)) ≡ true) even γn=t
  ... | no notEven = ∣ inr (∃β→Q (half n , claim)) ∣₁
    where
    claim : β (half n) ≡ true
    claim = subst (λ x → (if x then α (half n) else β (half n)) ≡ true) (¬true→false (isEvenB n) notEven) γn=t

  -- Use Markov to extract a witness from the double negation
  forward : ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ → Σ[ n ∈ ℕ ] γ n ≡ true
  forward truncPQ = mp γ ¬all-false
    where
    -- From ∥ P ⊎ Q ∥₁ and (∀n. γ n = false), we can derive a contradiction
    ¬all-false : ¬ ((n : ℕ) → γ n ≡ false)
    ¬all-false all-false = PT.rec isProp⊥ helper truncPQ
      where
      helper : ⟨ P ⟩ ⊎ ⟨ Q ⟩ → ⊥
      helper (inl p) =
        let (k , αk=t) = P→∃α p
        in false≢true (sym (sym (interleave-2k α β k) ∙ all-false (2 ·ℕ k)) ∙ αk=t)
      helper (inr q) =
        let (k , βk=t) = Q→∃β q
        in false≢true (sym (sym (interleave-2k+1 α β k) ∙ all-false (suc (2 ·ℕ k))) ∙ βk=t)

-- Non-truncated version: given definite knowledge P ⊎ Q, produce a concrete witness
openOrNonTrunc : (P Q : hProp ℓ-zero) (αP : isOpenProp P) (αQ : isOpenProp Q)
               → ⟨ P ⟩ ⊎ ⟨ Q ⟩ → Σ[ n ∈ ℕ ] interleave (fst αP) (fst αQ) n ≡ true
openOrNonTrunc P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) (inl p) =
  let (k , αk=t) = P→∃α p
  in (2 ·ℕ k) , (interleave-2k α β k ∙ αk=t)
openOrNonTrunc P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) (inr q) =
  let (k , βk=t) = Q→∃β q
  in suc (2 ·ℕ k) , (interleave-2k+1 α β k ∙ βk=t)

-- Markov's Principle follows from Stone Duality (proven in the library)
-- Proof sketch:
-- 1. If ¬(∀n. αn = false), then Sp(2/α) is empty (emptySp from Markov.agda)
-- 2. By Stone Duality (Sp is an embedding), Sp(2/α) = ∅ = Sp(trivial) ⟹ 2/α = trivial
-- 3. Hence 0 = 1 in 2/α, so true ∈ αI (trivialQuotient→1∈I)
-- 4. By t∈I→αn, this gives Σn. αn = true
postulate
  mp : MarkovPrinciple

-- Canonical open proposition: (∃n. α n ≡ true) is open with witness α
-- This is the defining property of open propositions
-- Note: We use the truncated version ∥ Σ n. α n ≡ true ∥₁ for the hProp
-- The forward direction uses MP to extract a witness from the truncated existential
someTrueIsOpen : (α : binarySequence) → isOpenProp ((∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁) , squash₁)
someTrueIsOpen α = α , forward , backward
  where
  forward : ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward trunc = mp α ¬allFalse
    where
    ¬allFalse : ¬ ((n : ℕ) → α n ≡ false)
    ¬allFalse all-false = PT.rec isProp⊥ (λ { (n , αn=t) → true≢false (sym αn=t ∙ all-false n) }) trunc
  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁
  backward = ∣_∣₁

-- Bundled negation: Closed → Open (requires MP)
¬-Closed : Closed → Open
¬-Closed C = ¬hProp (fst C) , negClosedIsOpen mp (fst C) (snd C)

-- Open propositions are closed under finite disjunction (derived from MP)
openOr : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
       → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
openOr = openOrMP mp

-- =============================================================================
-- Section 11: ℕ_∞ specific elements
-- =============================================================================

-- The element ∞ : ℕ_∞ (all zeros)
∞ : ℕ∞
∞ = (λ _ → false) , (λ m n αm=t _ → ex-falso (false≢true αm=t))

-- Embedding ℕ into ℕ_∞ (the element that is 1 exactly at position n)
ι : ℕ → ℕ∞
ι n = α , atMostOnce
  where
  α : binarySequence
  α m with discreteℕ m n
  ... | yes _ = true
  ... | no _ = false

  atMostOnce : hitsAtMostOnce α
  atMostOnce m k αm=t αk=t with discreteℕ m n | discreteℕ k n
  ... | yes m=n | yes k=n = m=n ∙ sym k=n
  ... | yes _ | no k≠n = ex-falso (false≢true αk=t)
  ... | no m≠n | yes _ = ex-falso (false≢true αm=t)
  ... | no m≠n | no k≠n = ex-falso (false≢true αm=t)

-- Properties of ι and ∞
-- ι(n) at position n is true
ι-at-n : (n : ℕ) → fst (ι n) n ≡ true
ι-at-n n with discreteℕ n n
... | yes _ = refl
... | no n≠n = ex-falso (n≠n refl)

-- ι(n) at position m ≠ n is false
ι-at-m≠n : (n m : ℕ) → ¬ (m ≡ n) → fst (ι n) m ≡ false
ι-at-m≠n n m m≠n with discreteℕ m n
... | yes m=n = ex-falso (m≠n m=n)
... | no _ = refl

-- ι(n) ≠ ∞ : ι n has a true at position n, but ∞ is all false
ι≠∞ : (n : ℕ) → ¬ (ι n ≡ ∞)
ι≠∞ n ι=∞ = false≢true (sym (cong (λ x → fst x n) ι=∞) ∙ ι-at-n n)

-- ι m ≠ ι n when m ≠ n
ι-injective : (m n : ℕ) → ι m ≡ ι n → m ≡ n
ι-injective m n ιm=ιn =
  let ιm-at-m : fst (ι m) m ≡ true
      ιm-at-m = ι-at-n m
      -- By ιm = ιn, fst (ι n) m = fst (ι m) m = true
      ιn-at-m : fst (ι n) m ≡ true
      ιn-at-m = cong (λ x → fst x m) (sym ιm=ιn) ∙ ιm-at-m
  in snd (ι n) m n ιn-at-m (ι-at-n n)

-- Markov principle for ℕ∞ elements (tex Theorem after NotWLPO, line 500)
-- For α : ℕ∞, if ¬(∀n. αn = false), then Σn. αn = true
-- This follows directly from general MP since ℕ∞ ⊆ 2^ℕ
ℕ∞-Markov : (α : ℕ∞) → ¬ ((n : ℕ) → fst α n ≡ false) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-Markov α = mp (fst α)

-- Equivalently: if α ≠ ∞, then there exists n with αn = true
-- (since ∞ is the unique element with ∀n. αn = false)
ℕ∞-notInfty→witness : (α : ℕ∞) → ¬ (α ≡ ∞) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-notInfty→witness α α≠∞ = ℕ∞-Markov α ¬all-false
  where
  ¬all-false : ¬ ((n : ℕ) → fst α n ≡ false)
  ¬all-false all-false = α≠∞ (Σ≡Prop isPropHitsAtMostOnce (funExt all-false))

-- The converse is also true: if ∃n. αn = true then α ≠ ∞
witness→ℕ∞-notInfty : (α : ℕ∞) → Σ[ n ∈ ℕ ] fst α n ≡ true → ¬ (α ≡ ∞)
witness→ℕ∞-notInfty α (n , αn=t) α=∞ = false≢true (sym (cong (λ x → fst x n) α=∞) ∙ αn=t)

-- For ℕ∞ elements, the witness is unique (by hitsAtMostOnce)
ℕ∞-witness-unique : (α : ℕ∞) → (n m : ℕ) → fst α n ≡ true → fst α m ≡ true → n ≡ m
ℕ∞-witness-unique α n m αn=t αm=t = snd α n m αn=t αm=t

-- α = ∞ ↔ ∀n. αn = false
-- This characterizes the element ∞
∞-char : (α : ℕ∞) → (α ≡ ∞) ↔ ((n : ℕ) → fst α n ≡ false)
∞-char α = forward , backward
  where
  forward : α ≡ ∞ → (n : ℕ) → fst α n ≡ false
  forward α=∞ n = cong (λ x → fst x n) α=∞

  backward : ((n : ℕ) → fst α n ≡ false) → α ≡ ∞
  backward all-false = Σ≡Prop isPropHitsAtMostOnce (funExt all-false)

-- Given a witness n, α = ι n
ℕ∞-witness→ι : (α : ℕ∞) → (n : ℕ) → fst α n ≡ true → α ≡ ι n
ℕ∞-witness→ι α n αn=t = Σ≡Prop isPropHitsAtMostOnce (funExt lemma)
  where
  -- Need to case on discreteℕ to reduce fst (ι n) m
  lemma : (m : ℕ) → fst α m ≡ fst (ι n) m
  lemma m with discreteℕ m n
  lemma m | yes m=n = cong (fst α) m=n ∙ αn=t  -- fst (ι n) m = true
  lemma m | no m≠n = helper (fst α m) refl  -- fst (ι n) m = false here
    where
    helper : (b : Bool) → fst α m ≡ b → fst α m ≡ false
    helper false αm=f = αm=f
    helper true αm=t = ex-falso (m≠n (snd α m n αm=t αn=t))

-- Equality in ℕ∞ is closed
-- (This is a special case of the general Stone space theorem: equality in Stone spaces is closed)
-- Proof: α = β ↔ ∀n. fst α n = fst β n (pointwise equality)
-- Each (fst α n = fst β n) is decidable (Bool has decidable equality)
-- So α = β is a countable conjunction of decidable propositions, hence closed.
ℕ∞-equality-closed : (α β : ℕ∞) → isClosedProp ((α ≡ β) , isSetΣSndProp (isSetΠ (λ _ → isSetBool)) isPropHitsAtMostOnce α β)
ℕ∞-equality-closed α β = γ , forward , backward
  where
  -- The witness: γ n = true iff fst α n ≠ fst β n
  γ : binarySequence
  γ n with fst α n =B fst β n
  ... | yes _ = false
  ... | no _ = true

  -- Forward: α = β → ∀n. γ n = false
  forward : α ≡ β → (n : ℕ) → γ n ≡ false
  forward α=β n with fst α n =B fst β n
  ... | yes _ = refl
  ... | no αn≠βn = ex-falso (αn≠βn (cong (λ x → fst x n) α=β))

  -- Backward: ∀n. γ n = false → α = β
  backward : ((n : ℕ) → γ n ≡ false) → α ≡ β
  backward all-false = Σ≡Prop isPropHitsAtMostOnce (funExt pointwise)
    where
    pointwise : (n : ℕ) → fst α n ≡ fst β n
    pointwise n with fst α n =B fst β n | all-false n
    ... | yes αn=βn | _ = αn=βn
    ... | no αn≠βn | γn=f = ex-falso (true≢false γn=f)

-- =============================================================================
-- Section 12: Markov's Principle from Stone Duality
-- =============================================================================

-- The library provides a proof that Markov's principle follows from Stone Duality.
-- Here we show how to use it and state additional consequences.

-- Markov's principle: if a sequence is not all zeros, we can find a one.
-- This is proved in OmnisciencePrinciples.Markov from Stone Duality via
-- the observation that if α ≢ 0, then Sp(2/α) is inhabited.

-- Assuming Stone Duality, we can derive MP:
-- From Stone Duality: evaluation map B → 2^(Sp B) is an equivalence for B : Booleω
-- Given α : 2^ℕ with ¬(∀n. αn = 0), consider the quotient 2/α.
-- If Sp(2/α) were inhabited, we'd have a map 2/α → 2,
-- but this would make α identically 0, contradiction.
-- So Sp(2/α) is empty, meaning 0 = 1 in 2/α, meaning some αn = 1.

-- =============================================================================
-- Section 13: LLPO from Stone Duality
-- =============================================================================

-- The proof of LLPO from Stone Duality (see main-monolithic.tex) goes as follows:
--
-- 1. B_∞ is the Boolean algebra generated by (g_n)_{n:ℕ} with relations g_m ∧ g_n = 0 for m ≠ n.
--    Its spectrum ℕ∞ = Sp(B_∞) consists of sequences hitting 1 at most once.
--
-- 2. Define f : B_∞ → B_∞ × B_∞ by:
--    f(g_n) = (g_k, 0) if n = 2k
--    f(g_n) = (0, g_k) if n = 2k+1
--
-- 3. This map is injective (well-defined by the relations).
--
-- 4. By Stone Duality axiom "surjections are formal surjections":
--    f injective ⟹ Sp(f) : Sp(B_∞ × B_∞) → Sp(B_∞) is surjective.
--
-- 5. Since Sp(B_∞ × B_∞) ≅ ℕ∞ + ℕ∞, we get a surjection s : ℕ∞ + ℕ∞ → ℕ∞.
--
-- 6. For any α : ℕ∞, there exists x : ℕ∞ + ℕ∞ with s(x) = α.
--    - If x = inl(β), then α_{2k+1} = 0 for all k.
--    - If x = inr(β), then α_{2k} = 0 for all k.

-- We postulate LLPO as an axiom that follows from Stone Duality.
-- The full proof requires setting up B_∞ quotients which is done in the library.

postulate
  llpo : LLPO

-- =============================================================================
-- Section 14: Consequences of LLPO
-- =============================================================================

-- LLPO implies that closed propositions are closed under finite disjunctions.
-- This is because LLPO is equivalent to the statement:
-- (¬P ∨ ¬Q) ↔ ¬(P ∧ Q) for open P, Q

-- Given P, Q closed propositions:
-- P ↔ ∀n. αn = 0, Q ↔ ∀n. βn = 0
-- We want: P ∨ Q is closed.
--
-- P ∨ Q ↔ (∀n. αn = 0) ∨ (∀n. βn = 0)
--
-- Define γ : ℕ∞ by: γ(2k) = α(k), γ(2k+1) = β(k)
-- (But γ may hit 1 more than once if both α and β hit 1.)
--
-- Instead, we use LLPO on sequences that hit at most once.

-- For the full characterization, we would prove:
-- Closed propositions closed under disjunction (using LLPO)
-- The direct proof is more involved; we sketch the idea:

-- Given α, β : 2^ℕ witnessing closedness of P, Q:
-- P ↔ ∀n. αn = 0, Q ↔ ∀n. βn = 0
--
-- To show P ∨ Q is closed, we need γ : 2^ℕ with:
-- (P ∨ Q) ↔ ∀n. γn = 0
--
-- The issue is P ∨ Q = (∀n. αn = 0) ∨ (∀n. βn = 0), which is NOT the same as
-- ∀n. (αn = 0 ∨ βn = 0) (the latter is weaker).
--
-- LLPO bridges this gap for suitable sequences.

-- Closed propositions are closed under disjunction
-- This is postponed until after openAnd is defined.
-- See closedOr definition below.

-- =============================================================================
-- Section 15: The Cantor space as a Stone space
-- =============================================================================

-- 2^ℕ = Sp(Free BA on ℕ) where Free BA on ℕ is the free Boolean algebra on countably many generators.
-- This is a fundamental example of Stone duality.

-- The elements of Sp(B) for a Boolean algebra B are the Boolean homomorphisms B → 2.
-- For B = Free(ℕ), these correspond exactly to functions ℕ → 2 = binary sequences.

-- =============================================================================
-- Section 16: Open and closed subsets
-- =============================================================================

-- In the synthetic topology, every type X has a canonical topology where:
-- - An open subset of X is a function X → Ω_open (the type of open propositions)
-- - A closed subset of X is a function X → Ω_closed (the type of closed propositions)

-- The key properties are:
-- 1. Every function between types is continuous (this is automatic)
-- 2. Open subsets are closed under finite intersections and arbitrary unions
-- 3. Closed subsets are closed under finite unions and arbitrary intersections

-- =============================================================================
-- Section 17: Countable closure properties
-- =============================================================================

-- We need a bijection ℕ × ℕ ≅ ℕ for countable closure properties.
-- We'll use a simple diagonal enumeration.

-- The inspect idiom for capturing equalities from with-abstractions
data Reveal_·_is_ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) (y : B x) : Type₀ where
  [_] : f x ≡ y → Reveal f · x is y

inspect : ∀ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]

-- Cantor pairing function: ⟨m, n⟩ = (m + n)(m + n + 1)/2 + n
-- The bijectivity is fully proved below using findDiagonal helper

private
  -- Triangular number: T(n) = 0 + 1 + ... + n = n(n+1)/2
  -- This is the number of elements before diagonal n
  triangular : ℕ → ℕ
  triangular zero = zero
  triangular (suc n) = suc n +ℕ triangular n

  -- Cantor pairing: ⟨m, n⟩ = triangular(m + n) + n
  cantorPair : ℕ → ℕ → ℕ
  cantorPair m n = triangular (m +ℕ n) +ℕ n

  -- For unpairing, we enumerate diagonals:
  -- k=0: (0,0)
  -- k=1: (1,0)
  -- k=2: (0,1)
  -- k=3: (2,0)
  -- k=4: (1,1)
  -- k=5: (0,2)
  -- etc.
  --
  -- On diagonal w (sum = w), positions are: (w,0), (w-1,1), ..., (0,w)
  -- The k-th element overall is on diagonal w where triangular w ≤ k < triangular (w+1)
  -- Within the diagonal, position is k - triangular w

  -- Boolean less-than for natural numbers (local version)
  _<ᵇ'_ : ℕ → ℕ → Bool
  zero <ᵇ' zero = false
  zero <ᵇ' suc n = true
  suc m <ᵇ' zero = false
  suc m <ᵇ' suc n = m <ᵇ' n

  -- Helper: find diagonal w given k, using fuel
  -- Invariant: we're checking if k is on diagonal (diag + fuel - remaining_fuel)
  findDiagonal : ℕ → ℕ → ℕ → ℕ
  findDiagonal zero k diag = diag  -- out of fuel, return current
  findDiagonal (suc fuel) k diag =
    if k <ᵇ' triangular (suc diag)
    then diag  -- k < triangular(diag+1), so k is on diagonal diag
    else findDiagonal fuel k (suc diag)  -- k >= triangular(diag+1), try next

  -- Cantor unpairing: find diagonal w, then compute (w - n, n) where n = k - triangular w
  cantorUnpair : ℕ → ℕ × ℕ
  cantorUnpair k =
    let w = findDiagonal (suc k) k 0  -- use k+1 as fuel (sufficient)
        n = k ∸ triangular w
        m = w ∸ n
    in (m , n)

  -- Lemmas about boolean comparison
  <ᵇ'-reflects : (m n : ℕ) → m <ᵇ' n ≡ true → m < n
  <ᵇ'-reflects zero zero p = ex-falso (false≢true p)
  <ᵇ'-reflects zero (suc n) _ = suc-≤-suc zero-≤
  <ᵇ'-reflects (suc m) zero p = ex-falso (false≢true p)
  <ᵇ'-reflects (suc m) (suc n) p = suc-≤-suc (<ᵇ'-reflects m n p)

  ¬<ᵇ'-reflects : (m n : ℕ) → m <ᵇ' n ≡ false → n ≤ m
  ¬<ᵇ'-reflects zero zero _ = ≤-refl
  ¬<ᵇ'-reflects zero (suc n) p = ex-falso (true≢false p)
  ¬<ᵇ'-reflects (suc m) zero _ = zero-≤
  ¬<ᵇ'-reflects (suc m) (suc n) p = suc-≤-suc (¬<ᵇ'-reflects m n p)

  -- Arithmetic lemmas
  -- Note: (a + suc b) ∸ suc c = a + b ∸ c when suc c ≤ suc b
  +-∸-assoc : (a b c : ℕ) → c ≤ b → a +ℕ b ∸ c ≡ a +ℕ (b ∸ c)
  +-∸-assoc a zero zero _ = refl
  +-∸-assoc a zero (suc c) sc≤0 = ex-falso (¬-<-zero sc≤0)
  +-∸-assoc a (suc b) zero _ = refl
  +-∸-assoc a (suc b) (suc c) sc≤sb =
    a +ℕ suc b ∸ suc c   ≡⟨ cong (_∸ suc c) (+-suc a b) ⟩
    suc (a +ℕ b) ∸ suc c ≡⟨ refl ⟩
    a +ℕ b ∸ c           ≡⟨ +-∸-assoc a b c (pred-≤-pred sc≤sb) ⟩
    a +ℕ (b ∸ c)         ∎

  +∸-cancel : (a b : ℕ) → (a +ℕ b) ∸ b ≡ a
  +∸-cancel a zero = +-zero a
  +∸-cancel a (suc b) =
    (a +ℕ suc b) ∸ suc b   ≡⟨ cong (_∸ suc b) (+-suc a b) ⟩
    suc (a +ℕ b) ∸ suc b   ≡⟨ refl ⟩
    (a +ℕ b) ∸ b           ≡⟨ +∸-cancel a b ⟩
    a                      ∎

  ∸+-cancel : (a b : ℕ) → b ≤ a → (a ∸ b) +ℕ b ≡ a
  ∸+-cancel a zero _ = +-zero a
  ∸+-cancel zero (suc b) sb≤0 = ex-falso (¬-<-zero sb≤0)
  ∸+-cancel (suc a) (suc b) sb≤sa =
    (suc a ∸ suc b) +ℕ suc b   ≡⟨ refl ⟩
    (a ∸ b) +ℕ suc b           ≡⟨ +-suc (a ∸ b) b ⟩
    suc ((a ∸ b) +ℕ b)         ≡⟨ cong suc (∸+-cancel a b (pred-≤-pred sb≤sa)) ⟩
    suc a ∎

  -- triangular w ≤ triangular w + n
  triangular≤cantorPair : (m n : ℕ) → triangular (m +ℕ n) ≤ cantorPair m n
  triangular≤cantorPair m n = ≤-+k-local (triangular (m +ℕ n)) n
    where
    ≤-+k-local : (a b : ℕ) → a ≤ a +ℕ b
    ≤-+k-local a zero = subst (a ≤_) (sym (+-zero a)) ≤-refl
    ≤-+k-local a (suc b) =
      let step1 : a ≤ a +ℕ b
          step1 = ≤-+k-local a b
          step2 : a ≤ suc (a +ℕ b)
          step2 = ≤-suc step1
      in subst (a ≤_) (sym (+-suc a b)) step2

  -- cantorPair m n < triangular (suc (m + n))
  -- triangular (suc w) = (suc w) + triangular w
  -- cantorPair m n = triangular w + n where w = m + n
  -- We need: triangular w + n < (suc w) + triangular w
  -- i.e., n < suc w = suc (m + n)
  -- This is always true since n ≤ m + n < suc (m + n)

  cantorPair<triangular-suc : (m n : ℕ) → cantorPair m n < triangular (suc (m +ℕ n))
  cantorPair<triangular-suc m n = goal
    where
    w = m +ℕ n
    -- cantorPair m n = triangular w + n
    -- triangular (suc w) = suc w + triangular w
    -- We need: suc (triangular w + n) ≤ suc w + triangular w
    -- Since n ≤ w, we have suc n ≤ suc w
    -- So: triangular w + suc n ≤ triangular w + suc w
    -- And: suc (triangular w + n) = triangular w + suc n (by +-suc)

    n≤w : n ≤ w
    n≤w = n≤m+n-local m n
      where
      n≤m+n-local : (a b : ℕ) → b ≤ a +ℕ b
      n≤m+n-local zero b = ≤-refl
      n≤m+n-local (suc a) b = ≤-trans (n≤m+n-local a b) ≤-sucℕ

    sucn≤sucw : suc n ≤ suc w
    sucn≤sucw = suc-≤-suc n≤w

    -- triangular w + suc n ≤ triangular w + suc w
    step1 : triangular w +ℕ suc n ≤ triangular w +ℕ suc w
    step1 = ≤-+k-mono (triangular w) (suc n) (suc w) sucn≤sucw
      where
      ≤-+k-mono : (a b c : ℕ) → b ≤ c → a +ℕ b ≤ a +ℕ c
      ≤-+k-mono zero b c b≤c = b≤c
      ≤-+k-mono (suc a) b c b≤c = suc-≤-suc (≤-+k-mono a b c b≤c)

    -- suc (triangular w + n) = triangular w + suc n
    eq1 : suc (triangular w +ℕ n) ≡ triangular w +ℕ suc n
    eq1 = sym (+-suc (triangular w) n)

    -- triangular w + suc w = suc w + triangular w (commutativity)
    eq2 : triangular w +ℕ suc w ≡ suc w +ℕ triangular w
    eq2 = +-comm (triangular w) (suc w)

    -- suc w + triangular w = triangular (suc w)
    eq3 : suc w +ℕ triangular w ≡ triangular (suc w)
    eq3 = refl

    -- step1 : triangular w +ℕ suc n ≤ triangular w +ℕ suc w
    -- We need: suc (triangular w +ℕ n) ≤ triangular (suc w)
    -- Using: suc (triangular w +ℕ n) ≡ triangular w +ℕ suc n
    -- And: triangular w +ℕ suc w ≡ suc w +ℕ triangular w = triangular (suc w)

    goal : suc (triangular w +ℕ n) ≤ triangular (suc w)
    goal = subst (_≤ triangular (suc w)) (sym eq1)
             (subst (triangular w +ℕ suc n ≤_) (eq2 ∙ eq3) step1)

  -- Key lemma: if k < triangular (suc diag), then findDiagonal returns diag
  findDiagonal-found : (fuel k diag : ℕ) → k <ᵇ' triangular (suc diag) ≡ true
                     → findDiagonal (suc fuel) k diag ≡ diag
  findDiagonal-found fuel k diag p with k <ᵇ' triangular (suc diag) | p
  ... | true | _ = refl
  ... | false | q = ex-falso (false≢true q)

  -- If k >= triangular (suc diag), findDiagonal continues to next diag
  findDiagonal-continue : (fuel k diag : ℕ) → k <ᵇ' triangular (suc diag) ≡ false
                        → findDiagonal (suc fuel) k diag ≡ findDiagonal fuel k (suc diag)
  findDiagonal-continue fuel k diag p with k <ᵇ' triangular (suc diag) | p
  ... | false | _ = refl
  ... | true | q = ex-falso (true≢false q)

  -- Boolean comparison properties
  <ᵇ'-suc : (n : ℕ) → n <ᵇ' suc n ≡ true
  <ᵇ'-suc zero = refl
  <ᵇ'-suc (suc n) = <ᵇ'-suc n

  -- Helper to convert between < and <ᵇ'
  <-reflects-<ᵇ' : (a b : ℕ) → a < b → a <ᵇ' b ≡ true
  <-reflects-<ᵇ' zero zero 1≤0 = ex-falso (¬-<-zero 1≤0)
  <-reflects-<ᵇ' zero (suc b) _ = refl
  <-reflects-<ᵇ' (suc a) zero sa<0 = ex-falso (¬-<-zero sa<0)
  <-reflects-<ᵇ' (suc a) (suc b) sa<sb = <-reflects-<ᵇ' a b (pred-≤-pred sa<sb)

  cantorPair<ᵇ'-triangular-suc : (m n : ℕ) → cantorPair m n <ᵇ' triangular (suc (m +ℕ n)) ≡ true
  cantorPair<ᵇ'-triangular-suc m n = <-reflects-<ᵇ' _ _ (cantorPair<triangular-suc m n)

  -- For the full bijectivity proofs, we need:
  -- 1. findDiagonal finds the correct diagonal w = m + n for cantorPair m n
  -- 2. The arithmetic (cantorPair m n) - triangular w = n
  -- 3. The arithmetic w - n = m
  --
  -- Step 2: (triangular w + n) - triangular w = n (by +∸-cancel)
  cantorPair-triangular-diff : (m n : ℕ) → cantorPair m n ∸ triangular (m +ℕ n) ≡ n
  cantorPair-triangular-diff m n = +∸-cancel' n (triangular (m +ℕ n))
    where
    +∸-cancel' : (a b : ℕ) → (b +ℕ a) ∸ b ≡ a
    +∸-cancel' a zero = refl
    +∸-cancel' a (suc b) = +∸-cancel' a b

  -- Step 3: (m + n) - n = m (standard arithmetic)
  m+n∸n≡m : (m n : ℕ) → (m +ℕ n) ∸ n ≡ m
  m+n∸n≡m m zero = +-zero m
  m+n∸n≡m m (suc n) =
    (m +ℕ suc n) ∸ suc n   ≡⟨ cong (_∸ suc n) (+-suc m n) ⟩
    suc (m +ℕ n) ∸ suc n   ≡⟨ refl ⟩
    (m +ℕ n) ∸ n           ≡⟨ m+n∸n≡m m n ⟩
    m ∎

  -- Step 1 is the main lemma: findDiagonal finds the right diagonal
  -- This requires showing that for k = cantorPair m n with w = m + n:
  -- - For all acc < w: k ≥ triangular (suc acc), so we continue
  -- - For acc = w: k < triangular (suc w), so we stop

  -- Key lemma: k ≥ triangular(suc acc) when acc < w and triangular w ≤ k
  -- This is because triangular is monotonic: acc < w => triangular(suc acc) ≤ triangular w ≤ k

  -- Triangular is strictly monotonic: n < m => triangular n < triangular m (for n > 0)
  -- triangular n < triangular (suc n) = suc n + triangular n
  -- i.e., suc (triangular n) ≤ suc n + triangular n
  -- i.e., 1 + triangular n ≤ suc n + triangular n
  -- By monotonicity: since 1 ≤ suc n
  triangular-suc : (n : ℕ) → triangular n < triangular (suc n)
  triangular-suc n = ≤-+k-mono-l 1 (suc n) (triangular n) (suc-≤-suc zero-≤)
    where
    ≤-+k-mono-l : (a b c : ℕ) → a ≤ b → a +ℕ c ≤ b +ℕ c
    ≤-+k-mono-l zero b c _ = ≤-+k-r b c
      where
      ≤-+k-r : (x y : ℕ) → y ≤ x +ℕ y
      ≤-+k-r zero y = ≤-refl
      ≤-+k-r (suc x) y = ≤-trans (≤-+k-r x y) ≤-sucℕ
    ≤-+k-mono-l (suc a) zero c sa≤0 = ex-falso (¬-<-zero sa≤0)
    ≤-+k-mono-l (suc a) (suc b) c sa≤sb = suc-≤-suc (≤-+k-mono-l a b c (pred-≤-pred sa≤sb))

  triangular-mono-< : (n m : ℕ) → n < m → triangular n < triangular m
  triangular-mono-< n zero n<0 = ex-falso (¬-<-zero n<0)
  triangular-mono-< n (suc m) sn≤sm with n ≟ m
  ... | lt n<m = <-trans (triangular-mono-< n m n<m) (triangular-suc m)
  ... | eq n≡m = subst (λ x → triangular x < triangular (suc m)) (sym n≡m) (triangular-suc m)
  -- gt means m < n, but we have n < suc m i.e. suc n ≤ suc m i.e. n ≤ m
  -- So m < n and n ≤ m gives m < m, contradiction
  ... | gt m<n = ex-falso (¬m<m (≤-trans m<n (pred-≤-pred sn≤sm)))

  -- triangular is monotonic for ≤
  triangular-mono-≤ : (n m : ℕ) → n ≤ m → triangular n ≤ triangular m
  triangular-mono-≤ n m n≤m with n ≟ m
  ... | lt n<m = <-weaken (triangular-mono-< n m n<m)
  ... | eq n≡m = subst (λ x → triangular n ≤ triangular x) n≡m ≤-refl
  ... | gt m<n = ex-falso (¬m<m (≤-trans m<n n≤m))

  -- If acc < w and k ≥ triangular w, then k ≥ triangular(suc acc)
  -- acc < w means suc acc ≤ w, so triangular (suc acc) ≤ triangular w ≤ k
  k≥triangular-suc-acc : (k w acc : ℕ) → acc < w → triangular w ≤ k
                       → triangular (suc acc) ≤ k
  k≥triangular-suc-acc k w acc acc<w Tw≤k =
    ≤-trans (triangular-mono-≤ (suc acc) w acc<w) Tw≤k

  -- Therefore k <ᵇ' triangular(suc acc) ≡ false when acc < w
  k≮ᵇ'triangular-suc-acc : (k w acc : ℕ) → acc < w → triangular w ≤ k
                        → k <ᵇ' triangular (suc acc) ≡ false
  k≮ᵇ'triangular-suc-acc k w acc acc<w Tw≤k = ≤-reflects-¬<ᵇ' _ _ (k≥triangular-suc-acc k w acc acc<w Tw≤k)
    where
    ≤-reflects-¬<ᵇ' : (a b : ℕ) → b ≤ a → a <ᵇ' b ≡ false
    ≤-reflects-¬<ᵇ' zero zero _ = refl
    ≤-reflects-¬<ᵇ' (suc a) zero _ = refl
    ≤-reflects-¬<ᵇ' zero (suc b) sb≤0 = ex-falso (¬-<-zero sb≤0)
    ≤-reflects-¬<ᵇ' (suc a) (suc b) sb≤sa = ≤-reflects-¬<ᵇ' a b (pred-≤-pred sb≤sa)

  -- Main lemma: findDiagonal finds w when called with sufficient fuel
  -- We prove this by induction on (w - acc)
  findDiagonal-aux : (w k acc fuel : ℕ) → w ∸ acc ≤ fuel
                   → k <ᵇ' triangular (suc w) ≡ true
                   → triangular w ≤ k
                   → acc ≤ w
                   → findDiagonal (suc fuel) k acc ≡ w
  findDiagonal-aux w k acc zero w∸acc≤0 k<Tsw Tw≤k acc≤w with w ≟ acc
  ... | lt w<acc = ex-falso (¬m<m (≤-trans w<acc acc≤w))
  ... | eq w≡acc = subst (findDiagonal 1 k acc ≡_) (sym w≡acc) (findDiagonal-found 0 k acc (subst (λ x → k <ᵇ' triangular (suc x) ≡ true) w≡acc k<Tsw))
  ... | gt acc<w = ex-falso (¬m<m (≤-trans (∸-<-from w acc acc<w) w∸acc≤0))
    where
    ∸-<-from : (a b : ℕ) → b < a → 1 ≤ a ∸ b
    ∸-<-from zero zero 1≤0 = ex-falso (¬-<-zero 1≤0)
    ∸-<-from zero (suc b) sb<0 = ex-falso (¬-<-zero sb<0)
    ∸-<-from (suc a) zero _ = suc-≤-suc zero-≤
    ∸-<-from (suc a) (suc b) sb<sa = ∸-<-from a b (pred-≤-pred sb<sa)

  findDiagonal-aux w k acc (suc fuel) w∸acc≤sf k<Tsw Tw≤k acc≤w with w ≟ acc
  ... | lt w<acc = ex-falso (¬m<m (≤-trans w<acc acc≤w))
  ... | eq w≡acc = subst (findDiagonal (suc (suc fuel)) k acc ≡_) (sym w≡acc) (findDiagonal-found (suc fuel) k acc (subst (λ x → k <ᵇ' triangular (suc x) ≡ true) w≡acc k<Tsw))
  ... | gt acc<w =
    let step1 = findDiagonal-continue (suc fuel) k acc (k≮ᵇ'triangular-suc-acc k w acc acc<w Tw≤k)
        step2 = findDiagonal-aux w k (suc acc) fuel (≤-pred-∸' w acc acc<w w∸acc≤sf) k<Tsw Tw≤k acc<w
    in step1 ∙ step2
    where
    -- w ∸ acc ≤ suc fuel and acc < w imply w ∸ suc acc ≤ fuel
    -- Since acc < w, we can case split to show w ≥ 1
    ≤-pred-∸' : (w acc : ℕ) → acc < w → w ∸ acc ≤ suc fuel → w ∸ suc acc ≤ fuel
    ≤-pred-∸' zero acc 0<acc _ = ex-falso (¬-<-zero 0<acc)
    ≤-pred-∸' (suc w') acc acc<sw w∸acc≤sf = ≤-pred-∸-aux w' acc acc<sw w∸acc≤sf
      where
      ≤-pred-∸-aux : (w acc : ℕ) → acc < suc w → suc w ∸ acc ≤ suc fuel → suc w ∸ suc acc ≤ fuel
      ≤-pred-∸-aux w zero _ sw∸0≤sf = pred-≤-pred sw∸0≤sf
      ≤-pred-∸-aux w (suc acc) sacc<sw p = ≤-pred-∸-aux' w acc (pred-≤-pred sacc<sw) p
        where
        ≤-pred-∸-aux' : (w acc : ℕ) → acc < w → w ∸ acc ≤ suc fuel → w ∸ suc acc ≤ fuel
        ≤-pred-∸-aux' zero acc 1≤0 _ = ex-falso (¬-<-zero 1≤0)
        ≤-pred-∸-aux' (suc w') acc acc<sw' w∸acc≤sf' = ≤-pred-∸-aux w' acc acc<sw' w∸acc≤sf'

  -- w ≤ triangular w + w
  w≤triangular : (w : ℕ) → w ≤ triangular w +ℕ w
  w≤triangular w = ≤-+k-r' w (triangular w)
    where
    -- n ≤ m + n for any m, n
    ≤-+k-r' : (n m : ℕ) → n ≤ m +ℕ n
    ≤-+k-r' n zero = ≤-refl
    ≤-+k-r' n (suc m) = ≤-trans (≤-+k-r' n m) ≤-sucℕ

  -- m + n ≤ cantorPair m n = triangular (m + n) + n
  -- Since m + n ≤ triangular (m + n), we have m + n ≤ triangular (m + n) + n
  w≤cantorPair : (m n : ℕ) → m +ℕ n ≤ cantorPair m n
  w≤cantorPair m n = ≤-trans (m+n≤tri-m+n m n) (≤-+k-r (triangular (m +ℕ n)) n)
    where
    -- n ≤ triangular n for all n
    n≤triangular-n : (n : ℕ) → n ≤ triangular n
    n≤triangular-n zero = zero-≤
    n≤triangular-n (suc n) = suc-≤-suc (≤-trans (n≤triangular-n n) (≤-+k-r' (triangular n) n))
      where
      ≤-+k-r' : (a b : ℕ) → a ≤ b +ℕ a
      ≤-+k-r' a zero = ≤-refl
      ≤-+k-r' a (suc b) = ≤-trans (≤-+k-r' a b) ≤-sucℕ

    m+n≤tri-m+n : (m n : ℕ) → m +ℕ n ≤ triangular (m +ℕ n)
    m+n≤tri-m+n m n = n≤triangular-n (m +ℕ n)

    -- a ≤ a + b
    ≤-+k-r : (a b : ℕ) → a ≤ a +ℕ b
    ≤-+k-r a zero = subst (a ≤_) (sym (+-zero a)) ≤-refl
    ≤-+k-r a (suc b) = subst (a ≤_) (sym (+-suc a b)) (≤-trans (≤-+k-r a b) ≤-sucℕ)

  -- Putting it together: findDiagonal finds m + n for cantorPair m n
  findDiagonal-correct : (m n : ℕ) →
    findDiagonal (suc (cantorPair m n)) (cantorPair m n) 0 ≡ m +ℕ n
  findDiagonal-correct m n =
    let k = cantorPair m n
        w = m +ℕ n
    in findDiagonal-aux w k 0 k
         (w≤cantorPair m n)
         (cantorPair<ᵇ'-triangular-suc m n)
         (triangular≤cantorPair m n)
         zero-≤

  -- Now we can prove cantorUnpair-pair
  cantorUnpair-pair : (m n : ℕ) → cantorUnpair (cantorPair m n) ≡ (m , n)
  cantorUnpair-pair m n =
    let k = cantorPair m n
        w = m +ℕ n
        findW = findDiagonal-correct m n
    in
    cantorUnpair k                                         ≡⟨ refl ⟩
    (let w' = findDiagonal (suc k) k 0
         n' = k ∸ triangular w'
         m' = w' ∸ n'
     in (m' , n'))                                          ≡⟨ cong (λ w' → ((w' ∸ (k ∸ triangular w')) , (k ∸ triangular w'))) findW ⟩
    (w ∸ (k ∸ triangular w) , k ∸ triangular w)             ≡⟨ cong (λ x → (w ∸ x , x)) (cantorPair-triangular-diff m n) ⟩
    (w ∸ n , n)                                              ≡⟨ cong (λ x → (x , n)) (m+n∸n≡m m n) ⟩
    (m , n) ∎

  -- For cantorPair-unpair, we need the reverse direction
  -- If cantorUnpair k = (m, n), then cantorPair m n = k

  -- Helper: a + (b - a) = b when a ≤ b
  a+b∸a≡b : (a b : ℕ) → a ≤ b → a +ℕ (b ∸ a) ≡ b
  a+b∸a≡b zero b _ = refl
  a+b∸a≡b (suc a) zero sa≤0 = ex-falso (¬-<-zero sa≤0)
  a+b∸a≡b (suc a) (suc b) sa≤sb = cong suc (a+b∸a≡b a b (pred-≤-pred sa≤sb))

  -- (w - n) + n = w when n ≤ w
  w∸n+n≡w : (w n : ℕ) → n ≤ w → (w ∸ n) +ℕ n ≡ w
  w∸n+n≡w w n n≤w = ∸+-cancel w n n≤w

  -- Key: findDiagonal returns a value w such that triangular w ≤ k < triangular (suc w)
  -- This means n = k - triangular w satisfies n ≤ w
  -- and cantorPair m n = triangular(m + n) + n = triangular w + n = k

  -- First: show n ≤ w when n = k - triangular w and k < triangular(suc w)
  n≤w-from-bounds : (k w : ℕ) → triangular w ≤ k → k < triangular (suc w)
                  → k ∸ triangular w ≤ w
  n≤w-from-bounds k w Tw≤k k<Tsw =
    -- k - triangular w < triangular(suc w) - triangular w = suc w
    -- So k - triangular w ≤ w
    let step1 : k ∸ triangular w < triangular (suc w) ∸ triangular w
        step1 = ∸-mono-< k (triangular w) (triangular (suc w)) Tw≤k k<Tsw (triangular-suc w)
        -- triangular (suc w) ∸ triangular w = suc w
        eq : triangular (suc w) ∸ triangular w ≡ suc w
        eq = +∸-cancel (suc w) (triangular w)
        step2 : k ∸ triangular w < suc w
        step2 = subst (k ∸ triangular w <_) eq step1
    in pred-≤-pred step2
    where
    -- a ≤ b and b < c and c = b + d implies a - b < d, so a - b ≤ d - 1
    ∸-mono-< : (a b c : ℕ) → b ≤ a → a < c → b < c → a ∸ b < c ∸ b
    ∸-mono-< a b zero b≤a a<0 _ = ex-falso (¬-<-zero a<0)
    ∸-mono-< a b (suc c) b≤a sa≤sc b<sc with ≤Dec b a
    ... | yes b≤a' = subst (suc (a ∸ b) ≤_) (sym (suc-∸ c b (pred-≤-pred b<sc))) (suc-≤-suc (∸-mono a c b (pred-≤-pred sa≤sc) b≤a'))
      where
      -- b ≤ c implies suc c ∸ b ≡ suc (c ∸ b)
      suc-∸ : (x y : ℕ) → y ≤ x → suc x ∸ y ≡ suc (x ∸ y)
      suc-∸ x zero _ = refl
      suc-∸ (suc x) (suc y) sy≤sx = suc-∸ x y (pred-≤-pred sy≤sx)
      suc-∸ zero (suc y) sy≤0 = ex-falso (¬-<-zero sy≤0)

      ∸-mono : (x y z : ℕ) → x ≤ y → z ≤ x → x ∸ z ≤ y ∸ z
      ∸-mono x y zero x≤y _ = x≤y
      ∸-mono zero zero (suc z) _ sz≤0 = ex-falso (¬-<-zero sz≤0)
      ∸-mono zero (suc y) (suc z) _ sz≤0 = ex-falso (¬-<-zero sz≤0)
      ∸-mono (suc x) zero (suc z) sx≤0 _ = ex-falso (¬-<-zero sx≤0)
      ∸-mono (suc x) (suc y) (suc z) sx≤sy sz≤sx = ∸-mono x y z (pred-≤-pred sx≤sy) (pred-≤-pred sz≤sx)
    ... | no ¬b≤a = ex-falso (¬b≤a b≤a)

  -- Show that findDiagonal returns the correct diagonal (satisfying bounds)
  -- This requires that findDiagonal actually finds the right diagonal
  -- Since findDiagonal-aux already ensures this, we just need to extract bounds

  -- For cantorPair-unpair, we need the bounds that findDiagonal's result satisfies.
  -- The key is that findDiagonal returns w such that:
  -- - triangular w ≤ k (accumulated from starting at 0)
  -- - k < triangular (suc w) (the stopping condition)
  --
  -- We prove these bounds by induction on the fuel parameter.

  -- Lemma: findDiagonal satisfies the lower bound (triangular w ≤ k)
  -- when started with triangular diag ≤ k
  findDiagonal-lower-bound : (fuel k diag : ℕ) → triangular diag ≤ k
                           → triangular (findDiagonal fuel k diag) ≤ k
  findDiagonal-lower-bound zero k diag Td≤k = Td≤k
  findDiagonal-lower-bound (suc fuel) k diag Td≤k with k <ᵇ' triangular (suc diag) | inspect (k <ᵇ'_) (triangular (suc diag))
  ... | true | _ = Td≤k
  ... | false | [ p ] = findDiagonal-lower-bound fuel k (suc diag) (¬<ᵇ'-reflects k (triangular (suc diag)) p)

  -- Lemma: findDiagonal satisfies the upper bound (k < triangular (suc w))
  -- Invariant: diag + fuel > k (strict), which means fuel runs out only when diag > k
  findDiagonal-upper-bound : (fuel k diag : ℕ) → suc k ≤ diag +ℕ fuel
                           → k < triangular (suc (findDiagonal fuel k diag))
  findDiagonal-upper-bound zero k diag sk≤d0 =
    -- fuel = 0, so findDiagonal returns diag
    -- sk≤d0 : suc k ≤ diag +ℕ 0
    -- We have suc k ≤ diag, i.e., k < diag
    -- Need: k < triangular (suc diag), i.e., suc k ≤ triangular (suc diag)
    -- triangular (suc diag) = suc diag + triangular diag ≥ suc diag ≥ suc k (since suc k ≤ diag < suc diag)
    let sk≤d : suc k ≤ diag
        sk≤d = subst (suc k ≤_) (+-zero diag) sk≤d0
        sk≤sd : suc k ≤ suc diag
        sk≤sd = ≤-trans sk≤d ≤-sucℕ
        -- triangular (suc diag) = suc diag + triangular diag, so suc diag ≤ triangular (suc diag)
        sd≤Tsd : suc diag ≤ triangular (suc diag)
        sd≤Tsd = n≤n+m (suc diag) (triangular diag)
    in ≤-trans sk≤sd sd≤Tsd
    where
    n≤n+m : (n m : ℕ) → n ≤ n +ℕ m
    n≤n+m n zero = subst (n ≤_) (sym (+-zero n)) ≤-refl
    n≤n+m n (suc m) = subst (n ≤_) (sym (+-suc n m)) (≤-trans (n≤n+m n m) ≤-sucℕ)
  findDiagonal-upper-bound (suc fuel) k diag sk≤df with k <ᵇ' triangular (suc diag) | inspect (k <ᵇ'_) (triangular (suc diag))
  ... | true | [ p ] = <ᵇ'-reflects k (triangular (suc diag)) p
  ... | false | _ =
    -- Recurse: need suc k ≤ suc diag +ℕ fuel = suc (diag +ℕ fuel)
    -- We have suc k ≤ diag +ℕ suc fuel = suc (diag +ℕ fuel) by +-suc
    findDiagonal-upper-bound fuel k (suc diag) (subst (suc k ≤_) (+-suc diag fuel) sk≤df)

  -- Combine the bounds
  findDiagonal-bounds : (k : ℕ) →
    let w = findDiagonal (suc k) k 0
    in (triangular w ≤ k) × (k < triangular (suc w))
  findDiagonal-bounds k =
    let Tw≤k = findDiagonal-lower-bound (suc k) k 0 zero-≤
        -- Need: suc k ≤ 0 +ℕ suc k = suc k, which is ≤-refl
        k<Tsw = findDiagonal-upper-bound (suc k) k 0 ≤-refl
    in Tw≤k , k<Tsw

  -- Now prove cantorPair-unpair using the bounds
  cantorPair-unpair : (k : ℕ) → uncurry cantorPair (cantorUnpair k) ≡ k
  cantorPair-unpair k =
    let w = findDiagonal (suc k) k 0
        n' = k ∸ triangular w
        m' = w ∸ n'
        (Tw≤k , k<Tsw) = findDiagonal-bounds k
        n'≤w = n≤w-from-bounds k w Tw≤k k<Tsw
        -- m' + n' = w
        m'+n'=w : m' +ℕ n' ≡ w
        m'+n'=w = w∸n+n≡w w n' n'≤w
        -- cantorPair m' n' = triangular(m' + n') + n' = triangular w + n'
        step1 : cantorPair m' n' ≡ triangular (m' +ℕ n') +ℕ n'
        step1 = refl
        step2 : triangular (m' +ℕ n') +ℕ n' ≡ triangular w +ℕ n'
        step2 = cong (λ x → triangular x +ℕ n') m'+n'=w
        -- triangular w + n' = triangular w + (k - triangular w) = k
        step3 : triangular w +ℕ n' ≡ k
        step3 = a+b∸a≡b (triangular w) k Tw≤k
    in
    uncurry cantorPair (cantorUnpair k)
      ≡⟨ refl ⟩
    cantorPair m' n'
      ≡⟨ step1 ⟩
    triangular (m' +ℕ n') +ℕ n'
      ≡⟨ step2 ⟩
    triangular w +ℕ n'
      ≡⟨ step3 ⟩
    k ∎

-- Open propositions are closed under finite conjunction
-- If P ↔ ∃n. αn = 1 and Q ↔ ∃m. βm = 1, then P ∧ Q ↔ ∃k. γk = 1
-- where γ(⟨n,m⟩) = αn ∧ᵇ βm (using Cantor pairing)
openAnd : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
openAnd P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = γ , forward , backward
  where
  γ : binarySequence
  γ k = let (n , m) = cantorUnpair k in α n and β m

  forward : ⟨ P ⟩ × ⟨ Q ⟩ → Σ[ k ∈ ℕ ] γ k ≡ true
  forward (p , q) =
    let (n , αn=t) = P→∃α p
        (m , βm=t) = Q→∃β q
        k = cantorPair n m
        -- γ k = α (fst (cantorUnpair k)) ∧ᵇ β (snd (cantorUnpair k))
        -- = α n ∧ᵇ β m (by cantorUnpair-pair)
        -- = true ∧ᵇ true = true
        γk=t : γ k ≡ true
        γk=t =
          γ k
            ≡⟨ cong (λ p → α (fst p) and β (snd p)) (cantorUnpair-pair n m) ⟩
          α n and β m
            ≡⟨ cong (λ x → x and β m) αn=t ⟩
          true and β m
            ≡⟨ cong (true and_) βm=t ⟩
          true ∎
    in (k , γk=t)

  backward : Σ[ k ∈ ℕ ] γ k ≡ true → ⟨ P ⟩ × ⟨ Q ⟩
  backward (k , γk=t) =
    let (n , m) = cantorUnpair k
        -- γ k = α n ∧ᵇ β m = true means both α n = true and β m = true
        αn∧βm=t : α n and β m ≡ true
        αn∧βm=t = γk=t
        αn=t : α n ≡ true
        αn=t = and-true-left (α n) (β m) αn∧βm=t
        βm=t : β m ≡ true
        βm=t = and-true-right (α n) (β m) αn∧βm=t
    in (∃α→P (n , αn=t)) , (∃β→Q (m , βm=t))
    where
    and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
    and-true-left true true _ = refl
    and-true-left true false p = ex-falso (false≢true p)
    and-true-left false true p = ex-falso (false≢true p)
    and-true-left false false p = ex-falso (false≢true p)

    and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
    and-true-right true true _ = refl
    and-true-right true false p = ex-falso (false≢true p)
    and-true-right false true p = ex-falso (false≢true p)
    and-true-right false false p = ex-falso (false≢true p)

-- Bundled version: meet (∧) on Open
_∧-Open_ : Open → Open → Open
O₁ ∧-Open O₂ = ((⟨ fst O₁ ⟩ × ⟨ fst O₂ ⟩) , isProp× (snd (fst O₁)) (snd (fst O₂))) ,
               openAnd (fst O₁) (fst O₂) (snd O₁) (snd O₂)

-- Bundled version: meet (∧) on Closed
_∧-Closed_ : Closed → Closed → Closed
C₁ ∧-Closed C₂ = ((⟨ fst C₁ ⟩ × ⟨ fst C₂ ⟩) , isProp× (snd (fst C₁)) (snd (fst C₂))) ,
                 closedAnd (fst C₁) (fst C₂) (snd C₁) (snd C₂)

-- =============================================================================
-- Closed propositions are closed under disjunction (uses LLPO)
-- =============================================================================

-- The key equivalence used to prove closedOr:
-- For closed P, Q: P ∨ Q ↔ ¬(¬P ∧ ¬Q)
-- - ¬P and ¬Q are open (by negClosedIsOpen with MP)
-- - ¬P ∧ ¬Q is open (by openAnd)
-- - ¬(¬P ∧ ¬Q) is closed (by negOpenIsClosed)
-- - The backward direction ¬(¬P ∧ ¬Q) → P ∨ Q needs LLPO

-- First-true truncation: given a sequence, produce one that hits true at most once
-- (at the position of the first true in the original, if any)
-- Using explicit Bool case analysis to help with definitional equality
firstTrue : binarySequence → binarySequence
firstTrue α zero = α zero
firstTrue α (suc n) with α zero
... | true = false
... | false = firstTrue (α ∘ suc) n

-- firstTrue preserves never-hitting-true (all false → all false)
firstTrue-preserves-allFalse : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
                             → (n : ℕ) → firstTrue α n ≡ false
firstTrue-preserves-allFalse α allF zero = allF zero
firstTrue-preserves-allFalse α allF (suc n) with α zero | allF zero
... | true  | α0=f = ex-falso (false≢true (sym α0=f))
... | false | _    = firstTrue-preserves-allFalse (α ∘ suc) (allF ∘ suc) n

-- firstTrue sequence hits true at most once
firstTrue-hitsAtMostOnce : (α : binarySequence) → hitsAtMostOnce (firstTrue α)
firstTrue-hitsAtMostOnce α m n ftm=t ftn=t = aux α m n ftm=t ftn=t
  where
  aux : (α : binarySequence) → (m n : ℕ) → firstTrue α m ≡ true → firstTrue α n ≡ true → m ≡ n
  aux α zero zero _ _ = refl
  aux α zero (suc n) ft0=t ft-sn=t with α zero
  aux α zero (suc n) ft0=t ft-sn=t | true = ex-falso (false≢true ft-sn=t)
  aux α zero (suc n) ft0=t ft-sn=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) zero ft-sm=t ft0=t with α zero
  aux α (suc m) zero ft-sm=t ft0=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) zero ft-sm=t ft0=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t with α zero
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | false = cong suc (aux (α ∘ suc) m n ft-sm=t ft-sn=t)

-- Key lemma: firstTrue α n = true implies α n = true (and all earlier are false)
firstTrue-true-implies-original-true : (α : binarySequence) (n : ℕ)
                                      → firstTrue α n ≡ true → α n ≡ true
firstTrue-true-implies-original-true α zero ft0=t = ft0=t
firstTrue-true-implies-original-true α (suc n) ft-sn=t with α zero
... | true  = ex-falso (false≢true ft-sn=t)
... | false = firstTrue-true-implies-original-true (α ∘ suc) n ft-sn=t

-- Key lemma: if firstTrue α n = false but α n = true, then some earlier position hit true
-- Using witness: we return the position m as a natural number and prove m < n separately
private
  firstTrue-with : (α : binarySequence) (n : ℕ) (b : Bool)
                  → α zero ≡ b
                  → firstTrue α (suc n) ≡ (if b then false else firstTrue (α ∘ suc) n)
  firstTrue-with α n true  p with α zero
  ... | true = refl
  ... | false = ex-falso (true≢false (sym p))
  firstTrue-with α n false p with α zero
  ... | true = ex-falso (false≢true (sym p))
  ... | false = refl

firstTrue-false-but-original-true : (α : binarySequence) (n : ℕ)
                                   → firstTrue α n ≡ false → α n ≡ true
                                   → Σ[ m ∈ ℕ ] (suc m ≤ n) × (α m ≡ true)
firstTrue-false-but-original-true α zero ft0=f α0=t = ex-falso (true≢false (sym α0=t ∙ ft0=f))
firstTrue-false-but-original-true α (suc n) ft-sn=f α-sn=t with α zero =B true
... | yes α0=t = zero , suc-≤-suc zero-≤ , α0=t
... | no α0≠t =
  let α0=f = ¬true→false (α zero) α0≠t
      eq : firstTrue α (suc n) ≡ firstTrue (α ∘ suc) n
      eq = firstTrue-with α n false α0=f ∙ refl
      ft-sn=f' : firstTrue (α ∘ suc) n ≡ false
      ft-sn=f' = sym eq ∙ ft-sn=f
      (m , m<n , αsm=t) = firstTrue-false-but-original-true (α ∘ suc) n ft-sn=f' α-sn=t
  in suc m , suc-≤-suc m<n , αsm=t

-- De Morgan law for closed propositions (consequence of LLPO)
-- This is the key step: ¬(¬P ∧ ¬Q) → ∥P ⊎ Q∥₁ for closed P, Q
closedDeMorgan : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
               → ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
closedDeMorgan P Q (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) ¬¬P∧¬Q =
  let -- Interleave α and β, then apply firstTrue to get an ℕ∞ element
      δ₀ : binarySequence
      δ₀ = interleave α β

      δ : binarySequence
      δ = firstTrue δ₀

      -- δ hits true at most once by construction
      δ-hamo : hitsAtMostOnce δ
      δ-hamo = firstTrue-hitsAtMostOnce δ₀

      -- δ as element of ℕ∞
      δ∞ : ℕ∞
      δ∞ = δ , δ-hamo

      -- Apply LLPO
      llpo-result : ((k : ℕ) → δ (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → δ (suc (2 ·ℕ k)) ≡ false)
      llpo-result = llpo δ∞

      -- Analyze the result
      -- Case 1: All evens of δ are false
      --   δ(2k) = firstTrue(interleave α β)(2k)
      --   If all these are false, then either:
      --   - All αk are false (P holds), or
      --   - Some βm was true before any αk was true
      --   Either way, we can derive P or Q

      -- Case 2: All odds of δ are false
      --   Similar reasoning gives P or Q

  -- The full proof requires careful case analysis
  -- For now, we extract the result using ¬¬P∧¬Q
  in helper llpo-result
  where
  -- Key lemma: if all evens of firstTrue(interleave α β) are false,
  -- and some αk = true, then some earlier βm = true (so Q fails)
  -- Therefore, by ¬(¬P ∧ ¬Q), P must hold.
  --
  -- Actually, simpler approach:
  -- If all evens of δ are false:
  --   - Either all αk are false (so P holds by ∀α→P), OR
  --   - Some αk = true, but was blocked, meaning some odd came first
  --     In this case, that odd position had interleave α β = βm = true for some m
  --     Since firstTrue preserves this, δ at that odd position is true
  --     But then we'd have a true in the sequence...
  --
  -- The key insight: we use ¬(¬P ∧ ¬Q) together with closed stability.
  -- If LLPO tells us all evens are false, we reason:
  -- - Suppose P doesn't hold (¬P). Then ∃k. αk = true.
  -- - Since ¬(¬P ∧ ¬Q) and we have ¬P, we must have ¬¬Q.
  -- - Since Q is closed, Q is ¬¬-stable, so Q holds.
  -- Similarly for the other case.

  -- Key lemma: if all evens of δ are false, then P holds
  -- Proof outline:
  -- 1. If all evens of firstTrue(interleave α β) are false, and interleave hits true
  --    somewhere, then the FIRST true position must be at an odd index.
  -- 2. If first true is at odd position 2j+1, then β(j) = true, so ¬Q.
  -- 3. Suppose ¬P. Then some αk = true, so interleave hits true at even 2k.
  -- 4. By (1), the first true is at an odd position, so ¬Q.
  -- 5. ¬P ∧ ¬Q contradicts ¬(¬P ∧ ¬Q).

  -- Helper: extract first true position using well-founded recursion on <
  -- The key fact is that firstTrue-false-but-original-true gives m < n
  module _ where
    open WF.WFI (<-wellfounded)

    ResultOdd : ℕ → Type₀
    ResultOdd n = interleave α β n ≡ true
                → ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
                → Σ[ m ∈ ℕ ] (isEvenB m ≡ false) × (β (half m) ≡ true)

    find-first-true-odd-step : (n : ℕ) → ((m : ℕ) → m < n → ResultOdd m) → ResultOdd n
    find-first-true-odd-step n rec δ₀-n=t allEvensF with firstTrue (interleave α β) n =B true
    ... | yes ft-n=t with isEvenB n =B true
    ...   | yes n-even =
            let k = half n
                2k=n : 2 ·ℕ k ≡ n
                2k=n = 2·half-even n n-even
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true) (sym 2k=n) ft-n=t)
                                     ∙ allEvensF k))
    ...   | no n-odd =
            let j = half n
                m-odd-eq : isEvenB n ≡ false
                m-odd-eq = ¬true→false (isEvenB n) n-odd
                βj=t : β j ≡ true
                βj=t = sym (interleave-odd α β n m-odd-eq) ∙ δ₀-n=t
            in n , m-odd-eq , βj=t
    find-first-true-odd-step n rec δ₀-n=t allEvensF | no ft-n≠t =
      let ft-n=f = ¬true→false (firstTrue (interleave α β) n) ft-n≠t
          (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n ft-n=f δ₀-n=t
      in rec m m<n δ₀-m=t allEvensF

    find-first-true-odd : (n : ℕ) → ResultOdd n
    find-first-true-odd = induction find-first-true-odd-step

  allEvensF-implies-P : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false) → ⟨ P ⟩
  allEvensF-implies-P allEvensF = closedIsStable P (α , P→∀α , ∀α→P) ¬¬P
    where
    ¬¬P : ¬ ¬ ⟨ P ⟩
    ¬¬P ¬p =
      let -- From ¬P, get witness that α has a true
          (k , αk=t) = mp α (λ all-false → ¬p (∀α→P all-false))
          -- interleave α β (2k) = αk = true
          δ₀-2k=t : interleave α β (2 ·ℕ k) ≡ true
          δ₀-2k=t = interleave-2k α β k ∙ αk=t
          -- Find first true; it must be at an odd position
          (m , m-odd , βj=t) = find-first-true-odd (2 ·ℕ k) δ₀-2k=t allEvensF
          j = half m
          -- So β(j) = true, meaning Q fails
          ¬q : ¬ ⟨ Q ⟩
          ¬q q = false≢true (sym (Q→∀β q j) ∙ βj=t)
      in ¬¬P∧¬Q (¬p , ¬q)

  -- Similarly: if all odds of δ are false, then Q holds
  module _ where
    open WF.WFI (<-wellfounded)

    ResultEven : ℕ → Type₀
    ResultEven n = interleave α β n ≡ true
                 → ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
                 → Σ[ m ∈ ℕ ] (isEvenB m ≡ true) × (α (half m) ≡ true)

    find-first-true-even-step : (n : ℕ) → ((m : ℕ) → m < n → ResultEven m) → ResultEven n
    find-first-true-even-step n rec δ₀-n=t allOddsF with firstTrue (interleave α β) n =B true
    ... | yes ft-n=t with isEvenB n =B true
    ...   | yes n-even =
            let j = half n
                αj=t : α j ≡ true
                αj=t = sym (interleave-even α β n n-even) ∙ δ₀-n=t
            in n , n-even , αj=t
    ...   | no n-odd =
            let k = half n
                n-odd-eq : isEvenB n ≡ false
                n-odd-eq = ¬true→false (isEvenB n) n-odd
                2k+1=n : suc (2 ·ℕ k) ≡ n
                2k+1=n = suc-2·half-odd n n-odd-eq
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true) (sym 2k+1=n) ft-n=t)
                                     ∙ allOddsF k))
    find-first-true-even-step n rec δ₀-n=t allOddsF | no ft-n≠t =
      let ft-n=f = ¬true→false (firstTrue (interleave α β) n) ft-n≠t
          (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n ft-n=f δ₀-n=t
      in rec m m<n δ₀-m=t allOddsF

    find-first-true-even : (n : ℕ) → ResultEven n
    find-first-true-even = induction find-first-true-even-step

  allOddsF-implies-Q : ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false) → ⟨ Q ⟩
  allOddsF-implies-Q allOddsF = closedIsStable Q (β , Q→∀β , ∀β→Q) ¬¬Q
    where
    ¬¬Q : ¬ ¬ ⟨ Q ⟩
    ¬¬Q ¬q =
      let (k , βk=t) = mp β (λ all-false → ¬q (∀β→Q all-false))
          δ₀-odd-k=t : interleave α β (suc (2 ·ℕ k)) ≡ true
          δ₀-odd-k=t = interleave-2k+1 α β k ∙ βk=t
          (m , m-even , αj=t) = find-first-true-even (suc (2 ·ℕ k)) δ₀-odd-k=t allOddsF
          j = half m
          ¬p : ¬ ⟨ P ⟩
          ¬p p = false≢true (sym (P→∀α p j) ∙ αj=t)
      in ¬¬P∧¬Q (¬p , ¬q)

  -- From LLPO result, derive P ∨ Q
  helper : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
         ⊎ ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
         → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  helper (inl allEvensF) = ∣ inl (allEvensF-implies-P allEvensF) ∣₁
  helper (inr allOddsF) = ∣ inr (allOddsF-implies-Q allOddsF) ∣₁

-- Now we can define closedOr
closedOr : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
         → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
closedOr P Q Pclosed Qclosed = γ , forward , backward
  where
  -- ¬P and ¬Q are open (since P, Q are closed and we have MP)
  ¬P : hProp ℓ-zero
  ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

  ¬Q : hProp ℓ-zero
  ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

  ¬Popen : isOpenProp ¬P
  ¬Popen = negClosedIsOpen mp P Pclosed

  ¬Qopen : isOpenProp ¬Q
  ¬Qopen = negClosedIsOpen mp Q Qclosed

  -- ¬P ∧ ¬Q is open (by openAnd)
  ¬P∧¬Q : hProp ℓ-zero
  ¬P∧¬Q = ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) , isProp× (isProp¬ ⟨ P ⟩) (isProp¬ ⟨ Q ⟩)

  ¬P∧¬Qopen : isOpenProp ¬P∧¬Q
  ¬P∧¬Qopen = openAnd ¬P ¬Q ¬Popen ¬Qopen

  -- The witness for ∥P ⊎ Q∥₁ being closed is the same as for ¬P ∧ ¬Q being open
  γ : binarySequence
  γ = fst ¬P∧¬Qopen

  -- Forward: ∥P ⊎ Q∥₁ → ∀k. γk = false
  forward : ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ → (n : ℕ) → γ n ≡ false
  forward P∨Q n with γ n =B true
  ... | yes γn=t = ex-falso (PT.rec isProp⊥ (helper γn=t) P∨Q)
    where
    helper : γ n ≡ true → ⟨ P ⟩ ⊎ ⟨ Q ⟩ → ⊥
    helper γn=t (inl p) = fst (snd (snd ¬P∧¬Qopen) (n , γn=t)) p
    helper γn=t (inr q) = snd (snd (snd ¬P∧¬Qopen) (n , γn=t)) q
  ... | no γn≠t = ¬true→false (γ n) γn≠t

  -- Backward: ∀k. γk = false → ∥P ⊎ Q∥₁
  backward : ((n : ℕ) → γ n ≡ false) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  backward all-false =
    let ¬¬P∧¬Q : ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩))
        ¬¬P∧¬Q (¬p , ¬q) =
          let (n , γn=t) = fst (snd ¬P∧¬Qopen) (¬p , ¬q)
          in false≢true (sym (all-false n) ∙ γn=t)
    in closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q

-- Bundled version: join (∨) on Open
_∨-Open_ : Open → Open → Open
O₁ ∨-Open O₂ = ((∥ ⟨ fst O₁ ⟩ ⊎ ⟨ fst O₂ ⟩ ∥₁) , squash₁) ,
               openOr (fst O₁) (fst O₂) (snd O₁) (snd O₂)

-- Bundled version: join (∨) on Closed
_∨-Closed_ : Closed → Closed → Closed
C₁ ∨-Closed C₂ = ((∥ ⟨ fst C₁ ⟩ ⊎ ⟨ fst C₂ ⟩ ∥₁) , squash₁) ,
                 closedOr (fst C₁) (fst C₂) (snd C₁) (snd C₂)

-- De Morgan for open propositions: ¬(P ∧ Q) ↔ ∥¬P ⊎ ¬Q∥₁
-- This is a consequence of closedDeMorgan (which uses LLPO)
-- since ¬P and ¬Q are closed when P and Q are open.
-- (tex line 716)
openDeMorgan : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
             → (¬ (⟨ P ⟩ × ⟨ Q ⟩)) ↔ ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
openDeMorgan P Q Popen Qopen = forward , backward
  where
  -- ¬P is closed because P is open
  ¬Pclosed : isClosedProp (¬hProp P)
  ¬Pclosed = negOpenIsClosed P Popen

  -- ¬Q is closed because Q is open
  ¬Qclosed : isClosedProp (¬hProp Q)
  ¬Qclosed = negOpenIsClosed Q Qopen

  -- Forward: ¬(P ∧ Q) → ∥¬P ⊎ ¬Q∥₁
  -- This follows from closedDeMorgan for ¬P, ¬Q which are closed
  -- ¬(P ∧ Q) = ¬(¬¬P ∧ ¬¬Q) since P, Q are open hence ¬¬-stable
  -- Use closedDeMorgan: ¬(¬(¬P) ∧ ¬(¬Q)) → ∥¬P ⊎ ¬Q∥₁
  forward : ¬ (⟨ P ⟩ × ⟨ Q ⟩) → ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
  forward ¬P×Q = closedDeMorgan (¬hProp P) (¬hProp Q) ¬Pclosed ¬Qclosed ¬¬¬P×¬¬Q
    where
    -- Need: ¬(¬¬P × ¬¬Q) which follows from ¬(P × Q) by ¬¬-stability of P and Q
    Pstable : ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
    Pstable = openIsStable mp P Popen

    Qstable : ¬ ¬ ⟨ Q ⟩ → ⟨ Q ⟩
    Qstable = openIsStable mp Q Qopen

    ¬¬¬P×¬¬Q : ¬ ((¬ ¬ ⟨ P ⟩) × (¬ ¬ ⟨ Q ⟩))
    ¬¬¬P×¬¬Q (¬¬p , ¬¬q) = ¬P×Q (Pstable ¬¬p , Qstable ¬¬q)

  -- Backward: ∥¬P ⊎ ¬Q∥₁ → ¬(P ∧ Q) is trivial
  backward : ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁ → ¬ (⟨ P ⟩ × ⟨ Q ⟩)
  backward = PT.rec (isProp¬ _) λ
    { (inl ¬p) (p , _) → ¬p p
    ; (inr ¬q) (_ , q) → ¬q q
    }

-- Flattening a family of sequences into a single sequence
flatten : (ℕ → binarySequence) → binarySequence
flatten αs k = let (m , n) = cantorUnpair k in αs m n

-- Countable intersection of closed propositions
-- If each Pₙ is closed (witnessed by αₙ), then ∀n.Pₙ is closed
closedCountableIntersection : (P : ℕ → hProp ℓ-zero)
                            → ((n : ℕ) → isClosedProp (P n))
                            → isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
closedCountableIntersection P αs = β , forward , backward
  where
  -- Get witness sequence for each Pₙ
  αP : ℕ → binarySequence
  αP n = fst (αs n)

  -- Flatten to single sequence
  β : binarySequence
  β = flatten αP

  forward : ((n : ℕ) → ⟨ P n ⟩) → (k : ℕ) → β k ≡ false
  forward allP k =
    let (m , n) = cantorUnpair k
        Pm→allFalse = fst (snd (αs m))
    in Pm→allFalse (allP m) n

  backward : ((k : ℕ) → β k ≡ false) → (n : ℕ) → ⟨ P n ⟩
  backward allβFalse n = allFalse→Pn allαnFalse
    where
    allFalse→Pn : ((k : ℕ) → αP n k ≡ false) → ⟨ P n ⟩
    allFalse→Pn = snd (snd (αs n))
    -- β (cantorPair n k) = αP (fst (cantorUnpair (cantorPair n k))) (snd (cantorUnpair (cantorPair n k)))
    -- By cantorUnpair-pair: cantorUnpair (cantorPair n k) = (n, k)
    -- So β (cantorPair n k) ≡ αP n k (by path)
    allαnFalse : (k : ℕ) → αP n k ≡ false
    allαnFalse k =
      αP n k
        ≡⟨ cong (λ p → αP (fst p) (snd p)) (sym (cantorUnpair-pair n k)) ⟩
      αP (fst (cantorUnpair (cantorPair n k))) (snd (cantorUnpair (cantorPair n k)))
        ≡⟨ allβFalse (cantorPair n k) ⟩
      false ∎

-- Countable union of open propositions (requires MP)
-- If each Pₙ is open (witnessed by αₙ), then ∃n.Pₙ is open
openCountableUnion : (P : ℕ → hProp ℓ-zero)
                   → ((n : ℕ) → isOpenProp (P n))
                   → isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ , squash₁)
openCountableUnion P αs = β , forward , backward
  where
  -- Get witness sequence for each Pₙ
  αP : ℕ → binarySequence
  αP n = fst (αs n)

  -- Flatten to single sequence
  β : binarySequence
  β = flatten αP

  backward : Σ[ k ∈ ℕ ] β k ≡ true → ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁
  backward (k , βk=t) = ∣ n , Pn ∣₁
    where
    nm : ℕ × ℕ
    nm = cantorUnpair k
    n = fst nm
    m = snd nm
    αnm=t : αP n m ≡ true
    αnm=t = βk=t
    exists→Pn = snd (snd (αs n))
    Pn : ⟨ P n ⟩
    Pn = exists→Pn (m , αnm=t)

  -- Use Markov to extract witness from double negation
  forward : ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ → Σ[ k ∈ ℕ ] β k ≡ true
  forward truncExists = mp β ¬allFalse
    where
    ¬allFalse : ¬ ((k : ℕ) → β k ≡ false)
    ¬allFalse allFalse = PT.rec isProp⊥ helper truncExists
      where
      helper : Σ[ n ∈ ℕ ] ⟨ P n ⟩ → ⊥
      helper (n , pn) =
        let Pn→exists = fst (snd (αs n))
            (m , αnm=t) = Pn→exists pn
            k = cantorPair n m
            -- β k = αP (fst (cantorUnpair k)) (snd (cantorUnpair k))
            -- = αP (fst (cantorUnpair (cantorPair n m))) (snd (cantorUnpair (cantorPair n m)))
            -- ≡ αP n m (by cantorUnpair-pair)
            -- ≡ true (by αnm=t)
            βk=t : β k ≡ true
            βk=t =
              β k
                ≡⟨ refl ⟩
              αP (fst (cantorUnpair k)) (snd (cantorUnpair k))
                ≡⟨ cong (λ p → αP (fst p) (snd p)) (cantorUnpair-pair n m) ⟩
              αP n m
                ≡⟨ αnm=t ⟩
              true ∎
        in false≢true (sym (allFalse k) ∙ βk=t)

-- Bundled version: countable intersection on Closed
⋀-Closed : (ℕ → Closed) → Closed
⋀-Closed Cs = (((n : ℕ) → ⟨ fst (Cs n) ⟩) , isPropΠ (λ n → snd (fst (Cs n)))) ,
              closedCountableIntersection (λ n → fst (Cs n)) (λ n → snd (Cs n))

-- Bundled version: countable union on Open
⋁-Open : (ℕ → Open) → Open
⋁-Open Os = ((∥ Σ[ n ∈ ℕ ] ⟨ fst (Os n) ⟩ ∥₁) , squash₁) ,
            openCountableUnion (λ n → fst (Os n)) (λ n → snd (Os n))

-- =============================================================================
-- Section 18: Additional properties of open and closed propositions
-- =============================================================================

-- If a proposition is both open and closed, it is decidable
-- (ClopenDecidable from tex Corollary 774)
--
-- Proof from tex:
-- If P is open and closed, then P ∨ ¬P is open (P is open, ¬P is open since P is closed and MP gives ¬closed = open)
-- Open propositions are ¬¬-stable (by openIsStable)
-- ¬¬(P ∨ ¬P) is provable
-- Therefore P ∨ ¬P, i.e., P is decidable
--
-- We need: openOr P (¬P) where ¬P is open (from negClosedIsOpen)

-- Helper: P ⊎ ¬P is a proposition when P is
isProp⊎¬ : (P : hProp ℓ-zero) → isProp (⟨ P ⟩ ⊎ (¬ ⟨ P ⟩))
isProp⊎¬ P (inl p) (inl p') = cong inl (snd P p p')
isProp⊎¬ P (inl p) (inr ¬p) = ex-falso (¬p p)
isProp⊎¬ P (inr ¬p) (inl p) = ex-falso (¬p p)
isProp⊎¬ P (inr ¬p) (inr ¬p') = cong inr (isProp¬ ⟨ P ⟩ ¬p ¬p')

clopenIsDecidable : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp P → Dec ⟨ P ⟩
clopenIsDecidable P Popen Pclosed =
  let -- ¬P is open because P is closed (and we have MP)
      ¬P : hProp ℓ-zero
      ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

      ¬Popen : isOpenProp ¬P
      ¬Popen = negClosedIsOpen mp P Pclosed

      -- ∥ P ∨ ¬P ∥₁ is open (finite disjunction of opens)
      P∨¬P-trunc : hProp ℓ-zero
      P∨¬P-trunc = (∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁) , squash₁

      P∨¬P-trunc-open : isOpenProp P∨¬P-trunc
      P∨¬P-trunc-open = openOr P ¬P Popen ¬Popen

      -- ¬¬∥P ∨ ¬P∥₁ is provable
      ¬¬P∨¬P-trunc : ¬ ¬ ∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁
      ¬¬P∨¬P-trunc k = k ∣ inr (λ p → k ∣ inl p ∣₁) ∣₁

      -- Open propositions are ¬¬-stable
      P∨¬P-trunc-holds : ∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁
      P∨¬P-trunc-holds = openIsStable mp P∨¬P-trunc P∨¬P-trunc-open ¬¬P∨¬P-trunc

      -- Extract from truncation (P ⊎ ¬P is already a prop)
      P∨¬P-holds : ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩)
      P∨¬P-holds = PT.rec (isProp⊎¬ P) (λ x → x) P∨¬P-trunc-holds

  in ⊎-rec (λ p → yes p) (λ ¬p → no ¬p) P∨¬P-holds
  where
  ⊎-rec : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
  ⊎-rec f g (inl a) = f a
  ⊎-rec f g (inr b) = g b

-- Corollary: P is decidable ↔ P is both open and closed
-- Forward: decIsOpen and decIsClosed (defined earlier)
-- Backward: clopenIsDecidable (above)
-- This matches tex's statement: "Every decidable proposition is both open and closed"
-- and ClopenDecidable (Corollary 774)

-- If P is open and Q is closed, then P → Q is closed
-- (ImplicationOpenClosed from tex Lemma 857)
--
-- Proof idea:
-- P → Q ↔ ¬P ∨ Q (classically)
-- ¬P is closed (since P is open, by negOpenIsClosed)
-- Q is closed (by assumption)
-- ¬P ∨ Q is closed (by closedOr, which follows from LLPO)
--
-- Alternatively: ¬(P ∧ ¬Q), and P ∧ ¬Q is open...
--
-- Proof: (P → Q) ↔ ¬(P ∧ ¬Q)
-- - P is open (given)
-- - ¬Q is open (by negClosedIsOpen, since Q is closed)
-- - P ∧ ¬Q is open (by openAnd)
-- - ¬(P ∧ ¬Q) is closed (by negOpenIsClosed)
-- - Show (P → Q) ↔ ¬(P ∧ ¬Q) via De Morgan

implicationOpenClosed : (P Q : hProp ℓ-zero) → isOpenProp P → isClosedProp Q
                      → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
implicationOpenClosed P Q Popen Qclosed = γ , forward , backward
  where
  -- ¬Q is open (since Q is closed and we have MP)
  ¬Q : hProp ℓ-zero
  ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

  ¬Qopen : isOpenProp ¬Q
  ¬Qopen = negClosedIsOpen mp Q Qclosed

  -- P ∧ ¬Q is open (by openAnd)
  P∧¬Q : hProp ℓ-zero
  P∧¬Q = (⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)

  P∧¬Qopen : isOpenProp P∧¬Q
  P∧¬Qopen = openAnd P ¬Q Popen ¬Qopen

  -- ¬(P ∧ ¬Q) is closed (by negOpenIsClosed)
  ¬P∧¬Qclosed : isClosedProp (¬hProp P∧¬Q)
  ¬P∧¬Qclosed = negOpenIsClosed P∧¬Q P∧¬Qopen

  -- The witness for (P → Q) being closed is the same as for ¬(P ∧ ¬Q)
  γ : binarySequence
  γ = fst ¬P∧¬Qclosed

  -- Forward: (P → Q) → ∀k. γk = false
  -- Equivalent to: (P → Q) → ¬(P ∧ ¬Q) [easy]
  forward : (⟨ P ⟩ → ⟨ Q ⟩) → (n : ℕ) → γ n ≡ false
  forward p→q = fst (snd ¬P∧¬Qclosed) ¬P∧¬Q-holds
    where
    ¬P∧¬Q-holds : ¬ (⟨ P ⟩ × (¬ ⟨ Q ⟩))
    ¬P∧¬Q-holds (p , ¬q) = ¬q (p→q p)

  -- Backward: ∀k. γk = false → (P → Q)
  -- Equivalent to: ¬(P ∧ ¬Q) → (P → Q) [needs Q being ¬¬-stable when P holds]
  backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ → ⟨ Q ⟩
  backward all-false p =
    let ¬P∧¬Q-holds : ¬ (⟨ P ⟩ × (¬ ⟨ Q ⟩))
        ¬P∧¬Q-holds = snd (snd ¬P∧¬Qclosed) all-false
        -- Since ¬(P ∧ ¬Q) and P holds, we must have ¬¬Q
        ¬¬Q : ¬ ¬ ⟨ Q ⟩
        ¬¬Q ¬q = ¬P∧¬Q-holds (p , ¬q)
        -- Q is closed, so ¬¬Q → Q
    in closedIsStable (⟨ Q ⟩ , snd Q) Qclosed ¬¬Q

-- Dual of implicationOpenClosed (from tex Lemma 857):
-- If P is closed and Q is open, then P → Q is open
-- Proof: P → Q ↔ ¬P ∨ Q. ¬P is open (since P closed), Q is open, so ¬P ∨ Q is open.
-- The equivalence uses ¬¬-stability of both sides.
implicationClosedOpen : (P Q : hProp ℓ-zero) → isClosedProp P → isOpenProp Q
                      → isOpenProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
implicationClosedOpen P Q Pclosed Qopen = α , forward , backward
  where
  -- ¬P is open (since P is closed)
  ¬P : hProp ℓ-zero
  ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

  ¬Popen : isOpenProp ¬P
  ¬Popen = negClosedIsOpen mp P Pclosed

  -- ∥¬P ∨ Q∥₁ is open (using openOr)
  ¬P∨Q-prop : hProp ℓ-zero
  ¬P∨Q-prop = (∥ ⟨ ¬P ⟩ ⊎ ⟨ Q ⟩ ∥₁) , squash₁

  ¬P∨Q-open : isOpenProp ¬P∨Q-prop
  ¬P∨Q-open = openOr ¬P Q ¬Popen Qopen

  -- The witness for P → Q being open is the same as for ∥¬P ∨ Q∥₁
  α : binarySequence
  α = fst ¬P∨Q-open

  -- Helper: get ∥¬P ∨ Q∥₁ from P → Q using ¬¬-stability
  get¬P∨Q : (⟨ P ⟩ → ⟨ Q ⟩) → ∥ (¬ ⟨ P ⟩) ⊎ ⟨ Q ⟩ ∥₁
  get¬P∨Q p→q = openIsStable mp ¬P∨Q-prop ¬P∨Q-open ¬¬disj
    where
    ¬¬disj : ¬ ¬ ∥ (¬ ⟨ P ⟩) ⊎ ⟨ Q ⟩ ∥₁
    ¬¬disj k = k ∣ inr (p→q (closedIsStable P Pclosed (λ ¬p → k ∣ inl ¬p ∣₁))) ∣₁

  -- Forward: (P → Q) → ∃k. αk = true
  forward : (⟨ P ⟩ → ⟨ Q ⟩) → Σ[ k ∈ ℕ ] α k ≡ true
  forward p→q = fst (snd ¬P∨Q-open) (get¬P∨Q p→q)

  -- Backward: ∃k. αk = true → (P → Q)
  backward : Σ[ k ∈ ℕ ] α k ≡ true → ⟨ P ⟩ → ⟨ Q ⟩
  backward (k , αk=t) p = PT.rec (snd Q) extractQ (snd (snd ¬P∨Q-open) (k , αk=t))
    where
    extractQ : (¬ ⟨ P ⟩) ⊎ ⟨ Q ⟩ → ⟨ Q ⟩
    extractQ (inl ¬p) = ex-falso (¬p p)
    extractQ (inr q) = q

-- ClosedMarkov (from tex, Lemma 807):
-- For (Pₙ)_{n:ℕ} closed propositions: ¬(∀n. Pₙ) ↔ ∃n. ¬Pₙ
--
-- Proof: Both sides are open, hence ¬¬-stable.
-- The equivalence follows by classical De Morgan + ¬¬-stability.
closedMarkovTex : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n))
                → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
closedMarkovTex P Pclosed = forward , backward
  where
  -- ∀n. Pₙ is closed
  ∀P-closed : isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
  ∀P-closed = closedCountableIntersection P Pclosed

  -- ¬(∀n. Pₙ) is open (negation of closed)
  ¬∀P-open : isOpenProp ((¬ ((n : ℕ) → ⟨ P n ⟩)) , isProp¬ _)
  ¬∀P-open = negClosedIsOpen mp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n))) ∀P-closed

  -- Each ¬Pₙ is open (negation of closed)
  ¬Pn-open : (n : ℕ) → isOpenProp ((¬ ⟨ P n ⟩) , isProp¬ _)
  ¬Pn-open n = negClosedIsOpen mp (P n) (Pclosed n)

  -- ∃n. ¬Pₙ is open (countable union of open)
  ∃¬P-open : isOpenProp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁)
  ∃¬P-open = openCountableUnion (λ n → (¬ ⟨ P n ⟩) , isProp¬ _) ¬Pn-open

  -- Forward: ¬(∀n. Pₙ) → ∃n. ¬Pₙ
  -- Use ¬¬-stability: ¬(∀n. Pₙ) → ¬¬(∃n. ¬Pₙ), and ∃n. ¬Pₙ is open hence ¬¬-stable
  forward : ¬ ((n : ℕ) → ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
  forward ¬∀P =
    let ¬¬∃¬P : ¬ ¬ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
        ¬¬∃¬P k = ¬∀P (λ n →
          -- Suppose Pₙ fails for all n (contradiction with ¬∀P)
          -- Use closedness: ¬¬Pₙ → Pₙ
          closedIsStable (P n) (Pclosed n)
            (λ ¬Pn → k ∣ n , ¬Pn ∣₁))
    in openIsStable mp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁) ∃¬P-open ¬¬∃¬P

  -- Backward: ∃n. ¬Pₙ → ¬(∀n. Pₙ)
  -- This direction is constructively trivial
  backward : ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ → ¬ ((n : ℕ) → ⟨ P n ⟩)
  backward = PT.rec (isProp¬ _) (λ { (n , ¬Pn) ∀P → ¬Pn (∀P n) })

-- Dual of closedMarkovTex for open propositions:
-- For open (Pₙ)_{n:ℕ}, we have ¬(∃n. Pₙ) ↔ ∀n. ¬Pₙ
--
-- This is simpler than closedMarkovTex because:
-- - ∃n. Pn is open (by openCountableUnion)
-- - ¬(∃n. Pn) is closed (by negOpenIsClosed)
-- - Each ¬Pn is closed (by negOpenIsClosed)
-- - ∀n. ¬Pn is closed (by closedCountableIntersection)
-- - Both sides are closed hence ¬¬-stable
--
-- Actually, this direction is trivially true constructively (no axioms needed):
-- ¬(∃n. Pn) ↔ ∀n. ¬Pn is just the usual ¬∃↔∀¬ equivalence.
openMarkovTex : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isOpenProp (P n))
             → (¬ ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁) ↔ ((n : ℕ) → ¬ ⟨ P n ⟩)
openMarkovTex P Popen = forward , backward
  where
  forward : ¬ ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ → (n : ℕ) → ¬ ⟨ P n ⟩
  forward ¬∃P n pn = ¬∃P ∣ n , pn ∣₁

  backward : ((n : ℕ) → ¬ ⟨ P n ⟩) → ¬ ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁
  backward ∀¬P = PT.rec isProp⊥ (λ { (n , pn) → ∀¬P n pn })

-- =============================================================================
-- Section 19: Stone Spaces
-- =============================================================================

-- Recall from Axioms.StoneDuality:
-- hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S
-- Stone = TypeWithStr ℓ-zero hasStoneStr
--
-- A Stone space is a type S equipped with a countably presented Boolean algebra B
-- such that S ≡ Sp(B) (the spectrum of B).

-- The spectrum of a Boolean algebra B is the type of Boolean homomorphisms B → 2
-- Sp B = BoolHom B Bool

-- Key properties of Stone spaces (from tex):
-- 1. Stone spaces are profinite: they are sequential limits of finite sets
-- 2. Stone propositions are exactly closed propositions
-- 3. Stone spaces are closed under finite limits

-- The Cantor space 2^ℕ is Stone (spectrum of the free BA on ℕ)
-- ℕ_∞ is Stone (spectrum of B_∞, the BA generated by orthogonal generators)

-- =============================================================================
-- Section 20: Transitivity of openness and closedness
-- =============================================================================

-- Transitivity of openness (tex Corollary 1319-1322)
-- If V ⊆ T is open and W ⊆ V is open, then W ⊆ T is open.
-- In the propositional case: if P is open and Q : P → Open, then Σ P Q is open.
-- This follows from open propositions being closed under dependent sums.

-- Open propositions are stable under conjunction with a fixed true proposition
-- If P holds and Q is open, then P × Q is open (equivalent to Q via P)
openAndFixed : (P : Type₀) → (isPropP : isProp P) → P
              → (Q : hProp ℓ-zero) → isOpenProp Q
              → isOpenProp ((P × ⟨ Q ⟩) , isProp× isPropP (snd Q))
openAndFixed P isPropP p Q Qopen =
  let (α , Q→∃ , ∃→Q) = Qopen
  in α , (λ pq → Q→∃ (snd pq)) , (λ x → p , ∃→Q x)

-- Closed propositions are stable under conjunction with a fixed true proposition
-- If P holds and Q is closed, then P × Q is closed (equivalent to Q via P)
closedAndFixed : (P : Type₀) → (isPropP : isProp P) → P
                → (Q : hProp ℓ-zero) → isClosedProp Q
                → isClosedProp ((P × ⟨ Q ⟩) , isProp× isPropP (snd Q))
closedAndFixed P isPropP p Q Qclosed =
  let (α , Q→∀ , ∀→Q) = Qclosed
  in α , (λ pq → Q→∀ (snd pq)) , (λ x → p , ∀→Q x)

-- =============================================================================
-- Section 21: Dependent sums of open/closed propositions
-- =============================================================================

-- Open propositions over a decidable base
-- If D is decidable and Q : D → Open, then Σ D Q is open
-- Proof: by case split on D
--   - If D holds (d), then Σ D Q ↔ Q d (which is open)
--   - If ¬D, then Σ D Q ↔ ⊥ (which is open)
-- For decidable D with witness d, the truncated sigma is equivalent to Q d
-- So we can use the same openness witness, adjusting the conversions appropriately
-- The key is using MP to extract a witness from double negation
openSigmaDecidable : (D : hProp ℓ-zero) → Dec ⟨ D ⟩
                   → (Q : ⟨ D ⟩ → hProp ℓ-zero) → ((d : ⟨ D ⟩) → isOpenProp (Q d))
                   → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
openSigmaDecidable D (yes d) Q Qopen = α , forward , backward
  where
  -- Use the witness for Q d
  α = Qopen d .fst
  Qd→∃ = fst (snd (Qopen d))
  ∃→Qd = snd (snd (Qopen d))

  -- Forward: use MP to extract witness from double negation
  forward : ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward truncExists = mp α ¬allFalse
    where
    ¬allFalse : ¬ ((n : ℕ) → α n ≡ false)
    ¬allFalse allFalse = PT.rec isProp⊥ helper truncExists
      where
      helper : Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ → ⊥
      helper (d' , q) =
        let q' = subst (λ x → ⟨ Q x ⟩) (snd D d' d) q
            (n , αn=t) = Qd→∃ q'
        in false≢true (sym (allFalse n) ∙ αn=t)

  -- Backward: Σ n, α n = true → ∥ Σ D Q ∥₁
  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁
  backward w = ∣ d , ∃→Qd w ∣₁

openSigmaDecidable D (no ¬d) Q Qopen = α , forward , backward
  where
  -- When ¬D, ∥ Σ D Q ∥₁ ↔ ⊥ (which is open with constant false witness)
  α = ⊥-isOpen .fst

  forward : ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward x = ex-falso (PT.rec isProp⊥ (λ { (d , _) → ¬d d }) x)

  -- α n = false for all n, so Σ n, α n = true is empty
  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁
  backward (n , αn=t) = ex-falso (true≢false (sym αn=t))

-- Closed propositions over a decidable base
-- If D is decidable and Q : D → Closed, then Σ D Q is closed
closedSigmaDecidable : (D : hProp ℓ-zero) → Dec ⟨ D ⟩
                     → (Q : ⟨ D ⟩ → hProp ℓ-zero) → ((d : ⟨ D ⟩) → isClosedProp (Q d))
                     → isClosedProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
closedSigmaDecidable D (yes d) Q Qclosed =
  let (α , Qd→∀ , ∀→Qd) = Qclosed d
      forward : ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁ → (n : ℕ) → α n ≡ false
      forward = PT.rec (isPropΠ (λ _ → isSetBool _ _))
                       (λ { (d' , q) → Qd→∀ (subst (λ x → ⟨ Q x ⟩) (snd D d' d) q) })
      backward : ((n : ℕ) → α n ≡ false) → ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁
      backward w = ∣ d , ∀→Qd w ∣₁
  in α , forward , backward
closedSigmaDecidable D (no ¬d) Q Qclosed =
  -- When ¬D, ∥ Σ D Q ∥₁ ↔ ⊥ (which is closed with constant true witness)
  -- α = λ _ → true, so (∀n. α n = false) implies true = false, contradiction
  let α = ⊥-isClosed .fst  -- α n = true for all n
      backward : ((n : ℕ) → α n ≡ false) → ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁
      backward f = ex-falso (true≢false (f 0))
  in α ,
     (λ x → PT.rec (isPropΠ (λ _ → isSetBool _ _)) (λ { (d , _) → ex-falso (¬d d) }) x) ,
     backward

-- =============================================================================
-- Section 22: Open/Closed under Σ-types (general case)
-- =============================================================================

-- Open propositions are closed under Σ-types (tex Corollary OpenDependentSums 1313)
-- If P is open and Q : P → hProp with each Q(p) open, then Σ P Q is open.
--
-- Proof idea: P open means P ↔ ∃n. (αn = true)
-- Each (αn = true) is decidable, so we can use openSigmaDecidable
-- Then ∥Σ P Q∥₁ ↔ ∥Σn. Σ_{αn=true} Q(witness)∥₁, which is a countable union of opens.

openSigmaOpen : (P : hProp ℓ-zero) → isOpenProp P
              → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isOpenProp (Q p))
              → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
openSigmaOpen P (α , P→∃ , ∃→P) Q Qopen = result
  where
  -- For each n, the proposition (α n = true) is decidable
  Dn : ℕ → hProp ℓ-zero
  Dn n = (α n ≡ true) , isSetBool _ _

  Dn-dec : (n : ℕ) → Dec (α n ≡ true)
  Dn-dec n = α n =B true

  -- For each n with αn = true, we have a canonical witness of P
  witness : (n : ℕ) → (α n ≡ true) → ⟨ P ⟩
  witness n = λ eq → ∃→P (n , eq)

  -- For each n, define Rn = Σ_{αn=true} Q(witness(n, _))
  -- This is open by openSigmaDecidable
  Rn : ℕ → hProp ℓ-zero
  Rn n = (∥ Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ ∥₁) , squash₁

  Rn-open : (n : ℕ) → isOpenProp (Rn n)
  Rn-open n = openSigmaDecidable (Dn n) (Dn-dec n)
                (λ eq → Q (witness n eq))
                (λ eq → Qopen (witness n eq))

  -- ∥Σn. Rn∥₁ is open by openCountableUnion
  countableUnionOpen : isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁ , squash₁)
  countableUnionOpen = openCountableUnion Rn Rn-open

  -- Now show ∥Σ P Q∥₁ ↔ ∥Σn. Rn∥₁
  -- Forward: (p, q) : Σ P Q → get (n, αn=t) from P→∃ p, then ∣n, ∣αn=t, q'∣₁∣₁
  forward-equiv : ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ → ∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁
  forward-equiv = PT.rec squash₁ helper
    where
    helper : Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁
    helper (p , qp) = ∣ n , ∣ αn=t , qp' ∣₁ ∣₁
      where
      n = fst (P→∃ p)
      αn=t = snd (P→∃ p)
      p' = witness n αn=t
      p≡p' = snd P p p'
      qp' : ⟨ Q (witness n αn=t) ⟩
      qp' = subst (λ x → ⟨ Q x ⟩) p≡p' qp

  -- Backward: (n, ∣αn=t, q∣₁) → ∣witness n αn=t, q∣₁
  backward-equiv : ∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁ → ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁
  backward-equiv = PT.rec squash₁ helper1
    where
    helper1 : Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ → ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁
    helper1 (n , rn) = PT.rec squash₁ helper2 rn
      where
      helper2 : Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ → ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁
      helper2 (αn=t , qw) = ∣ witness n αn=t , qw ∣₁

  -- Use the equivalence to transfer openness
  -- Inline the openEquiv logic: if P ↔ Q and P is open, then Q is open
  result : isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  result =
    let (β , union→∃ , ∃→union) = countableUnionOpen
    in β ,
       (λ sigPQ → union→∃ (forward-equiv sigPQ)) ,
       (λ w → backward-equiv (∃→union w))

-- Closed propositions are closed under Σ-types (tex Corollary ClosedDependentSums 1785)
-- If P is closed and Q : P → hProp with each Q(p) closed, then Σ P Q is closed.
--
-- Proof from tex: Closed propositions are Stone (as propositions), and
-- the Σ of Stone spaces is Stone, so Σ P Q is Stone hence closed.
--
-- TODO: This requires Stone space infrastructure (tex Cor 1629: closed props are Stone,
-- tex Cor 1776-1782: Σ of Stone over Stone is Stone, tex 1613-1619: truncation of Stone is closed).
-- The key difficulty: we cannot define the witness β : binarySequence without having
-- a concrete element of P, but isClosedProp requires exhibiting β uniformly.
-- The tex proof uses that closed propositions are Stone spaces, allowing this construction.
-- For now, we postulate this and mark it for completion when Stone infrastructure is added.

postulate
  closedSigmaClosed : (P : hProp ℓ-zero) → isClosedProp P
                    → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isClosedProp (Q p))
                    → isClosedProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
-- {-# WARNING_ON_USAGE closedSigmaClosed "Postulate: requires Stone infrastructure from tex" #-}

-- =============================================================================
-- Section 23: Additional closure properties
-- =============================================================================

-- Open implies ¬¬-stable (via openIsStable which requires MP)
-- This is part of rmkOpenClosedNegation in the tex
open→¬¬stable : (P : hProp ℓ-zero) → isOpenProp P → (¬ ¬ ⟨ P ⟩ → ⟨ P ⟩)
open→¬¬stable P Popen = openIsStable mp P Popen

-- Closed implies ¬¬-stable (directly, no axioms needed)
closed→¬¬stable : (P : hProp ℓ-zero) → isClosedProp P → (¬ ¬ ⟨ P ⟩ → ⟨ P ⟩)
closed→¬¬stable P Pclosed = closedIsStable P Pclosed

-- Forward direction: open → negation is closed
-- (negOpenIsClosed is already defined)

-- Forward direction: closed → negation is open (requires MP)
-- (negClosedIsOpen is already defined)

-- Note: The converse directions require more care:
-- - If ¬P is closed, to show P is open requires showing P ↔ ¬¬P
-- - This only works if P is already known to be open or closed
-- So we don't have a full biconditional characterization

-- For ¬¬-stable propositions: P is closed iff ¬P is open
-- This is because both directions compose nicely when ¬¬P → P
closed→¬open : (P : hProp ℓ-zero) → isClosedProp P → isOpenProp (¬hProp P)
closed→¬open P = negClosedIsOpen mp P

¬open→closed : (P : hProp ℓ-zero) → isOpenProp (¬hProp P) → isClosedProp (¬¬hProp P)
¬open→closed P ¬Popen = negOpenIsClosed (¬hProp P) ¬Popen

-- Equivalence preservation: if P ↔ Q and P is open, then Q is open
openEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
          → isOpenProp P → isOpenProp Q
openEquiv P Q P→Q Q→P (α , P→∃ , ∃→P) =
  α , (λ q → P→∃ (Q→P q)) , (λ w → P→Q (∃→P w))

-- Equivalence preservation: if P ↔ Q and P is closed, then Q is closed
closedEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
            → isClosedProp P → isClosedProp Q
closedEquiv P Q P→Q Q→P (α , P→∀ , ∀→P) =
  α , (λ q → P→∀ (Q→P q)) , (λ w → P→Q (∀→P w))

-- Path transport for open/closed (uses equivalence via paths between hProps)
-- If P ≡ Q as hProps, then isOpenProp P → isOpenProp Q
openPath : {P Q : hProp ℓ-zero} → P ≡ Q → isOpenProp P → isOpenProp Q
openPath {P} {Q} P≡Q Popen = openEquiv P Q (transport (cong fst P≡Q)) (transport (cong fst (sym P≡Q))) Popen

closedPath : {P Q : hProp ℓ-zero} → P ≡ Q → isClosedProp P → isClosedProp Q
closedPath {P} {Q} P≡Q Pclosed = closedEquiv P Q (transport (cong fst P≡Q)) (transport (cong fst (sym P≡Q))) Pclosed

-- =============================================================================
-- Section 23: Decidability characterization
-- =============================================================================

-- Decidable ↔ both open and closed (tex Corollary ClopenDecidable + remark)
-- Forward: a decidable proposition is both open and closed
-- Backward: a proposition that is both open and closed is decidable (clopenIsDecidable)

decidable→open×closed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P × isClosedProp P
decidable→open×closed P dec = decIsOpen P dec , decIsClosed P dec

open×closed→decidable : (P : hProp ℓ-zero) → isOpenProp P × isClosedProp P → Dec ⟨ P ⟩
open×closed→decidable P (Popen , Pclosed) = clopenIsDecidable P Popen Pclosed

-- The biconditional
decidable↔open×closed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ ↔ (isOpenProp P × isClosedProp P)
decidable↔open×closed P = decidable→open×closed P , open×closed→decidable P

-- Corollary: isProp (isOpenProp P × isClosedProp P) when P has decidable equality
-- (we don't prove this since isOpenProp isn't necessarily a prop without more work)

-- =============================================================================
-- Section 24: Open and closed subsets of types (Synthetic Topology viewpoint)
-- =============================================================================

-- Definition (tex line 884-886):
-- A subset A ⊆ T is open (resp. closed) if A(t) is open (resp. closed) for all t:T

isOpenSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isOpenSubset {T} A = (t : T) → isOpenProp (A t)

isClosedSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isClosedSubset {T} A = (t : T) → isClosedProp (A t)

-- The pre-image of an open subset under any map is open (tex remark 889)
-- This shows that all maps are continuous in the synthetic topology sense
preimageOpenIsOpen : {S T : Type₀} (f : S → T) (A : T → hProp ℓ-zero)
                   → isOpenSubset A → isOpenSubset (λ s → A (f s))
preimageOpenIsOpen f A Aopen s = Aopen (f s)

-- Similarly for closed subsets
preimageClosedIsClosed : {S T : Type₀} (f : S → T) (A : T → hProp ℓ-zero)
                       → isClosedSubset A → isClosedSubset (λ s → A (f s))
preimageClosedIsClosed f A Aclosed s = Aclosed (f s)

-- Empty subset is both open and closed
emptySubsetOpen : {T : Type₀} → isOpenSubset {T} (λ _ → ⊥-hProp)
emptySubsetOpen _ = ⊥-isOpen

emptySubsetClosed : {T : Type₀} → isClosedSubset {T} (λ _ → ⊥-hProp)
emptySubsetClosed _ = ⊥-isClosed

-- Full subset (all of T) is both open and closed
fullSubsetOpen : {T : Type₀} → isOpenSubset {T} (λ _ → ⊤-hProp)
fullSubsetOpen _ = ⊤-isOpen

fullSubsetClosed : {T : Type₀} → isClosedSubset {T} (λ _ → ⊤-hProp)
fullSubsetClosed _ = ⊤-isClosed

-- Intersection of open subsets is open
openSubsetIntersection : {T : Type₀} (A B : T → hProp ℓ-zero)
                       → isOpenSubset A → isOpenSubset B
                       → isOpenSubset (λ t → (⟨ A t ⟩ × ⟨ B t ⟩) , isProp× (snd (A t)) (snd (B t)))
openSubsetIntersection A B Aopen Bopen t = openAnd (A t) (B t) (Aopen t) (Bopen t)

-- Intersection of closed subsets is closed
closedSubsetIntersection : {T : Type₀} (A B : T → hProp ℓ-zero)
                         → isClosedSubset A → isClosedSubset B
                         → isClosedSubset (λ t → (⟨ A t ⟩ × ⟨ B t ⟩) , isProp× (snd (A t)) (snd (B t)))
closedSubsetIntersection A B Aclosed Bclosed t = closedAnd (A t) (B t) (Aclosed t) (Bclosed t)

-- Union of open subsets is open (truncated)
openSubsetUnion : {T : Type₀} (A B : T → hProp ℓ-zero)
                → isOpenSubset A → isOpenSubset B
                → isOpenSubset (λ t → (∥ ⟨ A t ⟩ ⊎ ⟨ B t ⟩ ∥₁) , squash₁)
openSubsetUnion A B Aopen Bopen t = openOr (A t) (B t) (Aopen t) (Bopen t)

-- Union of closed subsets is closed (requires LLPO via closedOr)
closedSubsetUnion : {T : Type₀} (A B : T → hProp ℓ-zero)
                  → isClosedSubset A → isClosedSubset B
                  → isClosedSubset (λ t → (∥ ⟨ A t ⟩ ⊎ ⟨ B t ⟩ ∥₁) , squash₁)
closedSubsetUnion A B Aclosed Bclosed t = closedOr (A t) (B t) (Aclosed t) (Bclosed t)

-- Countable intersection of closed subsets is closed
closedSubsetCountableIntersection : {T : Type₀} (A : ℕ → T → hProp ℓ-zero)
                                  → ((n : ℕ) → isClosedSubset (A n))
                                  → isClosedSubset (λ t → ((n : ℕ) → ⟨ A n t ⟩) , isPropΠ (λ n → snd (A n t)))
closedSubsetCountableIntersection A Aclosed t =
  closedCountableIntersection (λ n → A n t) (λ n → Aclosed n t)

-- Countable union of open subsets is open (requires MP via openCountableUnion)
openSubsetCountableUnion : {T : Type₀} (A : ℕ → T → hProp ℓ-zero)
                         → ((n : ℕ) → isOpenSubset (A n))
                         → isOpenSubset (λ t → (∥ Σ[ n ∈ ℕ ] ⟨ A n t ⟩ ∥₁) , squash₁)
openSubsetCountableUnion A Aopen t =
  openCountableUnion (λ n → A n t) (λ n → Aopen n t)

-- Complement of open subset is closed
complementOpenIsClosed : {T : Type₀} (A : T → hProp ℓ-zero)
                       → isOpenSubset A
                       → isClosedSubset (λ t → ¬hProp (A t))
complementOpenIsClosed A Aopen t = negOpenIsClosed (A t) (Aopen t)

-- Complement of closed subset is open (requires MP)
complementClosedIsOpen : {T : Type₀} (A : T → hProp ℓ-zero)
                       → isClosedSubset A
                       → isOpenSubset (λ t → ¬hProp (A t))
complementClosedIsOpen A Aclosed t = negClosedIsOpen mp (A t) (Aclosed t)

-- Transitivity of openness (tex Corollary OpenTransitive 1319)
-- If V ⊆ T is open and W ⊆ V is open (as a subset of V), then W ⊆ T is open.
-- More precisely: given V : T → hProp and W : (t : T) → V(t) → hProp,
-- the composite W'(t) = Σ_{v:V(t)} W(t,v) is open in T.
openSubsetTransitive : {T : Type₀}
                     → (V : T → hProp ℓ-zero) → isOpenSubset V
                     → (W : (t : T) → ⟨ V t ⟩ → hProp ℓ-zero)
                     → ((t : T) (v : ⟨ V t ⟩) → isOpenProp (W t v))
                     → isOpenSubset (λ t → (∥ Σ[ v ∈ ⟨ V t ⟩ ] ⟨ W t v ⟩ ∥₁) , squash₁)
openSubsetTransitive V Vopen W Wopen t =
  openSigmaOpen (V t) (Vopen t) (W t) (Wopen t)

-- Remark: Open forms a dominance (tex Remark OpenDominance 1330)
-- A dominance is a set Σ of propositions that:
-- 1. Contains ⊤ (trivially: ⊤-isOpen)
-- 2. Is closed under Σ-types: if P ∈ Σ and Q : P → Σ, then Σ P Q ∈ Σ (openSigmaOpen)
-- The transitivity property (openSubsetTransitive) follows from the Σ-closure.
-- We have proven both required properties for Open to form a dominance.

-- Transitivity of closedness (dual of openSubsetTransitive)
-- If V ⊆ T is closed and W ⊆ V is closed (as a subset of V), then W ⊆ T is closed.
-- Uses the postulated closedSigmaClosed.
closedSubsetTransitive : {T : Type₀}
                       → (V : T → hProp ℓ-zero) → isClosedSubset V
                       → (W : (t : T) → ⟨ V t ⟩ → hProp ℓ-zero)
                       → ((t : T) (v : ⟨ V t ⟩) → isClosedProp (W t v))
                       → isClosedSubset (λ t → (∥ Σ[ v ∈ ⟨ V t ⟩ ] ⟨ W t v ⟩ ∥₁) , squash₁)
closedSubsetTransitive V Vclosed W Wclosed t =
  closedSigmaClosed (V t) (Vclosed t) (W t) (Wclosed t)

-- Remark: Closed also forms a dominance (tex Remark ClosedDominance 1794)
-- 1. Contains ⊤ (trivially: ⊤-isClosed)
-- 2. Is closed under Σ-types (closedSigmaClosed - currently postulated)
-- Once closedSigmaClosed is proved using Stone infrastructure, Closed forms a dominance.

-- =============================================================================
-- Section: Surjection from 2^ℕ to Closed (tex line 1753)
-- =============================================================================

-- Every binary sequence α defines a closed proposition: (∀n. αn = false)
-- This is stated in tex line 1753: "We have a surjection 2^ℕ → Closed defined by
-- α ↦ ∀n∈ℕ. αn = 0"

-- The proposition (∀n. αn = false) as an hProp
allFalseProp : binarySequence → hProp ℓ-zero
allFalseProp α = ((n : ℕ) → α n ≡ false) , isPropΠ (λ n → isSetBool (α n) false)

-- The surjection 2^ℕ → Closed
binarySeqToClosed : binarySequence → Closed
binarySeqToClosed α = allFalseProp α , allFalseIsClosed α

-- This map is surjective: for any closed proposition, there exists a binary
-- sequence that maps to it (up to equivalence of propositions)
--
-- Given (P, (α, forward, backward)) : Closed, the witness α produces
-- P ↔ (∀n. αn = false), so the image of α under binarySeqToClosed
-- is equivalent to P.

binarySeqToClosed-surjective : (C : Closed) → ∥ Σ[ α ∈ binarySequence ] (⟨ fst C ⟩ ↔ ⟨ fst (binarySeqToClosed α) ⟩) ∥₁
binarySeqToClosed-surjective (P , α , forward , backward) =
  ∣ α , forward , backward ∣₁

-- The dual: surjection 2^ℕ → Open defined by α ↦ ∃n∈ℕ. αn = true
-- (tex remark: open is dual of closed)

-- The proposition (∃n. αn = true) as an hProp (truncated)
someTrueProp : binarySequence → hProp ℓ-zero
someTrueProp α = (∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁) , squash₁

-- The surjection 2^ℕ → Open
binarySeqToOpen : binarySequence → Open
binarySeqToOpen α = someTrueProp α , someTrueIsOpen α

-- This map is surjective: for any open proposition, there exists a binary
-- sequence that maps to it (up to equivalence of propositions)
binarySeqToOpen-surjective : (O : Open) → ∥ Σ[ α ∈ binarySequence ] (⟨ fst O ⟩ ↔ ⟨ fst (binarySeqToOpen α) ⟩) ∥₁
binarySeqToOpen-surjective (P , α , forward , backward) =
  ∣ α , (λ p → ∣ forward p ∣₁) , (λ trunc → backward (fwd trunc)) ∣₁
  where
  fwd : ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  fwd = someTrueIsOpen α .snd .fst

-- =============================================================================
-- Summary of formalization status
-- =============================================================================

-- FULLY PROVED:
-- - isOpenProp, isClosedProp definitions
-- - isSetBinarySequence, isSetIsOpenProp, isSetIsClosedProp: isOpenProp/isClosedProp are sets
-- - isOpen, isClosed: property versions (truncated)
-- - openProp, closedProp, openType, closedType, open→hProp, closed→hProp: projections
-- - ⊥-Open, ⊥-Closed, ⊤-Open, ⊤-Closed: bundled ⊥/⊤
-- - _∧-Open_, _∧-Closed_, _∨-Open_, _∨-Closed_: bundled meet/join
-- - ¬-Open : Open → Closed, ¬-Closed : Closed → Open: bundled negation
-- - ⋀-Closed : (ℕ → Closed) → Closed, ⋁-Open : (ℕ → Open) → Open: countable ops
-- - Bool-equality-*, ℕ-equality-*: equality in Bool/ℕ is decidable/open/closed
-- - CantorSpace-equality-closed: equality in 2^ℕ is closed
-- - negOpenIsClosed, decIsOpen, decIsClosed, decNeg, decProd, decCoprod
-- - closedIsStable, openIsStable (given MP), negClosedIsOpen (given MP)
-- - ⊥-isOpen, ⊥-isClosed : false is both open and closed
-- - ⊤-isOpen, ⊤-isClosed : true is both open and closed
-- - doubleNegOpenIsOpen, doubleNegClosedIsClosed : ¬¬ preserves open/closed (given MP)
-- - closedAnd, openOrMP, openOr (given mp postulate)
-- - closedCountableIntersection, openCountableUnion
-- - openAnd : finite conjunction of opens is open (via Cantor pairing)
-- - Cantor pairing: cantorPair, cantorUnpair, cantorUnpair-pair, cantorPair-unpair
-- - firstTrue: truncation to hit true at most once
-- - clopenIsDecidable : if P is both open and closed, then P is decidable
-- - implicationOpenClosed : (P open, Q closed) → (P → Q) closed
-- - implicationClosedOpen : (P closed, Q open) → (P → Q) open
-- - closedOr : closed props closed under disjunction (using LLPO)
-- - closedDeMorgan : De Morgan for closed props (using LLPO + well-founded recursion)
-- - openDeMorgan : ¬(P ∧ Q) ↔ ∥¬P ⊎ ¬Q∥₁ for open P, Q (tex line 716)
-- - closedMarkovTex : ¬(∀n. Pₙ) ↔ ∃n. ¬Pₙ for closed Pₙ (from tex Lemma 807)
-- - openMarkovTex : ¬(∃n. Pₙ) ↔ ∀n. ¬Pₙ for open Pₙ (dual, trivially true)
-- - ℕ∞ infrastructure: ∞, ι, ι-at-n, ι-at-m≠n, ι≠∞, ι-injective
-- - ℕ∞-Markov, ℕ∞-notInfty→witness, witness→ℕ∞-notInfty (from tex line 500)
-- - ℕ∞-witness-unique, ℕ∞-witness→ι, ∞-char (characterization of ℕ∞ elements)
-- - ℕ∞-equality-closed: equality in ℕ∞ is closed (tex line 1636-1643)
-- - openAndFixed, closedAndFixed: conjunction with fixed true prop preserves open/closed
-- - openSigmaDecidable, closedSigmaDecidable: Σ over decidable base preserves open/closed
-- - openSigmaOpen: Σ of open over open is open (tex Cor 1313)
-- - openSubsetTransitive: transitivity of openness for subsets (tex Cor 1319)
-- - closedSubsetTransitive: transitivity of closedness (uses postulate closedSigmaClosed)
-- Dominance structure (tex Remarks OpenDominance 1330, ClosedDominance 1794):
-- - Open forms a dominance (⊤-isOpen + openSigmaOpen)
-- - Closed forms a dominance (⊤-isClosed + closedSigmaClosed, pending Stone infrastructure)
-- - allFalseIsClosed: canonical closed proposition (∀n. αn = false)
-- - someTrueIsOpen: canonical open proposition (∃n. αn = true) (uses MP)
-- - openPath, closedPath: path transport preserves open/closed
-- Surjections from 2^ℕ (tex line 1753):
-- - allFalseProp, binarySeqToClosed, binarySeqToClosed-surjective
-- - someTrueProp, binarySeqToOpen, binarySeqToOpen-surjective
-- - openEquiv, closedEquiv: equivalence preservation
-- Synthetic Topology (subsets):
-- - isOpenSubset, isClosedSubset definitions
-- - preimageOpenIsOpen, preimageClosedIsClosed: continuity
-- - emptySubsetOpen, emptySubsetClosed, fullSubsetOpen, fullSubsetClosed
-- - openSubsetIntersection, closedSubsetIntersection
-- - openSubsetUnion, closedSubsetUnion
-- - closedSubsetCountableIntersection, openSubsetCountableUnion
-- - complementOpenIsClosed, complementClosedIsOpen

-- AXIOMS (from tex file):
-- - mp : MarkovPrinciple
-- - llpo : LLPO
--
-- POSTULATES (requiring additional infrastructure):
-- - closedSigmaClosed: Σ of closed over closed is closed (tex Cor 1785)
--   Requires Stone space infrastructure to prove properly

-- =============================================================================
-- End of current formalization
-- =============================================================================
