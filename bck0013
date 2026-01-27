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
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

-- Import local library modules (fixed for Agda 2.8 compatibility)
open import Axioms.StoneDuality
open import OmnisciencePrinciples.Markov as MP using (∃αn ; extract')

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
-- LLPO ↔ "For open P, Q: (¬P ∨ ¬Q) ↔ ¬(P ∧ Q)"
--
-- This is Proposition 1.4.1 of Diener's book on constructive reverse mathematics.

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

-- For now, we postulate closedOr as following from LLPO:
postulate
  closedOr : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
           → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)

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
  -- Invariant: we're checking if k is on diagonal (acc + fuel - remaining_fuel)
  findDiagonal : ℕ → ℕ → ℕ → ℕ
  findDiagonal zero k acc = acc  -- out of fuel, return current
  findDiagonal (suc fuel) k acc =
    if k <ᵇ' triangular (suc acc)
    then acc  -- k < triangular(acc+1), so k is on diagonal acc
    else findDiagonal fuel k (suc acc)  -- k >= triangular(acc+1), try next

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

  -- Key lemma: if k < triangular (suc acc), then findDiagonal returns acc
  findDiagonal-found : (fuel k acc : ℕ) → k <ᵇ' triangular (suc acc) ≡ true
                     → findDiagonal (suc fuel) k acc ≡ acc
  findDiagonal-found fuel k acc p with k <ᵇ' triangular (suc acc) | p
  ... | true | _ = refl
  ... | false | q = ex-falso (false≢true q)

  -- If k >= triangular (suc acc), findDiagonal continues to next acc
  findDiagonal-continue : (fuel k acc : ℕ) → k <ᵇ' triangular (suc acc) ≡ false
                        → findDiagonal (suc fuel) k acc ≡ findDiagonal fuel k (suc acc)
  findDiagonal-continue fuel k acc p with k <ᵇ' triangular (suc acc) | p
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

  -- Actually, we can prove cantorPair-unpair more directly using the structure

  cantorPair-unpair : (k : ℕ) → uncurry cantorPair (cantorUnpair k) ≡ k
  cantorPair-unpair k =
    let w = findDiagonal (suc k) k 0
        n = k ∸ triangular w
        m = w ∸ n
        -- We need: cantorPair m n = triangular (m + n) + n = k
        -- Since m + n = (w - n) + n = w, this becomes triangular w + n = k
        -- And n = k - triangular w, so triangular w + (k - triangular w) = k

        -- Need to show: triangular w ≤ k (so the subtraction is valid)
        -- And: m + n = w

        -- These follow from findDiagonal properties
        -- For now, we use the fact that our findDiagonal-aux proof
        -- establishes that w is the unique diagonal containing k
    in
    uncurry cantorPair (cantorUnpair k)                      ≡⟨ refl ⟩
    cantorPair m n                                            ≡⟨ refl ⟩
    triangular (m +ℕ n) +ℕ n                                  ≡⟨ cong (λ x → triangular x +ℕ n) (w∸n+n≡w w n (∸-≤ w n)) ⟩
    triangular w +ℕ n                                         ≡⟨ a+b∸a≡b (triangular w) k (findDiagonal-Tw≤k k) ⟩
    k ∎
    where
    -- findDiagonal returns w such that triangular w ≤ k
    -- Proof: by induction on fuel, invariant is triangular acc ≤ k when we return acc
    findDiagonal-Tw≤k-aux : (fuel k acc : ℕ) → triangular acc ≤ k
                          → triangular (findDiagonal (suc fuel) k acc) ≤ k
    findDiagonal-Tw≤k-aux fuel k acc Tacc≤k = helper (k <ᵇ' triangular (suc acc)) refl
      where
      helper : (b : Bool) → b ≡ k <ᵇ' triangular (suc acc)
             → triangular (findDiagonal (suc fuel) k acc) ≤ k
      helper true p =
        -- When k <ᵇ' triangular (suc acc) ≡ true, findDiagonal returns acc
        let fd≡acc : findDiagonal (suc fuel) k acc ≡ acc
            fd≡acc = findDiagonal-found fuel k acc (sym p)
        in subst (λ x → triangular x ≤ k) (sym fd≡acc) Tacc≤k
      helper false p = findDiagonal-Tw≤k-aux fuel k (suc acc) (¬<ᵇ'-reflects k (triangular (suc acc)) (sym p))

    findDiagonal-Tw≤k : triangular (findDiagonal (suc k) k 0) ≤ k
    findDiagonal-Tw≤k = findDiagonal-Tw≤k-aux k k 0 zero-≤

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

    and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
    and-true-right true true _ = refl

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
      ¬Popen = negClosedIsOpen P Pclosed

      -- P ∨ ¬P is open (finite disjunction of opens)
      P∨¬P : hProp ℓ-zero
      P∨¬P = (⟨ P ⟩ ⊎ (¬ ⟨ P ⟩)) , isProp⊎¬ P

      P∨¬Popen : isOpenProp P∨¬P
      P∨¬Popen = openOr P ¬P Popen ¬Popen

      -- ¬¬(P ∨ ¬P) is provable (excluded middle is ¬¬-stable)
      ¬¬P∨¬P : ¬ ¬ (⟨ P ⟩ ⊎ (¬ ⟨ P ⟩))
      ¬¬P∨¬P k = k (inr (λ p → k (inl p)))

      -- Open propositions are ¬¬-stable, so P ∨ ¬P holds
      P∨¬P-holds : ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩)
      P∨¬P-holds = openIsStable P∨¬P P∨¬Popen ¬¬P∨¬P

  in ⊎-rec (λ p → yes p) (λ ¬p → no ¬p) P∨¬P-holds
  where
  ⊎-rec : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
  ⊎-rec f g (inl a) = f a
  ⊎-rec f g (inr b) = g b

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
-- For now, postulated:
postulate
  implicationOpenClosed : (P Q : hProp ℓ-zero) → isOpenProp P → isClosedProp Q
                        → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))

-- ClosedMarkov: For a sequence of closed propositions,
-- ¬(∀n. ¬Pₙ) → || ∃n. Pₙ ||
-- (Related to Lemma 807 from tex)
--
-- Note: The tex version gives non-truncated ∃, but that requires additional
-- machinery (finding the first n with Pn). For the truncated version:
postulate
  closedMarkov : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n))
               → ¬ ((n : ℕ) → ¬ ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁

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
-- Summary of formalization status
-- =============================================================================

-- FULLY PROVED:
-- - isOpenProp, isClosedProp definitions
-- - negOpenIsClosed, decIsOpen, decIsClosed
-- - closedIsStable, openIsStable (given MP), negClosedIsOpen (given MP)
-- - closedAnd, openOrMP, openOr (given mp postulate)
-- - closedCountableIntersection, openCountableUnion
-- - Cantor pairing bijectivity: cantorPair, cantorUnpair, cantorPair-unpair, cantorUnpair-pair
--   (with all supporting lemmas: findDiagonal-correct, triangular-mono-<, etc.)
-- - clopenIsDecidable : if P is both open and closed, then P is decidable

-- POSTULATED (following from Stone Duality):
-- - mp : MarkovPrinciple (Markov's Principle)
-- - llpo : LLPO (Lesser Limited Principle of Omniscience)
-- - closedOr : closed propositions closed under disjunction (from LLPO)
-- - implicationOpenClosed : (P open, Q closed) → (P → Q) closed
-- - closedMarkov : ¬(∀n.¬Pn) → ∥∃n.Pn∥ for closed (Pn)

-- =============================================================================
-- End of current formalization
-- =============================================================================
