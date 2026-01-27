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
-- End of current formalization
-- =============================================================================


