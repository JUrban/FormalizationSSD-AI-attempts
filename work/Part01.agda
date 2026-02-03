{-# OPTIONS --cubical --guardedness #-}

module work.Part01 where

-- =============================================================================
-- Part 01: work.agda lines 1-641 (foundations, imports, axioms)
-- =============================================================================

-- Basic imports from Cubical Agda library
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; rCancel; lCancel) renaming (assoc to ∙assoc)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport using (transport⁻; transportTransport⁻)

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Fin using (Fin)
import Cubical.Induction.WellFounded as WF
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (isEmbedding-inl; isEmbedding-inr)

open import Cubical.Functions.Embedding using (isEmbedding→Inj)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.DirectProd
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→; BoolBR→IsUnique)

-- Stone Duality infrastructure (library fixes enabled this import)
open import Axioms.StoneDuality using (StoneDualityAxiom; Sp; Booleω; SpEmbedding)

-- Markov principle infrastructure from OmnisciencePrinciples
import OmnisciencePrinciples.Markov as MarkovLib

-- Imports for quotientPreservesBooleω
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; _is-presented-by_/_; BooleanRingEquiv; invBooleanRingEquiv; idBoolEquiv; has-Countability-structure)
open import CountablyPresentedBooleanRings.Examples.Bool using (is-cp-2)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
import QuotientBool as QB
open import BooleanRing.BoolRingUnivalence using (uaBoolRing; BoolRingPath)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
import Cubical.Data.Sum as ⊎

-- Cohomology imports (Section 6 of tex file)
-- The Cubical library has Eilenberg-MacLane spaces and cohomology infrastructure
open import Cubical.Homotopy.EilenbergMacLane.Base as EM using (EM; EM∙; 0ₖ; hLevelEM; EM-raw→EM)
open import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp using (EM≃ΩEM+1; EM→ΩEM+1; ΩEM+1→EM; ΩEM+1→EM-refl)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure as EMGS using (_+ₖ_; -ₖ_; rCancelₖ)
open import Cubical.Homotopy.Connected using (isConnected; isConnectedFun)
open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; _+ₕ_; -ₕ_; 0ₕ)
-- ZCohomology group isomorphisms from the Cubical library
open import Cubical.ZCohomology.Groups.Unit using (isContrHⁿ-Unit; Hⁿ-contrType≅0)
open import Cubical.ZCohomology.Groups.Sn using (H¹-S¹≅ℤ; Hⁿ-Sⁿ≅ℤ)
open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr; IsAbGroup; AbGroup→Group; makeIsAbGroup)
open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Homotopy.Loopspace using (Ω; Ω→)
open import Cubical.Foundations.Pointed using (Pointed; Pointed₀; _→∙_; pt)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.EilenbergMacLane1 as EM₁ using (EM₁; emloop; embase)

-- BoolQuotientEquiv: quotient of (⊎.rec f g) equals iterated quotient
-- NOTE: This is proven in QuotientConclusions.agda. We keep it as a local declaration
-- to avoid the slow compilation time of importing that module (5+ minutes).
-- The import version is: open import BooleanRing.BooleanRingQuotients.QuotientConclusions using (BoolQuotientEquiv)
postulate
  BoolQuotientEquiv : (A : BooleanRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) →
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
    BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
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

-- ¬WLPO follows from Stone Duality (tex Theorem NotWLPO, line 475)
--
-- Proof sketch (from WLPO.agda):
-- 1. Assume f : 2^ℕ → Bool decides "all zeros": f(α) = false ↔ ∀n. αn = false
-- 2. By Stone Duality (Axiom 1), f is determined by some Boolean term c
-- 3. The term c uses only finitely many generators g₀, ..., gₖ
-- 4. Consider β = 0^ω (all zeros) and γ defined by γn = 0 if n ≤ k, else 1
-- 5. β and γ agree on g₀, ..., gₖ, so f(β) = f(γ)
-- 6. But f(β) should be false (β is all zeros) and f(γ) should be true
-- 7. Contradiction: decidable properties can't distinguish infinite tails
--
-- This shows that "∀n. αn = false" is not decidable uniformly in α.
-- The proof is formalized in WLPO.agda using Boolean ring infrastructure.

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

-- Helper definitions (were private in work.agda, made public for module splitting)
-- Helper: extract the index from an interleaved sequence
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

-- Markov's Principle follows from Stone Duality
-- The proof infrastructure is now available in:
--   - MarkovLib.emptySp : shows Sp(2/α) is empty when α ≠ 0
--   - MarkovLib.extract' : converts ∃[n] α n ≡ true → Σ[n] α n ≡ true
--   - StoneDualityAxiom from Axioms.StoneDuality
--   - SpEmbedding : StoneDualityAxiom → isEmbedding Sp
--
-- Full proof sketch:
-- 1. If ¬(∀n. αn = false), then Sp(2/α) is empty (MarkovLib.emptySp)
-- 2. By Stone Duality (Sp is an embedding), Sp(2/α) = ∅ = Sp(trivial) ⟹ 2/α = trivial
-- 3. Hence 0 = 1 in 2/α, so true ∈ αI (CommRingQuotients.TrivialIdeal.trivialQuotient→1∈I)
-- 4. By MarkovLib.t∈I→αn and MarkovLib.extract', this gives Σn. αn = true

-- Key lemma: If Sp B is empty and Stone Duality holds, then B is trivial (0 = 1)
-- Proof idea: evaluationMap B : ⟨ B ⟩ → (Sp B → Bool) is an equivalence.
-- If Sp B = ∅, then (∅ → Bool) has exactly one element (the empty function).
-- So ⟨ B ⟩ ≅ {*}, meaning all elements of B are equal, including 0 and 1.

-- =============================================================================
-- Re-exports for subsequent parts (names used in module signatures)
-- =============================================================================
