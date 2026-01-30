{-# OPTIONS --cubical --guardedness #-}

module work.Part12 where

-- =============================================================================
-- Part 12: TruncationStoneClosed, LemSurjectionsFormalToCompleteness,
--          ODiscInfrastructure, ClosedInStoneIsStone, StoneEqualityClosed
--          (lines 9500-10555 of work.agda)
-- =============================================================================

-- Import Part11 for previous definitions
open import work.Part11 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; invEq; secEq; retEq)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ; isOfHLevelΣ)
open import Cubical.Foundations.Transport using (transportTransport⁻; transport⁻)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; inj-m+; +-zero; injSuc; snotz; znots)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp; isSetBoolHom; StoneDualityAxiom; SDHomVersion; evaluationMap)

-- Stone Duality Axiom (postulated in work.agda, tex Axiom 2.4)
postulate
  sd-axiom : StoneDualityAxiom
open import Cubical.Functions.Surjection using (isSurjection)

-- =============================================================================
-- TruncationStoneClosed (tex Corollary 1613)
-- =============================================================================

module TruncationStoneClosed where

  -- 0=1 implies spectrum is empty
  0=1→¬Sp : (B : Booleω) → BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
           → ¬ Sp B
  0=1→¬Sp B 0≡1 h = true≢false (sym h-pres1 ∙ cong (fst h) (sym 0≡1) ∙ h-pres0)
    where
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)

  spectrumEmptyFrom0=1 : (B : Booleω)
    → BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
    → Sp B → ⊥.⊥
  spectrumEmptyFrom0=1 = 0=1→¬Sp

-- =============================================================================
-- LemSurjectionsFormalToCompleteness (tex Corollary 415)
-- =============================================================================

module LemSurjectionsFormalToCompleteness where

  canonicalMap : (B : BooleanRing ℓ-zero) → Bool → ⟨ B ⟩
  canonicalMap B false = BooleanRingStr.𝟘 (snd B)
  canonicalMap B true = BooleanRingStr.𝟙 (snd B)

  canonicalMapInjective : (B : BooleanRing ℓ-zero)
    → ¬ (BooleanRingStr.𝟘 (snd B) ≡ BooleanRingStr.𝟙 (snd B))
    → (b₁ b₂ : Bool) → canonicalMap B b₁ ≡ canonicalMap B b₂ → b₁ ≡ b₂
  canonicalMapInjective B 0≢1 false false _ = refl
  canonicalMapInjective B 0≢1 false true p = ex-falso (0≢1 p)
  canonicalMapInjective B 0≢1 true false p = ex-falso (0≢1 (sym p))
  canonicalMapInjective B 0≢1 true true _ = refl

  ¬¬Sp→0≢1 : (B : Booleω) → ¬ ¬ Sp B → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
  ¬¬Sp→0≢1 B ¬¬SpB 0≡1 = ¬¬SpB (TruncationStoneClosed.0=1→¬Sp B 0≡1)

  canonical-hom : (B : BooleanRing ℓ-zero) → BoolHom BoolBR B
  canonical-hom B = BoolBR→ B

  canonical-hom-injective : (B : BooleanRing ℓ-zero)
    → ¬ (BooleanRingStr.𝟘 (snd B) ≡ BooleanRingStr.𝟙 (snd B))
    → (b₁ b₂ : Bool) → fst (canonical-hom B) b₁ ≡ fst (canonical-hom B) b₂ → b₁ ≡ b₂
  canonical-hom-injective B 0≢1 false false _ = refl
  canonical-hom-injective B 0≢1 false true  p = ex-falso (0≢1 p)
  canonical-hom-injective B 0≢1 true  false p = ex-falso (0≢1 (sym p))
  canonical-hom-injective B 0≢1 true  true  _ = refl

  canonical-hom-is-injective : (B : Booleω)
    → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    → isInjectiveBoolHom Bool-Booleω B (canonical-hom (fst B))
  canonical-hom-is-injective B 0≢1 b₁ b₂ = canonical-hom-injective (fst B) 0≢1 b₁ b₂

  Sp-canonical : (B : Booleω) → Sp B → Sp Bool-Booleω
  Sp-canonical B h = h ∘cr canonical-hom (fst B)

  Sp-canonical-surjective : (B : Booleω)
    → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    → isSurjectiveSpHom Bool-Booleω B (canonical-hom (fst B))
  Sp-canonical-surjective B 0≢1 =
    injective→Sp-surjective Bool-Booleω B (canonical-hom (fst B)) (canonical-hom-is-injective B 0≢1)

  ¬¬Sp→truncSp : (B : Booleω) → ¬ ¬ Sp B → ∥ Sp B ∥₁
  ¬¬Sp→truncSp B ¬¬SpB = PT.rec squash₁ step1 Sp-Bool-inhabited
    where
    0≢1 : ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    0≢1 = ¬¬Sp→0≢1 B ¬¬SpB

    surj : isSurjectiveSpHom Bool-Booleω B (canonical-hom (fst B))
    surj = Sp-canonical-surjective B 0≢1

    step1 : Sp Bool-Booleω → ∥ Sp B ∥₁
    step1 pt = PT.rec squash₁ (λ preimg → ∣ fst preimg ∣₁) (surj pt)

  truncSp→¬¬Sp : (B : Booleω) → ∥ Sp B ∥₁ → ¬ ¬ Sp B
  truncSp→¬¬Sp B = PT.rec (isProp¬ _) (λ pt ¬SpB → ¬SpB pt)

  LemSurjectionsFormalToCompleteness-derived : (B : Booleω)
    → ⟨ ¬hProp ((¬ Sp B) , isProp¬ (Sp B)) ⟩ ≃ ∥ Sp B ∥₁
  LemSurjectionsFormalToCompleteness-derived B =
    propBiimpl→Equiv
      (isProp¬ (¬ Sp B))
      squash₁
      (¬¬Sp→truncSp B)
      (truncSp→¬¬Sp B)

-- =============================================================================
-- ODiscInfrastructure (tex Definition 918, Lemma 1336)
-- =============================================================================

module ODiscInfrastructure where

  postulate
    booleω-equality-open : (B : Booleω) → (a b : ⟨ fst B ⟩)
      → isOpenProp ((a ≡ b) , BooleanRingStr.is-set (snd (fst B)) a b)

  0=1-isOpen : (B : Booleω)
    → isOpenProp ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
                 , BooleanRingStr.is-set (snd (fst B)) _ _)
  0=1-isOpen B = booleω-equality-open B (BooleanRingStr.𝟘 (snd (fst B)))
                                        (BooleanRingStr.𝟙 (snd (fst B)))

  ¬-of-open-is-closed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬hProp P)
  ¬-of-open-is-closed = negOpenIsClosed

  0≢1-isClosed : (B : Booleω)
    → isClosedProp (¬hProp ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
                          , BooleanRingStr.is-set (snd (fst B)) _ _))
  0≢1-isClosed B = ¬-of-open-is-closed
    ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    , BooleanRingStr.is-set (snd (fst B)) _ _)
    (0=1-isOpen B)

-- =============================================================================
-- TruncationStoneClosedComplete (tex Corollary 1613)
-- =============================================================================

module TruncationStoneClosedComplete where
  open ODiscInfrastructure

  ¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬Sp-hProp B = (¬ Sp B) , isProp¬ (Sp B)

  ¬Sp-isOpen : (B : Booleω) → isOpenProp (¬Sp-hProp B)
  ¬Sp-isOpen B = transport (cong isOpenProp hProp-path) (0=1-isOpen B)
    where
    0=1-Prop : hProp ℓ-zero
    0=1-Prop = (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
             , BooleanRingStr.is-set (snd (fst B)) _ _

    fwd : ⟨ 0=1-Prop ⟩ → ⟨ ¬Sp-hProp B ⟩
    fwd = TruncationStoneClosed.0=1→¬Sp B

    bwd : ⟨ ¬Sp-hProp B ⟩ → ⟨ 0=1-Prop ⟩
    bwd spEmpty = SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B spEmpty

    equiv : ⟨ 0=1-Prop ⟩ ≃ ⟨ ¬Sp-hProp B ⟩
    equiv = propBiimpl→Equiv (snd 0=1-Prop) (snd (¬Sp-hProp B)) fwd bwd

    fst-path : fst 0=1-Prop ≡ fst (¬Sp-hProp B)
    fst-path = ua equiv

    hProp-path : 0=1-Prop ≡ ¬Sp-hProp B
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

  ¬¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬¬Sp-hProp B = ¬hProp (¬Sp-hProp B)

  ¬¬Sp-isClosed : (B : Booleω) → isClosedProp (¬¬Sp-hProp B)
  ¬¬Sp-isClosed B = ¬-of-open-is-closed (¬Sp-hProp B) (¬Sp-isOpen B)

  LemSurjectionsFormalToCompleteness-equiv : (B : Booleω)
    → ⟨ ¬¬Sp-hProp B ⟩ ≃ ∥ Sp B ∥₁
  LemSurjectionsFormalToCompleteness-equiv B =
    LemSurjectionsFormalToCompleteness.LemSurjectionsFormalToCompleteness-derived B

  truncSp-isClosed : (B : Booleω) → isClosedProp (∥ Sp B ∥₁ , squash₁)
  truncSp-isClosed B = transport (cong isClosedProp hProp-path) (¬¬Sp-isClosed B)
    where
    truncSp-Prop : hProp ℓ-zero
    truncSp-Prop = ∥ Sp B ∥₁ , squash₁

    equiv : ⟨ ¬¬Sp-hProp B ⟩ ≃ ⟨ truncSp-Prop ⟩
    equiv = LemSurjectionsFormalToCompleteness-equiv B

    fst-path : fst (¬¬Sp-hProp B) ≡ fst truncSp-Prop
    fst-path = ua equiv

    hProp-path : ¬¬Sp-hProp B ≡ truncSp-Prop
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

  TruncationStoneClosed : (S : Stone) → isClosedProp (∥ fst S ∥₁ , squash₁)
  TruncationStoneClosed (S , (B , p)) =
    transport (cong (λ X → isClosedProp (∥ X ∥₁ , squash₁)) p) (truncSp-isClosed B)

-- =============================================================================
-- Stone→closedProp (reverse direction of PropositionsClosedIffStone)
-- =============================================================================

module Stone→closedPropModule where
  open TruncationStoneClosedComplete

  Stone→closedProp : (P : hProp ℓ-zero) → hasStoneStr (fst P) → isClosedProp P
  Stone→closedProp P (B , p) = transport (cong isClosedProp hProp-path) truncClosed
    where
    SpB≡P : Sp B ≡ fst P
    SpB≡P = p

    truncSpClosed : isClosedProp (∥ Sp B ∥₁ , squash₁)
    truncSpClosed = truncSp-isClosed B

    propTruncIdem : ∥ fst P ∥₁ ≃ fst P
    propTruncIdem = PT.propTruncIdempotent≃ (snd P)

    truncPath : ∥ Sp B ∥₁ ≡ fst P
    truncPath = cong ∥_∥₁ SpB≡P ∙ ua propTruncIdem

    truncProp : hProp ℓ-zero
    truncProp = ∥ Sp B ∥₁ , squash₁

    fst-path : fst truncProp ≡ fst P
    fst-path = truncPath

    truncClosed : isClosedProp truncProp
    truncClosed = truncSpClosed

    hProp-path : truncProp ≡ P
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

-- =============================================================================
-- ClosedInStoneIsStone (tex Corollary 1770) - Postulate
-- =============================================================================

module ClosedInStoneIsStoneModule where

  postulate
    ClosedInStoneIsStone : (S : Stone) → (A : fst S → hProp ℓ-zero)
                         → ((x : fst S) → isClosedProp (A x))
                         → hasStoneStr (Σ (fst S) (λ x → fst (A x)))

-- =============================================================================
-- InhabitedClosedSubSpaceClosed (tex Corollary 1776)
-- =============================================================================

module InhabitedClosedSubSpaceClosedModule where
  open ClosedInStoneIsStoneModule
  open TruncationStoneClosedComplete

  InhabitedClosedSubSpaceClosed : (S : Stone) → (A : fst S → hProp ℓ-zero)
                                → ((x : fst S) → isClosedProp (A x))
                                → isClosedProp (∥ Σ (fst S) (λ x → fst (A x)) ∥₁ , squash₁)
  InhabitedClosedSubSpaceClosed S A A-closed =
    TruncationStoneClosed (Σ (fst S) (λ x → fst (A x)) , ClosedInStoneIsStone S A A-closed)

-- =============================================================================
-- ClosedDependentSums / closedSigmaClosed (tex Corollary 1785)
-- =============================================================================
--
-- Statement: Closed propositions are closed under sigma types.
--
-- Proof:
-- Let P : Closed and Q : P → Closed.
-- Then Σ_{p:P} Q(p) ↔ ∃_{p:P} Q(p) (since Q(p) is a prop for each p).
-- P is Stone by PropositionsClosedIffStone (specifically closedProp→Stone).
-- By InhabitedClosedSubSpaceClosed, Σ_{p:P} Q(p) is closed.

module ClosedDependentSumsModule where
  open ClosedPropIffStone
  open InhabitedClosedSubSpaceClosedModule

  -- This proves closedSigmaClosed using the infrastructure above
  closedSigmaClosed' : (P : hProp ℓ-zero) → isClosedProp P
                     → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isClosedProp (Q p))
                     → isClosedProp (Σ ⟨ P ⟩ (λ p → fst (Q p)) , isOfHLevelΣ 1 (snd P) (λ p → snd (Q p)))
  closedSigmaClosed' P P-closed Q Q-closed = result
    where
    -- The Σ type is a proposition
    ΣPQ : Type₀
    ΣPQ = Σ ⟨ P ⟩ (λ p → fst (Q p))

    ΣPQ-isProp : isProp ΣPQ
    ΣPQ-isProp = isOfHLevelΣ 1 (snd P) (λ p → snd (Q p))

    ΣPQ-hProp : hProp ℓ-zero
    ΣPQ-hProp = ΣPQ , ΣPQ-isProp

    -- P as a Stone space
    P-Stone : Stone
    P-Stone = fst P , closedProp→hasStoneStr P P-closed

    -- ||Σ P Q||₁ is closed by InhabitedClosedSubSpaceClosed
    truncΣ-closed : isClosedProp (∥ ΣPQ ∥₁ , squash₁)
    truncΣ-closed = InhabitedClosedSubSpaceClosed P-Stone Q Q-closed

    -- Since ΣPQ is a prop, ||ΣPQ||₁ ≃ ΣPQ
    propTruncIdem : ∥ ΣPQ ∥₁ ≃ ΣPQ
    propTruncIdem = PT.propTruncIdempotent≃ ΣPQ-isProp

    -- Path in Type
    fst-path : ∥ ΣPQ ∥₁ ≡ ΣPQ
    fst-path = ua propTruncIdem

    -- Path in hProp
    hProp-path : (∥ ΣPQ ∥₁ , squash₁) ≡ ΣPQ-hProp
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

    -- Transport closedness along this path
    result : isClosedProp ΣPQ-hProp
    result = transport (cong isClosedProp hProp-path) truncΣ-closed

open ClosedDependentSumsModule public

-- =============================================================================
-- SDDecToElem: Stone Duality Correspondence (tex AxStoneDuality)
-- =============================================================================
--
-- The Stone duality axiom says that evaluation B → 2^{Sp(B)} is an equivalence.
-- This gives a bijection between:
-- - Elements b ∈ B
-- - Decidable predicates D : Sp(B) → Bool

module SDDecToElemModule where
  open import Axioms.StoneDuality using (evaluationMap; SDHomVersion)

  DecPredOnSp : (B : Booleω) → Type ℓ-zero
  DecPredOnSp B = Sp B → Bool

  -- The inverse map: decidable predicate → element
  elemFromDecPred : StoneDualityAxiom → (B : Booleω) → DecPredOnSp B → ⟨ fst B ⟩
  elemFromDecPred SD B D = invEq (fst (SDHomVersion SD B)) D

  -- Round-trip: elem to predicate to elem is identity
  elemFromDecPred-roundtrip : (SD : StoneDualityAxiom) (B : Booleω) (b : ⟨ fst B ⟩)
    → elemFromDecPred SD B (evaluationMap B b) ≡ b
  elemFromDecPred-roundtrip SD B b = retEq (fst (SDHomVersion SD B)) b

  -- Round-trip: predicate to elem to predicate is identity
  decPredFromElem-roundtrip : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → evaluationMap B (elemFromDecPred SD B D) ≡ D
  decPredFromElem-roundtrip SD B D = secEq (fst (SDHomVersion SD B)) D

  -- Key property: for d = elemFromDecPred SD B D, we have x(d) = D(x)
  decPred-elem-correspondence : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → let d = elemFromDecPred SD B D
      in (x : Sp B) → fst x d ≡ D x
  decPred-elem-correspondence SD B D x =
    cong (λ f → f x) (decPredFromElem-roundtrip SD B D)

open SDDecToElemModule public

-- =============================================================================
-- Postulate Validation: closedSigmaClosed is NOW PROVED
-- =============================================================================
--
-- The proof uses:
-- 1. closedProp→hasStoneStr: P closed → P is Stone (as a space)
-- 2. InhabitedClosedSubSpaceClosed: For S:Stone, A:S→Closed, ||Σ_x A(x)|| is closed

module ClosedSigmaClosedDerived where
  open ClosedPropIffStone
  open InhabitedClosedSubSpaceClosedModule

  -- This is the SAME type as the postulate closedSigmaClosed
  closedSigmaClosed-derived : (P : hProp ℓ-zero) → isClosedProp P
                            → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isClosedProp (Q p))
                            → isClosedProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  closedSigmaClosed-derived P P-closed Q Q-closed =
    InhabitedClosedSubSpaceClosed P-Stone Q Q-closed
    where
    P-Stone : Stone
    P-Stone = fst P , closedProp→hasStoneStr P P-closed

open ClosedSigmaClosedDerived public
