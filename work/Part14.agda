{-# OPTIONS --cubical --guardedness #-}

module work.Part14 where

-- =============================================================================
-- Part 14: StoneClosedSubsetsModule (work.agda lines 10555-11272)
-- =============================================================================

-- Import Part13 for previous definitions
open import work.Part13 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso; invIso; isoToPath)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; invEq; secEq; retEq; equivToIso; invEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ; isOfHLevelΣ)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ renaming (rec to ex-falso)
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (inl; inr; _⊎_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom; invBooleanRingEquiv)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp; isSetBoolHom; StoneDualityAxiom; SDHomVersion; evaluationMap)

-- Note: sd-axiom, SDDecToElemModule, StoneEqualityClosedModule are exported from Part13

-- =============================================================================
-- StoneClosedSubsets (tex Theorem 1648)
-- =============================================================================
--
-- Let A ⊆ S be a subset of a Stone space. The following are equivalent:
-- (i) There exists α : S → 2^ℕ such that A(x) ↔ ∀n. αₓₙ = 0
-- (ii) A = ⋂_{n:ℕ} Dₙ for decidable Dₙ
-- (iii) There exists T : Stone and embedding T → S with image A
-- (iv) There exists T : Stone and map T → S with image A
-- (v) A is closed
--
-- The key directions:
-- (i) ↔ (ii): Immediate from D_n(x) ↔ αₓₙ = 0
-- (ii) → (iii): For S = Sp(B), by SD we have dₙ ∈ B with Dₙ(x) ↔ x(dₙ) = 0.
--               Let C = B/(dₙ). Then Sp(C) → S is an embedding with image A.
-- (iii) → (iv): Trivial (embeddings are maps)
-- (iv) → (ii): For f : T → S with T = Sp(C), the image is Sp(B/Ker(g)) where
--              g : B → C is the corresponding map, and Ker(g) is countably generated.
-- (i) → (v): By definition of closed (countable ∀ of decidable is closed)
-- (v) → (iv): By LocalChoice, lift A : S → Closed through 2^ℕ → Closed

module StoneClosedSubsetsModule where
  open SDDecToElemModule
  open StoneEqualityClosedModule

  -- A subset of a Stone space given by a map α : S → 2^ℕ
  -- A(x) ↔ ∀n. α(x)(n) = false
  record ClosedBySequence (S : Stone) : Type₁ where
    field
      α : fst S → (ℕ → Bool)
      -- The subset A(x) is defined as ∀n. α(x)(n) = false

  -- A subset given by countable intersection of decidable subsets
  record ClosedByCountableIntersection (S : Stone) : Type₁ where
    field
      D : ℕ → fst S → Bool  -- Dₙ(x) is decidable
      -- A(x) = ∀n. D(n)(x) = true (or false, depending on convention)

  -- (i) ↔ (ii): The equivalence between sequence and decidable intersection forms
  -- This is immediate: D_n(x) ↔ α(x)(n) = 0

  -- seq→decIntersection : Given α : S → 2^ℕ, define Dₙ(x) = (α(x)(n) = 0)
  seq→decIntersection : (S : Stone) → ClosedBySequence S → ClosedByCountableIntersection S
  seq→decIntersection S seqForm = record
    { D = λ n x → not (ClosedBySequence.α seqForm x n) }
    -- A(x) = ∀n. α(x)(n) = 0 ↔ ∀n. not(α(x)(n)) = true ↔ ∀n. D(n)(x) = true

  -- decIntersection→seq : Given Dₙ, define α(x)(n) = not(Dₙ(x))
  decIntersection→seq : (S : Stone) → ClosedByCountableIntersection S → ClosedBySequence S
  decIntersection→seq S decForm = record
    { α = λ x n → not (ClosedByCountableIntersection.D decForm n x) }

  -- The subset predicate from a sequence characterization
  subsetFromSeq : (S : Stone) → ClosedBySequence S → (fst S → hProp ℓ-zero)
  subsetFromSeq S seqForm x = ((n : ℕ) → ClosedBySequence.α seqForm x n ≡ false) ,
                              isPropΠ (λ n → isSetBool _ _)

  -- The subset predicate is closed (countable ∀ of decidable is closed)
  subsetFromSeq-isClosed : (S : Stone) (seqForm : ClosedBySequence S)
    → (x : fst S) → isClosedProp (subsetFromSeq S seqForm x)
  subsetFromSeq-isClosed S seqForm x =
    closedCountableIntersection
      (λ n → (ClosedBySequence.α seqForm x n ≡ false) , isSetBool _ _)
      (λ n → Bool-eq-false-isClosed (ClosedBySequence.α seqForm x n))
    where
    -- Helper: equality with false in Bool is closed (because it's decidable)
    Bool-eq-false-isClosed : (b : Bool) → isClosedProp ((b ≡ false) , isSetBool _ _)
    Bool-eq-false-isClosed b = decIsClosed ((b ≡ false) , isSetBool b false) (Bool-equality-decidable b false)

  -- (i) → (v): A subset given by a sequence is closed
  -- This follows from the fact that ∀n.(αₓₙ = 0) is closed
  -- (countable conjunction of decidable props is closed)
  seqForm→closed : (S : Stone) (seqForm : ClosedBySequence S)
    → isClosedSubset (subsetFromSeq S seqForm)
  seqForm→closed S seqForm x = subsetFromSeq-isClosed S seqForm x

  -- Direction (ii) → (iii) requires Stone Duality infrastructure:
  -- For S = Sp(B), given decidable Dₙ, by SD we have dₙ ∈ B with Dₙ(x) ↔ x(dₙ) = 0.
  -- Let C = B/(dₙ)_{n:ℕ}. Then Sp(C) embeds into S with image = ⋂Dₙ.
  --
  -- This requires:
  -- 1. SDDecToElem (have): DecPred on Sp(B) → element of B
  -- 2. QuotientBySeqPreservesBooleω: B/(dₙ)_{n:ℕ} ∈ Booleω

  -- HELPER: The Sp equivalence part (independent of the Booleω structure)
  -- This shows that Sp(B/Im d) ≃ {x : Sp B | ∀n. x(d_n) = 0}
  module SpOfQuotientBySeq (B : BooleanRing ℓ-zero) (d : ℕ → ⟨ B ⟩) where
    -- The quotient ring
    B/d : BooleanRing ℓ-zero
    B/d = B QB./Im d

    -- The quotient map
    π : BoolHom B B/d
    π = QB.quotientImageHom

    -- The closed subset type
    ClosedSubset : Type ℓ-zero
    ClosedSubset = Σ[ x ∈ BoolHom B BoolBR ] ((n : ℕ) → fst x (d n) ≡ false)

    -- Forward: from quotient spectrum to closed subset
    Sp-quotient→ClosedSubset : BoolHom B/d BoolBR → ClosedSubset
    Sp-quotient→ClosedSubset h = h ∘cr π , λ n → zeroOnImage-applied n
      where
      -- h(π(d_n)) = h(0) = 0 because d_n is in the ideal
      zeroOnImage-applied : (n : ℕ) → fst (h ∘cr π) (d n) ≡ false
      zeroOnImage-applied n =
        fst (h ∘cr π) (d n)     ≡⟨ refl ⟩
        fst h (fst π (d n))     ≡⟨ cong (fst h) (QB.zeroOnImage {B = B} {f = d} n) ⟩
        fst h (BooleanRingStr.𝟘 (snd B/d))  ≡⟨ IsCommRingHom.pres0 (snd h) ⟩
        false ∎

    -- Backward: from closed subset to quotient spectrum
    -- Uses inducedHom
    ClosedSubset→Sp-quotient : ClosedSubset → BoolHom B/d BoolBR
    ClosedSubset→Sp-quotient (x , allZero) = QB.inducedHom {B = B} {f = d} BoolBR x allZero

    -- Round-trip 1: forward ∘ backward ≡ id
    -- If we start with (x, allZero), apply inducedHom, then compose with π, we get x back
    forward∘backward : (cs : ClosedSubset) → Sp-quotient→ClosedSubset (ClosedSubset→Sp-quotient cs) ≡ cs
    forward∘backward (x , allZero) = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetBool _ _)) path
      where
      induced = ClosedSubset→Sp-quotient (x , allZero)
      path : fst (Sp-quotient→ClosedSubset induced) ≡ x
      path = QB.evalInduce {B = B} {f = d} BoolBR {x} {allZero}

    -- Round-trip 2: backward ∘ forward ≡ id
    -- Uses inducedHomUnique: the induced hom is the unique hom factoring through π
    backward∘forward : (h : BoolHom B/d BoolBR) → ClosedSubset→Sp-quotient (Sp-quotient→ClosedSubset h) ≡ h
    backward∘forward h = QB.inducedHomUnique BoolBR (h ∘cr π) allZero h refl
      where
      allZero : (n : ℕ) → fst (h ∘cr π) (d n) ≡ false
      allZero = snd (Sp-quotient→ClosedSubset h)

    -- The Iso between Sp(B/d) and ClosedSubset
    Sp-quotient-Iso : Iso (BoolHom B/d BoolBR) ClosedSubset
    Iso.fun Sp-quotient-Iso = Sp-quotient→ClosedSubset
    Iso.inv Sp-quotient-Iso = ClosedSubset→Sp-quotient
    Iso.sec Sp-quotient-Iso = forward∘backward
    Iso.ret Sp-quotient-Iso = backward∘forward

    -- The equivalence
    Sp-quotient-≃ : BoolHom B/d BoolBR ≃ ClosedSubset
    Sp-quotient-≃ = isoToEquiv Sp-quotient-Iso

  -- HELPER: Given an untruncated presentation, construct presentation for quotient by sequence
  module QuotientBySeqPresentation
    (B : BooleanRing ℓ-zero)
    (f : ℕ → ⟨ freeBA ℕ ⟩)
    (equiv : BooleanRingEquiv B (freeBA ℕ QB./Im f))
    (d : ℕ → ⟨ B ⟩)
    where

    -- The quotient we're constructing presentation for
    B/d : BooleanRing ℓ-zero
    B/d = B QB./Im d

    -- The quotient map for B
    π-B : BoolHom B B/d
    π-B = QB.quotientImageHom

    -- The quotient map for freeBA ℕ /Im f
    π-f : BoolHom (freeBA ℕ) (freeBA ℕ QB./Im f)
    π-f = QB.quotientImageHom

    -- The equivalence as a function
    equiv-fun : ⟨ B ⟩ → ⟨ freeBA ℕ QB./Im f ⟩
    equiv-fun = fst (fst equiv)

    -- The inverse equivalence
    equiv-inv : ⟨ freeBA ℕ QB./Im f ⟩ → ⟨ B ⟩
    equiv-inv = fst (invEquiv (fst equiv))

    -- Transport d through the equivalence
    d' : ℕ → ⟨ freeBA ℕ QB./Im f ⟩
    d' n = equiv-fun (d n)

open StoneClosedSubsetsModule public
