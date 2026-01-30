{-# OPTIONS --cubical --guardedness #-}

module work.Part16 where

-- =============================================================================
-- Part 16: StoneSeparatedModule + CantorIsStoneModule (work.agda lines 11292-11504)
-- =============================================================================

-- Import Part15 for previous definitions
open import work.Part15 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso; invIso; isoToPath)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; invEq; secEq; retEq; equivToIso; invEquiv; fiber; isEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ; isOfHLevelΣ; isProp×)
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ renaming (rec to ex-falso)
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (inl; inr; _⊎_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingTheory)
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom; invBooleanRingEquiv)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp; isSetBoolHom; StoneDualityAxiom; SDHomVersion; evaluationMap)

-- Imports for CantorIsStoneModule
open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
open import CommRingQuotients.TrivialIdeal using (quotientFiber)
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Quotient.Base using (quotientHomSurjective)
open import Cubical.Functions.Surjection
open import Cubical.Tactics.CommRingSolver

-- =============================================================================
-- StoneSeparatedModule (tex lines 11292-11356)
-- =============================================================================
--
-- Disjoint closed subsets of Stone spaces can be separated by clopen sets.

module StoneSeparatedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)
  open StoneClosedSubsetsModule
  open SDDecToElemModule

  -- Type of closed subsets of a Stone space
  ClosedSubsetOfStone : Stone → Type₁
  ClosedSubsetOfStone S = Σ[ A ∈ (fst S → hProp ℓ-zero) ] ((x : fst S) → isClosedProp (A x))

  -- Decidable subset of a Stone space
  DecSubsetOfStone : Stone → Type₀
  DecSubsetOfStone S = fst S → Bool

  -- Membership in decidable subset (D(x) = true)
  _∈Dec_ : {S : Stone} → fst S → DecSubsetOfStone S → Type₀
  x ∈Dec D = D x ≡ true

  -- Membership in closed subset
  _∈Closed_ : {S : Stone} → fst S → ClosedSubsetOfStone S → Type₀
  x ∈Closed (A , _) = fst (A x)

  -- Intersection of closed subsets is empty
  ClosedSubsetsDisjoint : (S : Stone) → ClosedSubsetOfStone S → ClosedSubsetOfStone S → Type₀
  ClosedSubsetsDisjoint S (F , _) (G , _) = (x : fst S) → fst (F x) → fst (G x) → ⊥

  -- Subset containment for closed in decidable
  ClosedSubDec : (S : Stone) → ClosedSubsetOfStone S → DecSubsetOfStone S → Type₀
  ClosedSubDec S (A , _) D = (x : fst S) → fst (A x) → D x ≡ true

  -- Subset containment in complement
  ClosedSubNotDec : (S : Stone) → ClosedSubsetOfStone S → DecSubsetOfStone S → Type₀
  ClosedSubNotDec S (A , _) D = (x : fst S) → fst (A x) → D x ≡ false

  -- The main separation theorem
  -- This is a key property of Stone spaces: disjoint closed subsets can be
  -- separated by clopen (decidable) subsets.
  --
  -- The proof requires:
  -- 1. Representing F, G as countable intersections of decidable subsets
  -- 2. Showing their intersection corresponds to a quotient with empty spectrum
  -- 3. Using SpectrumEmptyIff01Equal to get 1 = ⋁fᵢ ∨ ⋁gⱼ for finite I,J
  -- 4. Constructing D from the finite join ⋁_{j:J} gⱼ
  --
  -- For now, we postulate this as it requires significant infrastructure
  postulate
    StoneSeparated : (S : Stone)
      → (F G : ClosedSubsetOfStone S)
      → ClosedSubsetsDisjoint S F G
      → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S F D) × (ClosedSubNotDec S G D) ∥₁

  -- A useful consequence: closed subsets of Stone are "separated from points"
  -- If F is closed and x ∉ F, there exists a clopen D with F ⊆ D and x ∉ D
  --
  -- Proof: Apply StoneSeparated with G = {x} (singleton, which is closed)
  -- This follows from StoneEqualityClosed: {x} = {y | y = x} is closed
  --
  -- Note: This requires the singleton subset to be closed, which follows from
  -- StoneEqualityClosed (equality in Stone spaces is closed).

  -- Complement of a closed subset is open
  -- This follows from the equivalence: P closed ↔ ¬P open (via closedComplement)
  closedComplementIsOpen : {S : Stone} → (A : ClosedSubsetOfStone S)
    → (x : fst S) → isOpenProp (¬hProp ((fst A) x))
  closedComplementIsOpen (A , Aclosed) x = negClosedIsOpen mp (A x) (Aclosed x)

-- =============================================================================
-- CantorIsStoneModule (tex lines 11387-11504)
-- =============================================================================
--
-- The Cantor space 2^ℕ = (ℕ → Bool) is Stone because:
-- 1. freeBA ℕ (the free Boolean algebra on ℕ) is in Booleω
-- 2. Sp(freeBA ℕ) ≃ (ℕ → Bool) by the universal property
--
-- For (1): We need to show freeBA ℕ is countably presented.
-- freeBA ℕ is presented by generators {gₙ | n : ℕ} and no relations.
-- Quotienting by the constantly-zero function gives the same ring.
--
-- For (2): By freeBA-universal-property, BoolHom (freeBA A) B ≃ (A → ⟨B⟩).
-- So BoolHom (freeBA ℕ) BoolBR ≃ (ℕ → Bool) = CantorSpace.

module CantorIsStoneModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; SpGeneralBooleanRing)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; freeBA-universal-property; generator)
  import QuotientBool as QB
  open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
  open import CommRingQuotients.TrivialIdeal using (quotientFiber)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import Cubical.Algebra.CommRing.Quotient.Base using (quotientHomSurjective)
  open import Cubical.HITs.PropositionalTruncation as PT
  open import Cubical.Data.Sigma using (Σ≡Prop)
  open import Cubical.Functions.Surjection
  open import Cubical.Tactics.CommRingSolver

  -- Open isEquiv to enable copattern matching for equiv-proof
  open isEquiv

  private
    R = BooleanRing→CommRing (freeBA ℕ)
  open BooleanRingStr (snd (freeBA ℕ)) using (𝟘; 𝟙)

  -- The free Boolean algebra on ℕ is Booleω
  -- Proof: We show freeBA ℕ ≃ freeBA ℕ /Im (const 𝟘) where const 𝟘 : ℕ → ⟨freeBA ℕ⟩
  -- Quotienting by the constantly-zero function is the same as quotienting by
  -- the trivial ideal, which gives an equivalent ring.

  -- The key insight: has-Boole-ω' B = Σ[ f ∈ (ℕ → ⟨ freeBA ℕ ⟩) ] BooleanRingEquiv B (freeBA ℕ /Im f)
  -- For freeBA ℕ, we can use f = const 𝟘 (the constantly zero function)

  constZero : ℕ → ⟨ freeBA ℕ ⟩
  constZero _ = BooleanRingStr.𝟘 (snd (freeBA ℕ))

  -- Quotienting by constantly zero is the same as the original ring
  -- (since adding 𝟘 to the ideal doesn't change it - 𝟘 is already in every ideal)
  -- The ideal generated by {𝟘} is the trivial ideal {0r}.
  --
  -- Proof: If x is in the ideal generated by {𝟘}, then
  -- x = sum of terms of form r · 𝟘 = 0r, so x = 0r.
  -- Hence the quotient freeBA ℕ / {𝟘} ≃ freeBA ℕ.

  private
    R' = R IQ./Im constZero
    I' = IQ.genIdeal R constZero
    instance
      _ = snd R'

    π = IQ.quotientImageHom R constZero

    is-set' : isSet ⟨ R' ⟩
    is-set' = CommRingStr.is-set (snd R')

    -- Key lemma: elements in the ideal generated by constZero are 0r
    -- This is because constZero always produces 0r, so:
    -- - isImage: constZero n = 0r, so if 0r ≡ i, then i = 0r
    -- - iszero: trivial
    -- - isSum: 0r + 0r = 0r
    -- - isMul: s · 0r = 0r

    -- Local abbreviations using CommRingStr
    private
      module CRS = CommRingStr (snd R)
    _+R_ = CRS._+_
    _·R_ = CRS._·_
    _-R_ = CRS._-_
    0R = CRS.0r

    trivConstZero : (i : ⟨ R ⟩) → isInIdeal R constZero i → i ≡ 0R
    trivConstZero i (isImage .i n p) = sym p  -- constZero n ≡ i means 0R ≡ i
    trivConstZero i (iszero .i p) = sym p
    trivConstZero i (isSum .i s t i=s+t s∈I t∈I) =
      i           ≡⟨ i=s+t ⟩
      s +R t      ≡⟨ cong₂ _+R_ (trivConstZero s s∈I) (trivConstZero t t∈I) ⟩
      0R +R 0R    ≡⟨ CRS.+IdL 0R ⟩
      0R          ∎
    trivConstZero i (isMul .i s t i=st t∈I) =
      i           ≡⟨ i=st ⟩
      s ·R t      ≡⟨ cong (s ·R_) (trivConstZero t t∈I) ⟩
      s ·R 0R     ≡⟨ RingTheory.0RightAnnihilates (CommRing→Ring R) s ⟩
      0R          ∎

    fiberProp : (c : ⟨ R' ⟩) → isProp (fiber (fst π) c)
    fiberProp c (x , qx=c) (y , qy=c) = Σ≡Prop (λ d → is-set' _ _) help'' where
      help : (x -R y) ∈ fst I'
      help = quotientFiber R I' x y (qx=c ∙ sym qy=c)

      help' : x -R y ≡ 0R
      help' = PT.rec (CRS.is-set _ _) (trivConstZero (x -R y)) (idealDecomp R constZero (x -R y) help)

      -- Direct proof using ring solver: x - y = 0 implies x = y
      help'' : x ≡ y
      help'' = x ≡⟨ solve! R ⟩ (x -R y) +R y ≡⟨ cong (_+R y) help' ⟩ 0R +R y ≡⟨ solve! R ⟩ y ∎

    fiberInhabited : (c : ⟨ R' ⟩) → fiber (fst π) c
    fiberInhabited c = transport (propTruncIdempotent (fiberProp c))
      (quotientHomSurjective R I' c)

  opaque
    unfolding QB._/Im_
    quotientByConstZero≃Original : BooleanRingEquiv (freeBA ℕ) (freeBA ℕ QB./Im constZero)
    fst (fst quotientByConstZero≃Original) = fst π
    equiv-proof (snd (fst quotientByConstZero≃Original)) y = fiberInhabited y , fiberProp y _
    snd quotientByConstZero≃Original = snd π

  freeBA-ℕ-is-Booleω' : has-Boole-ω' (freeBA ℕ)
  freeBA-ℕ-is-Booleω' = constZero , quotientByConstZero≃Original

  freeBA-ℕ-Booleω : Booleω
  freeBA-ℕ-Booleω = freeBA ℕ , ∣ freeBA-ℕ-is-Booleω' ∣₁

  -- The spectrum of freeBA ℕ is CantorSpace
  -- Sp(freeBA ℕ) = BoolHom (freeBA ℕ) BoolBR ≃ (ℕ → Bool) by universal property

  Sp-freeBA-ℕ-Iso : Iso (SpGeneralBooleanRing (freeBA ℕ)) CantorSpace
  Sp-freeBA-ℕ-Iso = invIso (freeBA-universal-property ℕ BoolBR)

  Sp-freeBA-ℕ-≡-Cantor : SpGeneralBooleanRing (freeBA ℕ) ≡ CantorSpace
  Sp-freeBA-ℕ-≡-Cantor = isoToPath Sp-freeBA-ℕ-Iso

  -- Now we can prove CantorIsStone
  -- hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S
  CantorIsStone : hasStoneStr CantorSpace
  CantorIsStone = freeBA-ℕ-Booleω , Sp-freeBA-ℕ-≡-Cantor

open StoneSeparatedModule public
open CantorIsStoneModule public
