{-# OPTIONS --cubical --guardedness #-}

module work.Part09 where

open import work.Part08 public

-- Additional imports for Part09
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; fiber; isEquiv)
open isEquiv
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; isSetBool; not)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom; BooleanRing→CommRing)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; iso; invIso; isoToPath)
open import Cubical.Algebra.CommRing using (CommRing; CommRingHom; IsCommRingHom; CommRingStr; CommRing→Ring)
open import Cubical.Algebra.Ring.Properties using (module RingTheory)

-- =============================================================================
-- Part 09: work.agda lines 11292-11505 (StoneSeparated, CantorIsStone)
-- =============================================================================

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

  -- The main separation theorem (tex Lemma 1824)
  -- This is a key property of Stone spaces: disjoint closed subsets can be
  -- separated by clopen (decidable) subsets.
  --
  -- PROOF OUTLINE (from tex lines 1828-1858):
  -- 1. Assume S = Sp(B) for some B : Booleω
  -- 2. By StoneClosedSubsets, ∃ fₙ,gₙ : B such that:
  --    x ∈ F ↔ ∀n. x(fₙ) = 0  and  y ∈ G ↔ ∀n. y(gₙ) = 0
  -- 3. Define hₖ by h_{2k} = fₖ and h_{2k+1} = gₖ (interleave sequences)
  -- 4. Sp(B/(hₖ)_{k:ℕ}) = F ∩ G = ∅ (quotient has empty spectrum)
  -- 5. By SpectrumEmptyIff01Equal: ∃ finite I,J ⊆ ℕ with 1 = (⋁_{i:I} fᵢ) ∨ (⋁_{j:J} gⱼ)
  -- 6. Define D(x) = (x(⋁_{j:J} gⱼ) = 1) as the separating decidable
  -- 7. If y ∈ F: y(fᵢ) = 0 for all i ∈ I, so y(⋁_{j:J} gⱼ) = 1, hence D(y) = true
  -- 8. If x ∈ G: x(gⱼ) = 0 for all j ∈ J, so x(⋁_{j:J} gⱼ) = 0, hence D(x) = false
  --
  -- DEPENDENCIES:
  -- - StoneClosedSubsets: closed = countable intersection of decidables
  -- - SpOfQuotientBySeq: Sp(B/d) ≃ {x : Sp B | ∀n. x(dₙ) = 0}
  -- - SpectrumEmptyIff01Equal: Sp(B) = ∅ ↔ 0 = 1 in B
  -- - Boolean ring finite joins (⋁ is defined as sum in Boolean ring)
  --
  -- SEE ALSO: Part21.agda StoneSeparatedTC for detailed documentation
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
    → (x : fst S) → isOpenProp (¬hProp (fst A x))
  closedComplementIsOpen (A , Aclosed) x = negClosedIsOpen mp (A x) (Aclosed x)

-- =============================================================================
-- StoneAsClosedSubsetOfCantor (tex Lemma 2082)
-- =============================================================================
--
-- A type X is Stone if and only if it is merely a closed subset of 2^ℕ.
--
-- Proof (from tex):
-- By BooleAsCQuotient, any B : Boole can be written as 2[ℕ]/(rₙ)_{n:ℕ}.
-- By BooleEpiMono, the quotient map induces an embedding Sp(B) ↪ Sp(2[ℕ]) = 2^ℕ.
-- This embedding is closed by StoneClosedSubsets.
--
-- The reverse direction: any closed subset of 2^ℕ is Stone because:
-- - 2^ℕ is Stone (it's Sp(2[ℕ]) where 2[ℕ] = freeBA ℕ is Booleω)
-- - Closed subsets of Stone are Stone (ClosedInStoneIsStone)

-- =============================================================================
-- CantorIsStone: 2^ℕ is a Stone space
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

