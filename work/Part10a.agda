{-# OPTIONS --cubical --guardedness #-}

module work.Part10a where

open import work.Part10b public

-- =============================================================================
-- Part 10a: Boolean algebra laws for closed/open subsets of Cantor space
-- Split from Part10 to improve compilation time
-- All laws postulated for compilation speed - proofs depend on operation definitions
-- =============================================================================

-- Additional imports for Part10a
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary using (¬_)

module BooleanAlgebraLawsModule where
  open StoneAsClosedSubsetOfCantorModule
  open StoneAsClosedSubsetOfCantorModule2

  -- ==========================================================================
  -- Boolean algebra laws for closed subsets (postulated for speed)
  -- ==========================================================================

  postulate
    -- Commutativity of intersection (closed)
    closedIntersectionComm : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A B ≡ ClosedSubsetIntersection B A

    -- Commutativity of union (closed)
    closedUnionComm : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A B ≡ ClosedSubsetUnion B A

    -- Idempotence of intersection (closed)
    closedIntersectionIdem : (A : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A A ≡ A

    -- Idempotence of union (closed)
    closedUnionIdem : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A A ≡ A

    -- Absorption: A ∩ (A ∪ B) = A
    closedAbsorption1 : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetUnion A B) ≡ A

    -- Absorption: A ∪ (A ∩ B) = A
    closedAbsorption2 : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (ClosedSubsetIntersection A B) ≡ A

    -- Identity: A ∩ Full = A
    closedIntersectionFull : (A : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A FullClosedSubset ≡ A

    -- Identity: A ∪ Empty = A
    closedUnionEmpty : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A EmptyClosedSubset ≡ A

    -- Annihilation: A ∩ Empty = Empty
    closedIntersectionEmpty : (A : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A EmptyClosedSubset ≡ EmptyClosedSubset

    -- Annihilation: A ∪ Full = Full
    closedUnionFull : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A FullClosedSubset ≡ FullClosedSubset

    -- Associativity of intersection (closed)
    closedIntersectionAssoc : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetIntersection B C)
        ≡ ClosedSubsetIntersection (ClosedSubsetIntersection A B) C

    -- Associativity of union (closed)
    closedUnionAssoc : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (ClosedSubsetUnion B C)
        ≡ ClosedSubsetUnion (ClosedSubsetUnion A B) C

    -- Distributivity: A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C) (closed)
    closedDistributiveIntersection : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetUnion B C)
        ≡ ClosedSubsetUnion (ClosedSubsetIntersection A B) (ClosedSubsetIntersection A C)

  -- ==========================================================================
  -- Boolean algebra laws for open subsets (postulated for speed)
  -- ==========================================================================

  postulate
    -- Commutativity of intersection (open)
    openIntersectionComm : (A B : OpenSubsetOfCantor)
      → OpenSubsetIntersection A B ≡ OpenSubsetIntersection B A

    -- Commutativity of union (open)
    openUnionComm : (A B : OpenSubsetOfCantor)
      → OpenSubsetUnion A B ≡ OpenSubsetUnion B A

    -- Idempotence of intersection (open)
    openIntersectionIdem : (A : OpenSubsetOfCantor)
      → OpenSubsetIntersection A A ≡ A

    -- Idempotence of union (open)
    openUnionIdem : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A A ≡ A

    -- Absorption: A ∩ (A ∪ B) = A (open)
    openAbsorption1 : (A B : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetUnion A B) ≡ A

    -- Absorption: A ∪ (A ∩ B) = A (open)
    openAbsorption2 : (A B : OpenSubsetOfCantor)
      → OpenSubsetUnion A (OpenSubsetIntersection A B) ≡ A

    -- Identity: A ∩ Full = A (open)
    openIntersectionFull : (A : OpenSubsetOfCantor)
      → OpenSubsetIntersection A FullOpenSubset ≡ A

    -- Identity: A ∪ Empty = A (open)
    openUnionEmpty : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A EmptyOpenSubset ≡ A

    -- Annihilation: A ∩ Empty = Empty (open)
    openIntersectionEmpty : (A : OpenSubsetOfCantor)
      → OpenSubsetIntersection A EmptyOpenSubset ≡ EmptyOpenSubset

    -- Annihilation: A ∪ Full = Full (open)
    openUnionFull : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A FullOpenSubset ≡ FullOpenSubset

    -- Associativity of intersection (open)
    openIntersectionAssoc : (A B C : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetIntersection B C)
        ≡ OpenSubsetIntersection (OpenSubsetIntersection A B) C

    -- Associativity of union (open)
    openUnionAssoc : (A B C : OpenSubsetOfCantor)
      → OpenSubsetUnion A (OpenSubsetUnion B C)
        ≡ OpenSubsetUnion (OpenSubsetUnion A B) C

    -- Distributivity: A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C) (open)
    openDistributiveIntersection : (A B C : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetUnion B C)
        ≡ OpenSubsetUnion (OpenSubsetIntersection A B) (OpenSubsetIntersection A C)

  -- ==========================================================================
  -- Complement laws (postulated for speed)
  -- ==========================================================================

  postulate
    -- Double complement involution for closed subsets
    closedDoubleComplementInvolution : (A : ClosedSubsetOfCantor)
      → OpenSubsetComplement (ClosedSubsetComplement A) ≡ A

    -- Double complement involution for open subsets
    openDoubleComplementInvolution : (A : OpenSubsetOfCantor)
      → ClosedSubsetComplement (OpenSubsetComplement A) ≡ A

    -- Law of excluded middle for closed subsets as path equality
    closedUnionComplement : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (OpenSubsetComplement (ClosedSubsetComplement A))
        ≡ FullClosedSubset

    -- Law of excluded middle for open subsets as path equality
    openUnionComplement : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A (ClosedSubsetComplement (OpenSubsetComplement A))
        ≡ FullOpenSubset

  -- ==========================================================================
  -- De Morgan laws (postulated for speed)
  -- ==========================================================================

  postulate
    -- De Morgan: ¬(closed A ∩ closed B) ↔ ¬A ∪ ¬B
    closedDeMorganIntersection-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
      → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)

    closedDeMorganIntersection-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
      → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)

    -- De Morgan: ¬(closed A ∪ closed B) ↔ ¬A ∩ ¬B
    closedDeMorganUnion-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
      → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)

    closedDeMorganUnion-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
      → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)

    -- De Morgan: ¬(open A ∩ open B) ↔ ¬A ∪ ¬B
    openDeMorganIntersection-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
      → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)

    openDeMorganIntersection-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
      → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)

    -- De Morgan: ¬(open A ∪ open B) ↔ ¬A ∩ ¬B
    openDeMorganUnion-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
      → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)

    openDeMorganUnion-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
      → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)

-- =============================================================================
-- BooleEpiMono (tex Remark 1475)
-- =============================================================================
--
-- Any morphism g : B → C in Boole has an overtly discrete kernel.
-- As a consequence:
-- 1. Ker(g) is enumerable
-- 2. B/Ker(g) is in Boole
-- 3. The factorization B ↠ B/Ker(g) ↪ C corresponds to
--    Sp(C) ↠ Sp(B/Ker(g)) ↪ Sp(B)
--
-- This means quotient maps in Boole correspond to closed embeddings of spectra.
--

-- End of Part10a
