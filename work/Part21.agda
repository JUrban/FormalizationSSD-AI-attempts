{-# OPTIONS --cubical --guardedness #-}

module work.Part21 where

open import work.Part20 public

-- =============================================================================
-- Part 21: work.agda lines 25601-26023 (StoneSeparated through CHausStructural)
-- =============================================================================

module StoneSeparatedTC where
  open import Axioms.StoneDuality using (Stone)
  open StoneSeparatedModule

  -- =========================================================================
  -- TEX LEMMA 1824 - StoneSeparated
  -- =========================================================================
  --
  -- STATEMENT (tex lines 1824-1827):
  -- "Assume S : Stone with F,G : S → Closed such that F ∩ G = ∅.
  --  Then there exists a decidable subset D : S → 2 such that F ⊆ D, G ⊆ ¬D."
  --
  -- PROOF SKETCH (tex lines 1828-1858):
  -- 1. Assume S = Sp(B).
  -- 2. By StoneClosedSubsets, for all n:ℕ there exist fₙ,gₙ:B such that:
  --    x ∈ F ↔ ∀n. x(fₙ) = 0 and y ∈ G ↔ ∀n. y(gₙ) = 0
  -- 3. Define hₖ by h_{2k} = fₖ and h_{2k+1} = gₖ
  -- 4. Sp(B/(hₖ)_{k:ℕ}) = F ∩ G = ∅
  -- 5. By SpectrumEmptyIff01Equal, there exist finite sets I,J ⊆ ℕ such that:
  --    1 = (⋁_{i:I} fᵢ) ∨ (⋁_{j:J} gⱼ) in B
  -- 6. Define D(x) = (x(⋁_{j:J} gⱼ) = 1)
  -- 7. If y ∈ F: y(fᵢ) = 0 for all i:I, so y(⋁_{j:J} gⱼ) = 1, hence D(y) = true
  -- 8. If x ∈ G: x(gⱼ) = 0 for all j:J, so x(⋁_{j:J} gⱼ) = 0, hence D(x) = false
  -- Therefore F ⊆ D and G ⊆ ¬D
  --
  -- STATUS: POSTULATED (StoneSeparated at line ~10355)
  --
  -- Dependencies used in proof:
  -- - StoneClosedSubsetsModule.SpOfQuotientBySeq: TYPE-CHECKED
  --   Provides Sp(B/d) ≃ {x : Sp B | ∀n. x(dₙ) = 0}
  -- - SpectrumEmptyIff01Equal: Documented but not directly type-checked as a lemma
  --   The property is used implicitly via quotient Boolean ring machinery
  --
  -- KEY INSIGHT:
  -- The separation property makes Stone spaces "totally disconnected" in the
  -- classical sense: any two disjoint closed sets can be separated by clopens.
  -- This is fundamental for compact Hausdorff separation properties.

  -- Reference the postulated theorem
  StoneSeparated-postulate : (S : Stone)
    → (F G : ClosedSubsetOfStone S)
    → ClosedSubsetsDisjoint S F G
    → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S F D) × (ClosedSubNotDec S G D) ∥₁
  StoneSeparated-postulate = StoneSeparated

  -- =========================================================================
  -- TYPE-CHECKED INFRASTRUCTURE
  -- =========================================================================
  --
  -- The following from StoneSeparatedModule is fully type-checked:
  --
  -- 1. ClosedSubsetOfStone S : Type₁
  --    - Σ[ A ∈ (fst S → hProp) ] ((x : fst S) → isClosedProp (A x))
  --
  -- 2. DecSubsetOfStone S : Type₀
  --    - fst S → Bool (decidable subset as a function to Bool)
  --
  -- 3. Membership predicates:
  --    - _∈Dec_ : x ∈Dec D = (D x ≡ true)
  --    - _∈Closed_ : x ∈Closed (A , _) = fst (A x)
  --
  -- 4. ClosedSubsetsDisjoint S F G : (x : fst S) → F(x) → G(x) → ⊥
  --
  -- 5. ClosedSubDec S F D : (x : fst S) → F(x) → D x ≡ true
  --
  -- 6. ClosedSubNotDec S G D : (x : fst S) → G(x) → D x ≡ false

  -- Re-export key types
  open StoneSeparatedModule public using
    ( ClosedSubsetOfStone
    ; DecSubsetOfStone
    ; ClosedSubsetsDisjoint
    ; ClosedSubDec
    ; ClosedSubNotDec
    ; closedComplementIsOpen
    )

-- =============================================================================
-- CHausFiniteIntersectionPropertyTC (tex Lemma 1981)
-- =============================================================================
--
-- Type-Checked Documentation Module
--
-- This module documents tex Lemma 1981: Compact Hausdorff spaces have the
-- finite intersection property for closed sets.

module CHausFiniteIntersectionPropertyTC where
  open CompactHausdorffModule using (CHaus)
  open CHausFiniteIntersectionPropertyModule

  -- =========================================================================
  -- TEX LEMMA 1981 - CHausFiniteIntersectionProperty
  -- =========================================================================
  --
  -- STATEMENT (tex lines 1981-1984):
  -- "Given X : CHaus and Cₙ : X → Closed closed subsets such that ⋂_{n:ℕ} Cₙ = ∅,
  --  there is some k:ℕ with ⋂_{n≤k} Cₙ = ∅."
  --
  -- PROOF SKETCH (tex lines 1985-2001):
  -- 1. By CompactHausdorffClosed, reduce to Stone case
  -- 2. By StoneClosedSubsets, assume Cₙ decidable
  -- 3. So assume X = Sp(B) and cₙ : B such that:
  --    Cₙ = {x : B → 2 | x(cₙ) = 0}
  -- 4. We have: Sp(B/(cₙ)_{n:ℕ}) ≃ ⋂_{n:ℕ} Cₙ = ∅
  -- 5. Hence 0 = 1 in B/(cₙ)_{n:ℕ}
  -- 6. Therefore there exists k:ℕ with ⋁_{n≤k} cₙ = 1
  -- 7. This means: ∅ = Sp(B/(cₙ)_{n≤k}) ≃ ⋂_{n≤k} Cₙ
  --
  -- STATUS: POSTULATED (CHausFiniteIntersectionProperty at line ~12092)
  --
  -- Dependencies:
  -- - CompactHausdorffClosed: TYPE-CHECKED
  -- - StoneClosedSubsets: TYPE-CHECKED (infrastructure)
  -- - SpectrumEmptyIff01Equal: Used implicitly in quotient machinery
  --
  -- MATHEMATICAL SIGNIFICANCE:
  -- This is the topological "finite intersection property" (FIP) for
  -- compact Hausdorff spaces. It's equivalent to compactness in classical
  -- topology but stated here for countable families of closed sets.

  -- Reference the postulated theorem
  -- The type uses finiteIntersectionClosed from Part11 (CompactHausdorffModule)
  -- which is defined recursively: finiteIntersectionClosed C n x = ⋀_{i≤n} C(i,x)
  CHausFiniteIntersectionProperty-postulate : (X : CHaus)
    → (C : ℕ → fst X → hProp ℓ-zero)
    → ((n : ℕ) (x : fst X) → isClosedProp (C n x))
    → ((x : fst X) → ((n : ℕ) → fst (C n x)) → ⊥)
    → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁
  CHausFiniteIntersectionProperty-postulate = CHausFiniteIntersectionProperty

-- =============================================================================
-- CHausSeperationOfClosedByOpensTC (tex Lemma 2058)
-- =============================================================================
--
-- Type-Checked Documentation Module
--
-- This module documents tex Lemma 2058: Compact Hausdorff spaces are normal.
-- Disjoint closed subsets can be separated by disjoint open neighborhoods.

module CHausSeperationOfClosedByOpensTC where
  open CompactHausdorffModule using (CHaus)
  open CHausSeperationOfClosedByOpensModule

  -- =========================================================================
  -- TEX LEMMA 2058 - CHausSeperationOfClosedByOpens
  -- =========================================================================
  --
  -- STATEMENT (tex lines 2058-2061):
  -- "Assume X : CHaus and A,B ⊆ X closed such that A ∩ B = ∅.
  --  Then there exist U,V ⊆ X open such that A ⊆ U, B ⊆ V and U ∩ V = ∅."
  --
  -- PROOF SKETCH (tex lines 2062-2076):
  -- 1. Let q : S ↠ X be a surjective map with S : Stone
  -- 2. q⁻¹(A) and q⁻¹(B) are closed in S
  -- 3. By StoneSeperated (tex 1824), there exists D : S → 2 such that:
  --    q⁻¹(A) ⊆ D and q⁻¹(B) ⊆ ¬D
  -- 4. Note q(D) and q(¬D) are closed by CompactHausdorffClosed
  -- 5. Since q⁻¹(A) ∩ ¬D = ∅, we have A ⊆ ¬q(¬D) := U
  -- 6. Similarly B ⊆ ¬q(D) := V
  -- 7. U and V are disjoint: ¬q(D) ∩ ¬q(¬D) = ¬(q(D) ∪ q(¬D)) = ¬X = ∅
  --
  -- STATUS: POSTULATED (CHausSeperationOfClosedByOpens at line ~12136)
  --
  -- Dependencies:
  -- - StoneSeparated (tex 1824): POSTULATED
  -- - CompactHausdorffClosed: TYPE-CHECKED
  --
  -- MATHEMATICAL SIGNIFICANCE:
  -- This property makes CHaus spaces "normal" in the topological sense.
  -- It's essential for proving Urysohn's lemma and the Tietze extension theorem.
  -- In Synthetic Stone Duality, it follows from the separation property of
  -- Stone spaces lifted through the CHaus → Stone surjection.

  -- Reference the postulated theorem
  -- The original uses areDisjoint A B = (x : X) → ¬ (fst (A x) × fst (B x))
  -- and subsetOf A B = (x : X) → fst (A x) → fst (B x)
  CHausSeperationOfClosedByOpens-postulate :
    (X : CHaus)
    → (A B : fst X → hProp ℓ-zero)
    → ((x : fst X) → isClosedProp (A x))
    → ((x : fst X) → isClosedProp (B x))
    → areDisjoint A B
    → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
        ((x : fst X) → isOpenProp (U x)) ×
        ((x : fst X) → isOpenProp (V x)) ×
        subsetOf A U × subsetOf B V × areDisjoint U V ∥₁
  CHausSeperationOfClosedByOpens-postulate = CHausSeperationOfClosedByOpens

-- =============================================================================
-- StonePropertiesTC - Foundational Stone Space Properties
-- =============================================================================
--
-- Type-Checked Documentation Module
--
-- This module documents foundational Stone space lemmas that support the
-- main theorems of Synthetic Stone Duality.

module StonePropertiesTC where
  open import Axioms.StoneDuality using (Stone)

  -- =========================================================================
  -- TEX LEMMA 251 - ClosedPropAsSpectrum
  -- =========================================================================
  --
  -- STATEMENT: Any closed proposition P can be represented as Sp(B) for some B.
  --
  -- This is fundamental: closed propositions ARE spectra of Boolean algebras.
  -- A proposition P is closed iff P ≃ Sp(B) for some B : Booleω.
  --
  -- TYPE-CHECKED AT: ClosedPropAsSpectrumModule (line ~8251)
  --
  -- This establishes the deep connection between:
  -- - Logical closedness (under countable conjunctions)
  -- - Topological closedness (spectrum of a Boolean algebra)

  -- =========================================================================
  -- TEX LEMMA 1636 - StoneEqualityClosed
  -- =========================================================================
  --
  -- STATEMENT: Equality in Stone spaces is closed.
  -- For S : Stone and x,y : S, the proposition (x ≡ y) is closed.
  --
  -- PROOF SKETCH (from tex):
  -- 1. S = Sp(B) for some B : Booleω
  -- 2. x,y are Boolean homomorphisms B → 2
  -- 3. x ≡ y ↔ ∀b:B. x(b) = y(b)
  -- 4. Each x(b) = y(b) is decidable (equality in Bool)
  -- 5. Countable conjunction of decidable is closed
  --
  -- TYPE-CHECKED AT: StoneEqualityClosedModule.StoneEqualityClosed (line ~9153)

  -- =========================================================================
  -- TEX COROLLARY 1628 - PropositionsClosedIffStone
  -- =========================================================================
  --
  -- STATEMENT: A proposition P is closed iff P is Stone.
  --
  -- Forward: P closed → P is Stone (via ClosedPropAsSpectrum)
  -- Backward: P : Stone → P closed (Stone spaces have closed equality)
  --
  -- TYPE-CHECKED AT: PropositionsClosedIffStoneModule (line ~8354)

  -- =========================================================================
  -- TEX COROLLARY 1613 - TruncationStoneClosed
  -- =========================================================================
  --
  -- STATEMENT: For S : Stone, the truncation ||S|| is closed.
  --
  -- PROOF SKETCH:
  -- 1. By SpectrumEmptyIff01Equal: ¬S ↔ 0=1 in B where S = Sp(B)
  -- 2. 0=1 in B is open (because B is overtly discrete)
  -- 3. Therefore ¬¬S is closed
  -- 4. By LemSurjectionsFormalToCompleteness: ||S|| ↔ ¬¬S for Stone
  --
  -- TYPE-CHECKED AT: TruncationStoneClosedModule (line ~8608)
  --
  -- This is crucial for the proof of InhabitedClosedSubSpaceClosedCHaus.

  -- =========================================================================
  -- TEX LEMMA 1770/1776 - ClosedInStoneIsStone
  -- =========================================================================
  --
  -- STATEMENT: Closed subsets of Stone spaces are Stone.
  -- For S : Stone and A ⊆ S closed, the Σ-type Σ_{x:S} A(x) is Stone.
  --
  -- PROOF SKETCH (from tex):
  -- 1. A closed in S means A = ⋂_n D_n for decidable D_n
  -- 2. By StoneClosedSubsets, A ≃ Sp(B/d_n) for some d_n : B
  -- 3. B/d_n is still Booleω (quotient of Booleω is Booleω)
  -- 4. Hence A is a spectrum, therefore Stone
  --
  -- TYPE-CHECKED AT: ClosedInStoneIsStoneProof.ClosedInStoneIsStone-proved (line ~13253)
  -- POSTULATE: ClosedInStoneIsStone at line ~8974 (kept for forward reference)
  --
  -- This is a key lemma for CHaus separation properties.

  -- =========================================================================
  -- TEX LEMMA 1906 - CompactHausdorffClosed
  -- =========================================================================
  --
  -- STATEMENT: Images of closed sets under CHaus maps are closed.
  -- For f : S → X with S : Stone and X : CHaus, if A ⊆ S is closed, then f(A) is closed in X.
  --
  -- TYPE-CHECKED AT: CompactHausdorffModule.CompactHausdorffClosed (line ~11891)
  --
  -- This extends the Stone property to compact Hausdorff spaces.

  -- =========================================================================
  -- TEX COROLLARY 1930 - InhabitedClosedSubSpaceClosedCHaus
  -- =========================================================================
  --
  -- STATEMENT: For X : CHaus and A ⊆ X closed, if ¬¬(A inhabited) then A is inhabited.
  -- Equivalently: ||A|| ↔ ¬¬||A|| for A closed in CHaus.
  --
  -- This is the ¬¬-stability of inhabitedness for closed subsets.
  --
  -- TYPE-CHECKED AT: InhabitedClosedSubSpaceClosedCHausModule (line ~11930)
  --
  -- CRUCIAL FOR: IVT and BFT proofs (allows proof by contradiction)

  -- =========================================================================
  -- SUMMARY: Stone Space Property Chain
  -- =========================================================================
  --
  -- The key lemmas form a dependency chain:
  --
  -- 1. ClosedPropAsSpectrum (tex 251)
  --    "Closed props are spectra"
  --         ↓
  -- 2. PropositionsClosedIffStone (tex 1628)
  --    "Closed props are Stone"
  --         ↓
  -- 3. StoneEqualityClosed (tex 1636)
  --    "Stone equality is closed"
  --         ↓
  -- 4. ClosedInStoneIsStone (tex 1770)
  --    "Closed in Stone is Stone"
  --         ↓
  -- 5. CompactHausdorffClosed (tex 1906)
  --    "CHaus preserves closedness"
  --         ↓
  -- 6. InhabitedClosedSubSpaceClosedCHaus (tex 1930)
  --    "Closed CHaus subsets have ¬¬-stable inhabitedness"
  --         ↓
  -- 7. IVT, BFT (tex 3082, 3099)
  --    "Main topological applications"

-- =============================================================================
-- CHausStructuralTC - Compact Hausdorff Structural Properties
-- =============================================================================
--
-- Type-Checked Documentation Module
--
-- This module documents structural properties of compact Hausdorff spaces,
-- focusing on how CHaus is closed under various operations.

module CHausStructuralTC where
  open CompactHausdorffModule using (CHaus; hasCHausStr)

  -- =========================================================================
  -- TEX COROLLARY 2003 - ChausMapsPreserveIntersectionOfClosed
  -- =========================================================================
  --
  -- STATEMENT: Let X,Y:CHaus and f:X → Y.
  -- Suppose (G_n)_{n:ℕ} is a decreasing sequence of closed subsets of X.
  -- Then f(⋂_{n:ℕ} G_n) = ⋂_{n:ℕ} f(G_n).
  --
  -- STATUS: POSTULATED (ChausMapsPreserveIntersectionOfClosed at line ~12137)
  --
  -- PROOF SKETCH:
  -- 1. f(⋂_{n:ℕ} G_n) ⊆ ⋂_{n:ℕ} f(G_n) always holds
  -- 2. For converse: if y ∈ f(G_n) for all n, define F = f⁻¹(y)
  -- 3. Then F ∩ G_n is non-empty for all n
  -- 4. By CHausFiniteIntersectionProperty, ⋂_{n:ℕ} (F ∩ G_n) ≠ ∅
  -- 5. By InhabitedClosedSubSpaceClosedCHaus, this is merely inhabited
  -- 6. Thus y ∈ f(⋂_{n:ℕ} G_n)
  --
  -- MATHEMATICAL SIGNIFICANCE:
  -- This property shows that CHaus maps are "well-behaved" with respect
  -- to countable intersections. It's used in proving CompactHausdorffTopology.

  -- =========================================================================
  -- TEX COROLLARY 2019 - CompactHausdorffTopology
  -- =========================================================================
  --
  -- STATEMENT: Let A ⊆ X be a subset of a compact Hausdorff space and p:S↠X
  -- a surjection with S:Stone. Then:
  -- - A is closed iff A = ⋂_{n:ℕ} p(D_n) for decidable D_n ⊆ S
  -- - A is open iff A = ⋃_{n:ℕ} ¬p(D_n) for decidable D_n ⊆ S
  --
  -- STATUS: POSTULATED (CompactHausdorffTopology-closed/open at line ~12185)
  --
  -- This characterizes the topology of CHaus spaces in terms of:
  -- - Countable intersections of images of decidable sets (for closed)
  -- - Countable unions of complements of images of decidable sets (for open)
  --
  -- USES: StoneClosedSubsets, CompactHausdorffClosed, ChausMapsPreserveIntersectionOfClosed

  -- =========================================================================
  -- TEX LEMMA 2098 - SigmaCompactHausdorff
  -- =========================================================================
  --
  -- STATEMENT: Compact Hausdorff spaces are stable under Σ-types.
  -- If X:CHaus and Y:X→CHaus, then Σ_{x:X} Y(x) is compact Hausdorff.
  --
  -- STATUS: POSTULATED (SigmaCompactHausdorff at line ~12270)
  --
  -- PROOF SKETCH:
  -- 1. By ClosedDependentSums, identity types in Σ_{x:X}Y(x) are closed
  -- 2. By StoneAsClosedSubsetOfCantor, for any x:X there merely exists
  --    closed C⊆2^ℕ with surjection Σ_{α:2^ℕ}C(α) ↠ Y(x)
  -- 3. By local choice, we merely get S:Stone with p:S↠X such that
  --    for all s:S we have C_s⊆2^ℕ closed with surjection Σ_{2^ℕ}C_s↠Y(p(s))
  -- 4. This gives surjection Σ_{s:S,α:2^ℕ}C_s(α) ↠ Σ_{x:X}Y_x
  -- 5. The source is Stone by StoneClosedUnderPullback and ClosedInStoneIsStone
  --
  -- MATHEMATICAL SIGNIFICANCE:
  -- This is crucial for building complex CHaus spaces from simpler ones.
  -- It shows that CHaus is closed under dependent sums.

  -- =========================================================================
  -- SUMMARY: CHaus Closure Properties
  -- =========================================================================
  --
  -- The tex proves CHaus is closed under many operations:
  --
  -- 1. Finite products (trivial)
  -- 2. Σ-types (tex 2098, SigmaCompactHausdorff)
  -- 3. Closed subsets (ClosedInCHausIsCHaus)
  -- 4. Quotients by closed equivalences
  --
  -- These closures enable proving the main theorems (IVT, BFT) by:
  -- - Building the interval I as a CHaus space
  -- - Building the disk D² as a CHaus space
  -- - Using ¬¬-stability of inhabitedness (InhabitedClosedSubSpaceClosedCHaus)

-- =============================================================================
-- FoundationalAxiomsTC - Foundational Axioms of Synthetic Stone Duality
-- =============================================================================
--
-- Type-Checked Documentation Module
--
-- This module documents the 5 foundational axioms from the tex file that
-- form the axiomatic basis of Synthetic Stone Duality.

