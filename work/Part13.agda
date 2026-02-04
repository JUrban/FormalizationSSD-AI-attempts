{-# OPTIONS --cubical --guardedness #-}

module work.Part13 where

open import work.Part12 public

-- Qualified imports for pattern matching
import Cubical.HITs.PropositionalTruncation as PT

-- =============================================================================
-- Part 13: work.agda lines 14015-14410 (BrouwerFPT, ClosedInStoneIsStoneProof)
-- =============================================================================

module BrouwerFixedPointTheoremModule where
  open InhabitedClosedSubSpaceClosedCHausModule
  open IntervalIsCHausModule
  open CompactHausdorffModule

  -- The 2-disk D² (abstract)
  postulate
    Disk2 : Type₀
    isSetDisk2 : isSet Disk2

  -- The 1-sphere S¹ (boundary of D²)
  postulate
    Circle : Type₀
    isSetCircle : isSet Circle

  -- Inclusion of boundary
  postulate
    boundary-inclusion : Circle → Disk2

  -- D² is compact Hausdorff (tex: follows from being homeomorphic to I²)
  postulate
    Disk2IsCHaus : hasCHausStr Disk2

  -- D² is contractible (tex Corollary 3047 R-I-contractible)
  -- The disk contracts to its center via radial contraction: H(x,t) = (1-t)·x
  -- This is a more primitive geometric postulate than disk-cohomology-vanishes,
  -- and implies H¹(D²) = 0 via Hⁿ-contrType≅0 from the Cubical library.
  postulate
    isContrDisk2 : isContr Disk2

  -- The CHaus structure on D²
  Disk2CHaus : CHaus
  Disk2CHaus = Disk2 , Disk2IsCHaus

  -- No retraction from D² to S¹ (tex Proposition 3074)
  --
  -- =================================================================
  -- PROOF STRUCTURE 1: Cohomology approach
  -- =================================================================
  --
  -- Suppose r : D² → S¹ is a retraction with r ∘ boundary-inclusion = id.
  -- This induces a sequence of group homomorphisms on cohomology:
  --
  --   H¹(S¹,ℤ) → H¹(D²,ℤ) → H¹(S¹,ℤ)
  --       ↓        ↓          ↓
  --       ℤ   →    0    →     ℤ
  --
  -- where:
  -- - r* : H¹(S¹) → H¹(D²) is induced by r
  -- - boundary-inclusion* : H¹(D²) → H¹(S¹) is induced by boundary-inclusion
  -- - The composition is id (since r ∘ boundary-inclusion = id)
  --
  -- But H¹(D²,ℤ) = 0 (from disk-cohomology-vanishes), so the composition
  -- ℤ → 0 → ℤ cannot be id. This is a contradiction.
  --
  -- Dependencies:
  -- - circle-cohomology : H¹(S¹) ≃ ℤ (in CohomologyModule)
  -- - disk-cohomology-vanishes : H¹(D²) = 0 (in CohomologyModule)
  -- - Functoriality of H¹ (not yet formalized)
  --
  -- =================================================================
  -- PROOF STRUCTURE 2: Shape-theoretic approach (tex Proposition 3074)
  -- =================================================================
  --
  -- The tex file gives a more direct proof using shapes/localization:
  --
  -- 1. D² is I-contractible (tex Corollary 3047 R-I-contractible)
  --    - Since D² is a closed, bounded, convex subset of ℝ², it is contractible
  --    - The shape L_I(D²) = 1 (trivial)
  --
  -- 2. S¹ ≃ ℝ/ℤ has shape BZ (tex Proposition 3051 shape-S1-is-BZ)
  --    - The shape L_I(S¹) = BZ = K(ℤ,1) (Eilenberg-MacLane space)
  --
  -- 3. If r : D² → S¹ is a retraction, it induces a map on shapes:
  --    L_I(r) : L_I(D²) → L_I(S¹)
  --           : 1 → BZ
  --    with L_I(r) ∘ L_I(i) = id where i : S¹ → D² is the inclusion.
  --
  -- 4. But then BZ → 1 → BZ would be id, which is impossible since
  --    BZ is not contractible (it has π₁(BZ) = ℤ ≠ 0).
  --
  -- This approach requires:
  -- - I-localization (shape) theory for compact Hausdorff spaces
  -- - Shape of D² is 1 (contractible shape)
  -- - Shape of S¹ is BZ (Eilenberg-MacLane K(ℤ,1))
  --
  postulate
    no-retraction : (r : Disk2 → Circle)
      → ((x : Circle) → r (boundary-inclusion x) ≡ x)
      → ⊥

  -- If ∀x. f(x) ≠ x, then there is a retraction D² → S¹
  --
  -- PROOF STRUCTURE (geometric construction):
  --
  -- Given f : D² → D² with ∀x. f(x) ≠ x, we construct r : D² → S¹ by:
  --
  -- For each x ∈ D²:
  --   1. Consider the line L from f(x) through x
  --   2. Since f(x) ≠ x, this line is well-defined
  --   3. L intersects S¹ = ∂D² at exactly one point "beyond" x (away from f(x))
  --   4. Define r(x) to be this intersection point
  --
  -- r is a retraction because:
  --   - For x ∈ S¹: the line from f(x) through x meets S¹ again at x
  --     (since x is already on the boundary)
  --   - So r(boundary-inclusion(x)) = x
  --
  -- Formalizing this requires:
  --   - Vector space structure on D² (or embedding in ℝ²)
  --   - Line intersection calculations
  --   - Continuity of the construction
  --
  -- This is fundamentally a GEOMETRIC postulate about the disk.
  --
  postulate
    retraction-from-no-fixpoint : (f : Disk2 → Disk2)
      → ((x : Disk2) → (f x ≡ x → ⊥))
      → Σ[ r ∈ (Disk2 → Circle) ] ((x : Circle) → r (boundary-inclusion x) ≡ x)

  -- The contradiction: if ∀x. f(x) ≠ x, then we get a retraction, contradicting no-retraction
  BFP-contradiction : (f : Disk2 → Disk2)
    → ((x : Disk2) → (f x ≡ x → ⊥))
    → ⊥
  BFP-contradiction f no-fix =
    let (r , r-is-retract) = retraction-from-no-fixpoint f no-fix
    in no-retraction r r-is-retract

  -- Main theorem (tex Theorem 3099) - PROVED (modulo the geometric postulates)
  BrouwerFixedPointTheorem : (f : Disk2 → Disk2)
    → ∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁
  BrouwerFixedPointTheorem f =
    let -- The proposition "∃x. f(x) = x"
        existence-prop : hProp ℓ-zero
        existence-prop = (∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁) , squash₁

        -- For each x, the equation f(x) = x defines a closed proposition
        A : Disk2 → hProp ℓ-zero
        A x = (f x ≡ x) , isSetDisk2 (f x) x

        -- A(x) is closed because equality in CHaus is closed
        A-closed : (x : Disk2) → isClosedProp (A x)
        A-closed x = hasCHausStr.equalityClosed Disk2IsCHaus (f x) x

        -- By InhabitedClosedSubSpaceClosedCHaus, ∃x.A(x) is closed
        existence-closed : isClosedProp existence-prop
        existence-closed = InhabitedClosedSubSpaceClosedCHaus Disk2CHaus A A-closed

        -- Prove ¬¬(∃x. f(x) = x) by showing ¬(∀x. f(x) ≠ x)
        ¬¬existence : ¬ ¬ ∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁
        ¬¬existence ¬∃ =
          let no-fix : (x : Disk2) → (f x ≡ x → ⊥)
              no-fix x fx=x = ¬∃ ∣ x , fx=x ∣₁
          in BFP-contradiction f no-fix

    in closedIsStable existence-prop existence-closed ¬¬existence

-- =============================================================================
-- Summary of Main Theorems
-- =============================================================================
--
-- This formalization covers the main results from the tex file on
-- Synthetic Stone Duality:
--
-- FUNDAMENTAL AXIOMS:
-- 1. Stone Duality (sd-axiom)
-- 2. Surjections are formal (surj-formal-axiom)
-- 3. Local Choice (localChoice-axiom)
--
-- MAIN STRUCTURAL RESULTS:
-- - Stone spaces are profinite
-- - Closed subsets of Stone are Stone (ClosedInStoneIsStone)
-- - Stone spaces are closed under Sigma types (StoneSigmaClosed)
-- - Compact Hausdorff spaces are closed under Sigma types (SigmaCompactHausdorff)
-- - Stone iff totally disconnected CHaus (StoneCompactHausdorffTotallyDisconnected)
-- - Cantor space is Stone (CantorIsStone)
-- - Stone spaces embed as closed subsets of Cantor (StoneAsClosedSubsetOfCantor)
--
-- CLOSED SUBSETS OF CANTOR (StoneAsClosedSubsetOfCantorModule):
-- - ClosedSubsetOfCantor→Stone, Stone→ClosedWithEquiv: bidirectional correspondence
-- - ClosedSubsetIntersection, ClosedSubsetUnion: Boolean algebra operations
-- - ClosedSubsetCountableIntersection: countable meet operation
-- - EmptyClosedSubset, FullClosedSubset: boundary elements
-- - CantorFullCorrespondence, EmptyCorrespondence: type correspondences
-- - ClosedSubsetPreimageCantor: functorial preimage operation
-- - preimageIntersection, preimageUnion: preimage preserves Boolean ops
-- - OpenSubsetOfCantor: dual type for open subsets
-- - ClosedSubsetComplement, OpenSubsetComplement: complementation operations
-- - doubleComplementClosed: ¬¬A = A for closed subsets (pointwise)
-- - OpenSubsetIntersection, OpenSubsetUnion: open subset operations
-- - EmptyOpenSubset, FullOpenSubset: boundary elements for open subsets
-- - OpenSubsetCountableUnion: countable join for open subsets
-- - deMorganClosedUnion: ¬(A ∪ B) ≡ ¬A ∩ ¬B (closed → open, full path equivalence)
-- - deMorganClosedIntersection-backward: ¬A ∨ ¬B → ¬(A ∧ B) (constructive direction)
-- - deMorganOpenUnion: ¬(A ∪ B) ≡ ¬A ∧ ¬B (open → closed, full path equivalence)
-- - deMorganOpenIntersection-backward: ¬A ∨ ¬B → ¬(A ∧ B) (constructive direction, for open)
-- - complementInvolution: OpenSubsetComplement ∘ ClosedSubsetComplement ≡ id (on closed)
-- - doubleComplementOpen: ¬¬A = A for open subsets (pointwise, using MP)
-- - isPropIsOpenProp: openness witnesses are propositional
-- - complementInvolutionOpen: ClosedSubsetComplement ∘ OpenSubsetComplement ≡ id (on open)
-- - OpenSubsetPreimageCantor: functorial preimage for open subsets
-- - preimageOpenIntersection, preimageOpenUnion: preimage preserves open ops
-- - preimageComplementClosed, preimageComplementOpen: preimage commutes with complement
-- - preimageEmpty, preimageFull, preimageOpenEmpty, preimageOpenFull: boundary preservation
-- - preimageCountableIntersection: preimage preserves countable ∩ (closed)
-- - preimageCountableUnion: preimage preserves countable ∪ (open)
-- - preimageClosedComposition, preimageOpenComposition: preimage respects ∘
-- - preimageClosedId, preimageOpenId: preimage preserves identity
--
-- INTERVAL TOPOLOGY (tex 2605-2762):
-- - Unit interval I is CHaus (IntervalIsCHaus)
-- - Linear order on I (≤I-linear, ≤I-antisym, ≤I-trans, ≤I-refl)
-- - Strict order is open (<I-isOpen), weak order is closed (≤I-isClosed)
-- - Apartness characterization (≠I-apartness)
-- - Interval topology is standard (IntervalTopologyStandard)
-- - Image of decidable sets are closed intervals (ImageDecidableClosedInterval)
--
-- MAIN THEOREMS:
-- - Intermediate Value Theorem (IntermediateValueTheorem) - PROVED (tex 3082)
--   Proof structure: ∃x.f(x)=y is closed → ¬¬-stable → contradict with Bool-I-local
-- - Brouwer's Fixed Point Theorem (BrouwerFixedPointTheorem) - PROVED (tex 3099)
--   Proof structure: ∃x.f(x)=x is closed → ¬¬-stable → contradict with no-retraction
--   Remaining postulates: Disk2, Circle, boundary-inclusion, Disk2IsCHaus,
--   no-retraction (cohomology), retraction-from-no-fixpoint (geometry)
--
-- DERIVED PRINCIPLES:
-- - ¬WLPO, MP, LLPO follow from Stone Duality
-- - Markov's principle for closed propositions (ClosedMarkov)
--
-- COMPACT HAUSDORFF TOPOLOGY:
-- - AllOpenSubspaceOpen (tex 1967): PROVED - ∀x.U(x) is open for open U ⊆ CHaus
--   Proof: ¬(∃x.¬U(x)) is open by negClosedIsOpen + InhabitedClosedSubSpaceClosedCHaus
--
-- INTERVAL ORDER THEORY:
-- - <I-trans, <I-≤I-trans, ≤I-<I-trans: PROVED transitivity of strict/mixed orders
-- - <I-irrefl, <I-implies-≢: PROVED irreflexivity and non-equality
-- - ≤I-from-≡, <I-implies-¬≤I: PROVED derived order properties
-- - <I-trichotomy: postulated (requires decidable equality on I)
--
-- =============================================================================
-- ClosedInStoneIsStone PROOF (validation of postulate at line ~8916)
-- =============================================================================
--
-- This module provides the full proof of ClosedInStoneIsStone, which was
-- postulated earlier in the file due to forward reference issues.
-- The postulate at line ~8916 IS NOW PROVABLE with this code.

module ClosedInStoneIsStoneProof where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr; isSetBoolHom)
  open SDDecToElemModule
  open StoneClosedSubsetsModule

  -- The full proof of ClosedInStoneIsStone
  ClosedInStoneIsStone-proved : (S : Stone) → (A : fst S → hProp ℓ-zero)
                              → ((x : fst S) → isClosedProp (A x))
                              → hasStoneStr (Σ (fst S) (λ x → fst (A x)))
  ClosedInStoneIsStone-proved S A A-closed =
    PT.rec (isPropHasStoneStr sd-axiom _) construct (snd (fst (snd S)))
    where
    -- The underlying type of S
    |S| : Type ℓ-zero
    |S| = fst S

    -- Σ A is a set (follows from A being hProp-valued over a set)
    S-isSet : isSet |S|
    S-isSet = subst isSet (snd (snd S)) (isSetBoolHom (fst (fst (snd S))) BoolBR)

    ΣA-isSet : isSet (Σ |S| (λ x → fst (A x)))
    ΣA-isSet = isSetΣ S-isSet (λ x → isProp→isSet (snd (A x)))

    -- The closedness witness gives us α : |S| → ℕ → Bool for each x
    α : |S| → ℕ → Bool
    α x = fst (A-closed x)

    -- A(x) ↔ ∀n. α(x)(n) = false
    A→allFalse : (x : |S|) → fst (A x) → (n : ℕ) → α x n ≡ false
    A→allFalse x = fst (snd (A-closed x))

    allFalse→A : (x : |S|) → ((n : ℕ) → α x n ≡ false) → fst (A x)
    allFalse→A x = snd (snd (A-closed x))

    -- Given the untruncated presentation, construct the Stone structure
    -- isPropHasStoneStr expects a Set (= Type in cubical Agda)
    construct : has-Boole-ω' (fst (fst (snd S))) → hasStoneStr (Σ |S| (λ x → fst (A x)))
    construct (f₀ , equiv₀) = PT.rec propHasStoneStrΣA extractC (quotientBySeqPreservesBooleω B d)
      where
      propHasStoneStrΣA : isProp (hasStoneStr (Σ |S| (λ x → fst (A x))))
      propHasStoneStrΣA = isPropHasStoneStr sd-axiom (Σ |S| (λ x → fst (A x)))

      -- B : Booleω from the Stone structure
      B : Booleω
      B = fst (snd S)

      -- The path Sp B ≡ |S|
      SpB≡S : Sp B ≡ |S|
      SpB≡S = snd (snd S)

      -- Transport α along the path to get α' on Sp B
      α' : Sp B → ℕ → Bool
      α' x n = α (transport SpB≡S x) n

      -- Define decidable predicates on Sp B
      -- Dₙ(x) = α'(x)(n), so x ∈ A ↔ ∀n. Dₙ(x) = false
      D : ℕ → Sp B → Bool
      D n x = α' x n

      -- By SD, for each n, get dₙ ∈ B with x(dₙ) = D(n)(x) = α'(x)(n)
      d : ℕ → ⟨ fst B ⟩
      d n = elemFromDecPred sd-axiom B (D n)

      -- Key property: x(d n) = α'(x)(n)
      d-property : (n : ℕ) (x : Sp B) → fst x (d n) ≡ α' x n
      d-property n x = decPred-elem-correspondence sd-axiom B (D n) x

      -- Extract C from the truncated result
      extractC : Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
               → hasStoneStr (Σ |S| (λ x → fst (A x)))
      extractC (C , SpC≃ClosedSubset) = C , SpC≡ΣA
        where
        -- The closed subset from quotientBySeqPreservesBooleω
        ClosedSubsetB : Type ℓ-zero
        ClosedSubsetB = Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)

        -- ClosedSubsetB ≃ Σ |S| A via the transport
        -- Key insight: x(d n) = false ↔ α'(x)(n) = false (by d-property)
        -- And α'(x)(n) = α(transport SpB≡S x)(n), so this is A(transport SpB≡S x)

        ClosedSubsetB→ΣA : ClosedSubsetB → Σ |S| (λ y → fst (A y))
        ClosedSubsetB→ΣA (x , all-zero) = transport SpB≡S x , allFalse→A (transport SpB≡S x) allFalse'
          where
          allFalse' : (n : ℕ) → α (transport SpB≡S x) n ≡ false
          allFalse' n =
            α (transport SpB≡S x) n   ≡⟨ sym (d-property n x) ⟩
            fst x (d n)               ≡⟨ all-zero n ⟩
            false ∎

        ΣA→ClosedSubsetB : Σ |S| (λ y → fst (A y)) → ClosedSubsetB
        ΣA→ClosedSubsetB (y , Ay) = x , all-zero
          where
          x : Sp B
          x = transport (sym SpB≡S) y

          all-zero : (n : ℕ) → fst x (d n) ≡ false
          all-zero n =
            fst x (d n)             ≡⟨ d-property n x ⟩
            α' x n                  ≡⟨ refl ⟩
            α (transport SpB≡S x) n ≡⟨ cong (λ z → α z n) (transportTransport⁻ SpB≡S y) ⟩
            α y n                   ≡⟨ A→allFalse y Ay n ⟩
            false ∎

        -- The round-trips
        -- Note: transport⁻Transport p x : transport⁻ p (transport p x) ≡ x
        --       transportTransport⁻ p y : transport p (transport⁻ p y) ≡ y
        open import Cubical.Foundations.Transport using (transport⁻Transport)
        ClosedSubsetB→ΣA→ClosedSubsetB : (xa : ClosedSubsetB) → ΣA→ClosedSubsetB (ClosedSubsetB→ΣA xa) ≡ xa
        ClosedSubsetB→ΣA→ClosedSubsetB (x , all-zero) =
          Σ≡Prop (λ _ → isPropΠ (λ _ → isSetBool _ _))
                 (transport⁻Transport SpB≡S x)

        ΣA→ClosedSubsetB→ΣA : (yAy : Σ |S| (λ y → fst (A y))) → ClosedSubsetB→ΣA (ΣA→ClosedSubsetB yAy) ≡ yAy
        ΣA→ClosedSubsetB→ΣA (y , Ay) =
          Σ≡Prop (λ z → snd (A z))
                 (transportTransport⁻ SpB≡S y)

        -- The equivalence ClosedSubsetB ≃ Σ A
        ClosedSubsetB≃ΣA : ClosedSubsetB ≃ Σ |S| (λ y → fst (A y))
        ClosedSubsetB≃ΣA = isoToEquiv (iso ClosedSubsetB→ΣA ΣA→ClosedSubsetB ΣA→ClosedSubsetB→ΣA ClosedSubsetB→ΣA→ClosedSubsetB)

        -- Compose: Sp C ≃ ClosedSubsetB ≃ Σ A
        SpC≃ΣA : Sp C ≃ Σ |S| (λ y → fst (A y))
        SpC≃ΣA = compEquiv SpC≃ClosedSubset ClosedSubsetB≃ΣA

        -- Convert to path
        SpC≡ΣA : Sp C ≡ Σ |S| (λ y → fst (A y))
        SpC≡ΣA = ua SpC≃ΣA

-- =============================================================================
-- ClosedInStoneIsStone Equality Verification (CHANGES0415)
-- =============================================================================
--
-- This module proves that the postulate ClosedInStoneIsStone (Part07.agda:793)
-- equals the proved version ClosedInStoneIsStone-proved (above).
--
-- This verification follows the same pattern as:
-- - f-injective-equality (Part14.agda:957): f-injective ≡ f-injective-from-trunc

module ClosedInStoneIsStoneEqualityModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr)
  open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isPropΠ3)
  open ClosedInStoneIsStoneModule
  open ClosedInStoneIsStoneProof

  -- The type of ClosedInStoneIsStone is a proposition
  -- because hasStoneStr is a proposition (isPropHasStoneStr sd-axiom)
  isProp-ClosedInStoneIsStone-type : isProp ((S : Stone) → (A : fst S → hProp ℓ-zero)
                                            → ((x : fst S) → isClosedProp (A x))
                                            → hasStoneStr (Σ (fst S) (λ x → fst (A x))))
  isProp-ClosedInStoneIsStone-type =
    isPropΠ3 (λ S A _ → isPropHasStoneStr sd-axiom (Σ (fst S) (λ x → fst (A x))))

  -- THE KEY THEOREM: ClosedInStoneIsStone equals ClosedInStoneIsStone-proved
  -- This shows the postulate is consistent with its proof.
  ClosedInStoneIsStone-equality : ClosedInStoneIsStone ≡ ClosedInStoneIsStone-proved
  ClosedInStoneIsStone-equality = isProp-ClosedInStoneIsStone-type ClosedInStoneIsStone ClosedInStoneIsStone-proved

-- =============================================================================
-- Section 6: Cohomology (tex 2769-2968)
-- =============================================================================
--
-- This section formalizes the cohomology results needed for Brouwer's theorem.
-- We use the Cubical library's existing Eilenberg-MacLane space infrastructure
-- and add the Čech cohomology constructions from the paper.
--
-- Key results from the tex file:
-- - Čech complex C(S,T,A) (tex 2784-2795) - DEFINED
-- - section-exact-cech-complex (tex Lemma 2807) - PROVED!
-- - canonical-exact-cech-complex (tex Lemma 2815) - PROVED!
-- - exact-cech-complex-vanishing-cohomology (tex Lemma 2823) - PROVED!
-- - cech-complex-vanishing-stone (tex Lemma 2878) - postulate with proof sketch
-- - eilenberg-stone-vanish: H^1(S,Z) = 0 for Stone S (tex 2887) - postulate with proof deps
-- - stone-commute-delooping: B(Z^S) ≃ (BZ)^S (tex 2895) - postulate
-- - cech-eilenberg-1-agree: H^1(X,Z) = Ȟ^1(X,S,Z) (tex 2945) - postulate
-- - interval-cohomology-vanishes (tex Prop 2991) - DERIVED from isContrUnitInterval (CHANGES0323)
-- - Cn-exact-sequence (tex Lemma 2973) - finite approx module added

