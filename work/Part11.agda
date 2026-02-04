{-# OPTIONS --cubical --guardedness #-}

module work.Part11 where

open import work.Part10a public

-- Qualified import for PT.rec etc.
import Cubical.HITs.PropositionalTruncation as PT

-- =============================================================================
-- Part 11: work.agda lines 12801-13413 (BooleEpiMono, CHaus modules)
-- =============================================================================

-- REMOVED (CHANGES0509): BooleEpiMonoModule with SurjInBoole→ClosedImage postulate
-- =====================================================================================
-- The BooleEpiMonoModule was ORPHANED - never opened or used anywhere in the codebase.
-- The postulate SurjInBoole→ClosedImage was defined but never called.
-- Commented out to eliminate the unused postulate.
--
-- module BooleEpiMonoModule where
--   open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)
--
--   -- Morphisms in Boole: BoolHom (fst B) (fst C)
--   -- The key facts about epi-mono factorization in Boole:
--   -- 1. Any g : B → C has an overtly discrete kernel
--   -- 2. Ker(g) is enumerable (countable)
--   -- 3. B/Ker(g) is in Boole
--   -- 4. Factorization B ↠ B/Ker(g) ↪ C corresponds to
--   --    Sp(C) ↠ Sp(B/Ker(g)) ↪ Sp(B)
--   -- 5. Surjections in Boole ↔ closed embeddings of spectra
--
--   -- The main result we need: surjections in Boole give closed embeddings of spectra
--   -- This is stated more precisely with explicit type arguments to avoid inference issues.
--   postulate
--     -- For surjective g : B → C, the induced Sp(C) → Sp(B) is a closed embedding
--     -- This means: the image of Sp(C) in Sp(B) is a closed subset
--     SurjInBoole→ClosedImage : (B C : Booleω)
--       → (g : BoolHom (fst B) (fst C))
--       → ((c : ⟨ fst C ⟩) → ∥ Σ[ b ∈ ⟨ fst B ⟩ ] fst g b ≡ c ∥₁)  -- g is surjective
--       → (x : Sp B) → isClosedProp (∥ Σ[ y ∈ Sp C ] y ∘cr g ≡ x ∥₁ , squash₁)

-- =============================================================================
-- Compact Hausdorff Spaces (tex Definition at line 1898)
-- =============================================================================
--
-- A type X is called a compact Hausdorff space (CHaus) if:
-- 1. Its identity types are closed propositions
-- 2. There exists some S : Stone with a surjection S ↠ X
--
-- Equivalently: CHaus spaces are precisely quotients of Stone spaces
-- by closed equivalence relations.

module CompactHausdorffModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)

  -- Definition: A type has CHaus structure if
  -- 1. X is a set (equivalent to: equality is closed)
  -- 2. Equality is closed (x =_X y is closed for all x,y : X)
  -- 3. There exists a Stone space with a surjection onto X
  --
  -- Note: We include isSetX explicitly because isClosedProp requires isProp,
  -- and we need to construct the hProp (x ≡ y , isSetX x y) first.
  -- In the tex, being closed implies being a set, but we make this explicit.

  record hasCHausStr (X : Type₀) : Type₁ where
    field
      isSetX : isSet X
      equalityClosed : (x y : X) → isClosedProp ((x ≡ y) , isSetX x y)
      stoneCover : ∥ Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → X) ] isSurjection q ∥₁

  CHaus : Type₁
  CHaus = Σ[ X ∈ Type₀ ] hasCHausStr X

  -- Stone spaces are CHaus
  -- Proof: Stone spaces have closed equality (StoneEqualityClosed)
  -- and the identity map from themselves is a surjection.
  Stone→CHaus : Stone → CHaus
  Stone→CHaus S = fst S , record
    { isSetX = hasStoneStr→isSet S
    ; equalityClosed = StoneEqualityClosed S
    ; stoneCover = ∣ S , (λ x → x) , (λ x → ∣ x , refl ∣₁) ∣₁
    }
    where
    open StoneEqualityClosedModule

  -- A subset of a CHaus space
  ClosedSubsetOfCHaus : CHaus → Type₁
  ClosedSubsetOfCHaus X = Σ[ A ∈ (fst X → hProp ℓ-zero) ] ((x : fst X) → isClosedProp (A x))

-- =============================================================================
-- CompactHausdorffClosed (tex Lemma 1906)
-- =============================================================================
--
-- Let X : CHaus, S : Stone, and q : S ↠ X surjective.
-- Then A ⊆ X is closed iff it is the image of a closed subset of S by q.
--
-- Proof outline:
-- (→) If A is closed, then q⁻¹(A) is closed. Since q is surjective, q(q⁻¹(A)) = A.
-- (←) If B ⊆ S is closed, then x ∈ q(B) iff ∃_{s:S} (B(s) ∧ q(s) = x).
--     By InhabitedClosedSubSpaceClosed, q(B) is closed.

module CompactHausdorffClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedModule

  -- Note: preimageClosedIsClosed already defined at line ~3321

  -- The main characterization of closed subsets in CHaus
  -- Backward direction: if B is closed in S, then q(B) is closed in X
  -- Proof: For fixed x, A_x(s) = B(s) ∧ (q s ≡ x) is closed in S
  -- Then ∥ Σ s. A_x(s) ∥₁ is closed by InhabitedClosedSubSpaceClosed
  CompactHausdorffClosed-backward : (X : CHaus) (S : Stone)
    → (q : fst S → fst X) → isSurjection q
    → (B : fst S → hProp ℓ-zero) → ((s : fst S) → isClosedProp (B s))
    → (x : fst X) → isClosedProp (∥ Σ[ s ∈ fst S ] fst (B s) × (q s ≡ x) ∥₁ , squash₁)
  CompactHausdorffClosed-backward X S q q-surj B B-closed x = InhabitedClosedSubSpaceClosed S Aₓ Aₓ-closed
    where
    open hasCHausStr (snd X)
    -- For fixed x, define Aₓ(s) = B(s) ∧ (q s ≡ x)
    Aₓ : fst S → hProp ℓ-zero
    Aₓ s = (fst (B s) × (q s ≡ x)) , isProp× (snd (B s)) (isSetX (q s) x)

    -- Aₓ(s) is closed: B(s) is closed and (q s ≡ x) is closed in X
    Aₓ-closed : (s : fst S) → isClosedProp (Aₓ s)
    Aₓ-closed s = closedAnd (B s) ((q s ≡ x) , isSetX (q s) x) (B-closed s) (equalityClosed (q s) x)

-- =============================================================================
-- InhabitedClosedSubSpaceClosedCHaus (tex Corollary 1930)
-- =============================================================================
--
-- For X : CHaus with A ⊆ X closed, ∃_{x:X} A(x) is closed and equivalent to A ≠ ∅.

module InhabitedClosedSubSpaceClosedCHausModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)
  open CompactHausdorffModule
  open TruncationStoneClosedComplete
  open InhabitedClosedSubSpaceClosedModule
  open ClosedInStoneIsStoneModule
  open StoneEqualityClosedModule using (isPropIsClosedProp)

  -- The main theorem: existence of element in closed subset is closed
  -- Proof:
  -- 1. CHaus X has a Stone cover S with surjection q : S ↠ X
  -- 2. Define B(s) = A(q(s)) - closed in S by preimageClosedIsClosed
  -- 3. ∥ Σ S B ∥₁ is closed by InhabitedClosedSubSpaceClosed
  -- 4. ∥ Σ S B ∥₁ ↔ ∥ Σ X A ∥₁ by surjectivity of q
  InhabitedClosedSubSpaceClosedCHaus : (X : CHaus)
    → (A : fst X → hProp ℓ-zero) → ((x : fst X) → isClosedProp (A x))
    → isClosedProp (∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁)
  InhabitedClosedSubSpaceClosedCHaus X A A-closed =
    PT.rec (isPropIsClosedProp {∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁}) construct (hasCHausStr.stoneCover (snd X))
    where
    open hasCHausStr (snd X)

    construct : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
              → isClosedProp (∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁)
    construct (S , q , q-surj) = closedEquiv ∥ΣSB∥₁ ∥ΣXA∥₁ forward backward ∥ΣSB∥₁-closed
      where
      -- Define B(s) = A(q(s))
      B : fst S → hProp ℓ-zero
      B s = A (q s)

      -- B is closed (preimage of closed is closed)
      B-closed : (s : fst S) → isClosedProp (B s)
      B-closed s = A-closed (q s)

      -- ∥ Σ S B ∥₁ is closed
      ∥ΣSB∥₁ : hProp ℓ-zero
      ∥ΣSB∥₁ = ∥ Σ[ s ∈ fst S ] fst (B s) ∥₁ , squash₁

      ∥ΣSB∥₁-closed : isClosedProp ∥ΣSB∥₁
      ∥ΣSB∥₁-closed = InhabitedClosedSubSpaceClosed S B B-closed

      -- ∥ Σ X A ∥₁
      ∥ΣXA∥₁ : hProp ℓ-zero
      ∥ΣXA∥₁ = ∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁

      -- Forward: ∥ Σ S B ∥₁ → ∥ Σ X A ∥₁
      forward : fst ∥ΣSB∥₁ → fst ∥ΣXA∥₁
      forward = PT.map (λ { (s , Bs) → q s , Bs })

      -- Backward: ∥ Σ X A ∥₁ → ∥ Σ S B ∥₁ (using surjectivity)
      backward : fst ∥ΣXA∥₁ → fst ∥ΣSB∥₁
      backward = PT.rec squash₁ (λ { (x , Ax) →
        PT.map (λ { (s , qs≡x) → s , subst (λ y → fst (A y)) (sym qs≡x) Ax }) (q-surj x) })

-- =============================================================================
-- AllOpenSubspaceOpen (tex Corollary 1967)
-- =============================================================================
--
-- For X : CHaus with U ⊆ X open, ∀_{x:X} U(x) is open.
--
-- Proof: ¬U is closed, so ∃_{x:X} ¬U(x) is closed.
-- Therefore ¬(∃_{x:X} ¬U(x)) is open.
-- This equals ∀_{x:X} ¬¬U(x) = ∀_{x:X} U(x) (using openness of U).

module AllOpenSubspaceOpenModule where
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedCHausModule

  -- Proved using the proof from tex:
  -- 1. ¬U(x) is closed for each x (since U(x) is open)
  -- 2. ∃_{x:X} ¬U(x) is closed (by InhabitedClosedSubSpaceClosedCHaus)
  -- 3. ¬(∃_{x:X} ¬U(x)) is open (by negClosedIsOpen)
  -- 4. ¬(∃_{x:X} ¬U(x)) ↔ ∀_{x:X} ¬¬U(x) ↔ ∀_{x:X} U(x) (since open props are ¬¬-stable)
  AllOpenSubspaceOpen : (X : CHaus)
    → (U : fst X → hProp ℓ-zero) → ((x : fst X) → isOpenProp (U x))
    → isOpenProp (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x)))
  AllOpenSubspaceOpen X U Uopen = proof
    where
    -- ¬U(x) is closed for each x
    ¬U : fst X → hProp ℓ-zero
    ¬U x = ¬hProp (U x)

    ¬Uclosed : (x : fst X) → isClosedProp (¬U x)
    ¬Uclosed x = negOpenIsClosed (U x) (Uopen x)

    -- ∃_{x:X} ¬U(x) is closed
    exists-¬U : hProp ℓ-zero
    exists-¬U = ∥ Σ[ x ∈ fst X ] (¬ fst (U x)) ∥₁ , squash₁

    exists-¬U-closed : isClosedProp exists-¬U
    exists-¬U-closed = InhabitedClosedSubSpaceClosedCHaus X ¬U ¬Uclosed

    -- ¬(∃_{x:X} ¬U(x)) is open
    ¬exists-¬U : hProp ℓ-zero
    ¬exists-¬U = ¬hProp exists-¬U

    ¬exists-¬U-open : isOpenProp ¬exists-¬U
    ¬exists-¬U-open = negClosedIsOpen mp exists-¬U exists-¬U-closed

    -- Now show ∀x.U(x) ↔ ¬(∃x.¬U(x))
    -- Forward: ∀x.U(x) → ¬(∃x.¬U(x))
    forward : ((x : fst X) → fst (U x)) → fst ¬exists-¬U
    forward all-U exists-¬U' = PT.rec isProp⊥ (λ { (x , ¬Ux) → ¬Ux (all-U x) }) exists-¬U'

    -- Backward: ¬(∃x.¬U(x)) → ∀x.U(x)
    -- Need ¬(∃x.¬U(x)) → ∀x.U(x)
    -- Since U(x) is open, it is ¬¬-stable (U(x) ↔ ¬¬U(x))
    backward : fst ¬exists-¬U → (x : fst X) → fst (U x)
    backward ¬∃¬U x = openIsStable mp (U x) (Uopen x) (¬∀→¬¬ x)
      where
      -- From ¬(∃x.¬U(x)), derive ¬¬U(x)
      ¬∀→¬¬ : (x : fst X) → ¬ ¬ fst (U x)
      ¬∀→¬¬ x ¬Ux = ¬∃¬U ∣ x , ¬Ux ∣₁

    -- The proposition ∀x.U(x) is equivalent to ¬(∃x.¬U(x))
    -- Use openEquiv to transfer openness
    proof : isOpenProp (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x)))
    proof = openEquiv ¬exists-¬U (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x)))
              backward forward ¬exists-¬U-open

-- =============================================================================
-- CHausFiniteIntersectionProperty (tex Lemma 1981)
-- =============================================================================
--
-- Given X:CHaus and C_n:X→Closed closed subsets such that ⋂_{n:ℕ} C_n = ∅,
-- there is some k:ℕ with ⋂_{n≤k} C_n = ∅.
--
-- Proof sketch:
-- 1. Reduce to Stone case by CompactHausdorffClosed
-- 2. Assume X=Sp(B) and c_n:B such that C_n = {x:B→2 | x(c_n) = 0}
-- 3. Sp(B/(c_n)_{n:ℕ}) ≃ ⋂_{n:ℕ} C_n = ∅
-- 4. So 0=1 in B/(c_n)_{n:ℕ}, thus ∃k. ⋁_{n≤k} c_n = 1
-- 5. Hence ⋂_{n≤k} C_n = ∅

module CHausFiniteIntersectionPropertyModule where
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedCHausModule
  open StoneClosedSubsetsModule

  -- Finite intersection of closed subsets
  finiteIntersectionClosed : {X : Type₀}
    → (C : ℕ → (X → hProp ℓ-zero))
    → (n : ℕ)
    → X → hProp ℓ-zero
  finiteIntersectionClosed C zero x = C zero x
  finiteIntersectionClosed C (suc n) x =
    (fst (C (suc n) x) × fst (finiteIntersectionClosed C n x)) ,
    isProp× (snd (C (suc n) x)) (snd (finiteIntersectionClosed C n x))

  -- Countable intersection of closed subsets
  countableIntersectionClosed : {X : Type₀}
    → (C : ℕ → (X → hProp ℓ-zero))
    → X → hProp ℓ-zero
  countableIntersectionClosed C x =
    ((n : ℕ) → fst (C n x)) , isPropΠ (λ n → snd (C n x))

  -- Main theorem (postulated)
  postulate
    CHausFiniteIntersectionProperty : (X : CHaus)
      → (C : ℕ → (fst X → hProp ℓ-zero))
      → ((n : ℕ) → (x : fst X) → isClosedProp (C n x))
      → ((x : fst X) → ¬ fst (countableIntersectionClosed C x))
      → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁

-- =============================================================================
-- ChausMapsPreserveIntersectionOfClosed (tex Corollary 2003)
-- =============================================================================
--
-- Let X,Y:CHaus and f:X → Y.
-- Suppose (G_n)_{n:ℕ} is a decreasing sequence of closed subsets of X.
-- Then f(⋂_{n:ℕ} G_n) = ⋂_{n:ℕ} f(G_n).
--
-- Proof:
-- - f(⋂_{n:ℕ} G_n) ⊆ ⋂_{n:ℕ} f(G_n) always holds
-- - For converse: if y ∈ f(G_n) for all n, define F = f⁻¹(y)
-- - Then F ∩ G_n is non-empty for all n
-- - By CHausFiniteIntersectionProperty, ⋂_{n:ℕ} (F ∩ G_n) ≠ ∅
-- - By InhabitedClosedSubSpaceClosedCHaus, this is merely inhabited
-- - Thus y ∈ f(⋂_{n:ℕ} G_n)

module ChausMapsPreserveIntersectionOfClosedModule where
  open CompactHausdorffModule
  open CHausFiniteIntersectionPropertyModule
  open InhabitedClosedSubSpaceClosedCHausModule

  -- Image of a subset under a function
  imageSubset : {X Y : Type₀} → (f : X → Y)
    → (A : X → hProp ℓ-zero) → Y → hProp ℓ-zero
  imageSubset f A y = ∥ Σ[ x ∈ _ ] fst (A x) × (f x ≡ y) ∥₁ , squash₁

  -- Preimage of a point
  preimagePoint : {X Y : Type₀} → (f : X → Y) → (y : Y)
    → isSet Y → X → hProp ℓ-zero
  preimagePoint f y isSetY x = (f x ≡ y) , isSetY (f x) y

  -- Decreasing sequence of closed subsets
  isDecreasingSeq : {X : Type₀}
    → (G : ℕ → (X → hProp ℓ-zero)) → Type₀
  isDecreasingSeq {X} G = (n : ℕ) → (x : X) → fst (G (suc n) x) → fst (G n x)

  -- Main theorem (postulated)
  postulate
    ChausMapsPreserveIntersectionOfClosed : (X Y : CHaus)
      → (f : fst X → fst Y)
      → (G : ℕ → (fst X → hProp ℓ-zero))
      → ((n : ℕ) → (x : fst X) → isClosedProp (G n x))
      → isDecreasingSeq G
      → (y : fst Y)
      → fst (imageSubset f (countableIntersectionClosed G) y)
        ≡ fst (countableIntersectionClosed (λ n → imageSubset f (G n)) y)

-- =============================================================================
-- CompactHausdorffTopology (tex Corollary 2019)
-- =============================================================================
--
-- Let A ⊆ X be a subset of a compact Hausdorff space and p:S↠X a surjection
-- with S:Stone. Then:
-- - A is closed iff A = ⋂_{n:ℕ} p(D_n) for decidable D_n ⊆ S
-- - A is open iff A = ⋃_{n:ℕ} ¬p(D_n) for decidable D_n ⊆ S
--
-- Uses: StoneClosedSubsets, CompactHausdorffClosed, ChausMapsPreserveIntersectionOfClosed

module CompactHausdorffTopologyModule where
  open CompactHausdorffModule
  open CHausFiniteIntersectionPropertyModule
  open ChausMapsPreserveIntersectionOfClosedModule
  open StoneClosedSubsetsModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)

  -- Decidable subset of Stone space
  DecSubset : Stone → Type₀
  DecSubset S = fst S → Bool

  -- Image of decidable subset
  imageDecSubset : {S : Stone} {X : Type₀}
    → (p : fst S → X) → DecSubset S → X → hProp ℓ-zero
  imageDecSubset p D x = ∥ Σ[ s ∈ _ ] (D s ≡ true) × (p s ≡ x) ∥₁ , squash₁

  -- REMOVED (CHANGES0510): CompactHausdorffTopology-open postulate and its helpers
  -- =====================================================================================
  -- The CompactHausdorffTopology-open postulate was UNUSED - never called anywhere.
  -- Its helper definitions complementImage and countableUnion were also only used for it.
  -- Commented out to eliminate the unused postulate.
  --
  -- -- Complement of image
  -- complementImage : {X : Type₀}
  --   → (A : X → hProp ℓ-zero) → X → hProp ℓ-zero
  -- complementImage A x = (fst (A x) → ⊥) , isProp→ isProp⊥
  --
  -- -- Countable union
  -- countableUnion : {X : Type₀}
  --   → (A : ℕ → (X → hProp ℓ-zero)) → X → hProp ℓ-zero
  -- countableUnion A x = ∥ Σ[ n ∈ ℕ ] fst (A n x) ∥₁ , squash₁

  -- Main theorem for closed sets (postulated, USED via Part21)
  postulate
    CompactHausdorffTopology-closed : (X : CHaus) (S : Stone)
      → (p : fst S → fst X) → isSurjection p
      → (A : fst X → hProp ℓ-zero) → ((x : fst X) → isClosedProp (A x))
      → ∥ Σ[ D ∈ (ℕ → DecSubset S) ]
          ((x : fst X) → fst (A x) ≡ fst (countableIntersectionClosed (λ n → imageDecSubset {S} {fst X} p (D n)) x)) ∥₁

  -- REMOVED (CHANGES0510): CompactHausdorffTopology-open postulate
  -- This postulate was defined but NEVER USED anywhere in the codebase.
  -- The "open" version can be derived from the "closed" version via negation if needed.
  --
  --   CompactHausdorffTopology-open : (X : CHaus) (S : Stone)
  --     → (p : fst S → fst X) → isSurjection p
  --     → (U : fst X → hProp ℓ-zero) → ((x : fst X) → isOpenProp (U x))
  --     → ∥ Σ[ D ∈ (ℕ → DecSubset S) ]
  --         ((x : fst X) → fst (U x) ≡ fst (countableUnion (λ n → complementImage (imageDecSubset {S} {fst X} p (D n))) x)) ∥₁

-- =============================================================================
-- CHausSeperationOfClosedByOpens (tex Lemma 2058)
-- =============================================================================
--
-- CHaus spaces are normal: given X:CHaus and A,B ⊆ X closed with A∩B=∅,
-- there exist U,V ⊆ X open such that A ⊆ U, B ⊆ V and U∩V=∅.
--
-- PROOF OUTLINE (from tex lines 2058-2076):
--
-- 1. Let q : S ↠ X be the Stone cover (from CHaus structure)
--
-- 2. q⁻¹(A) and q⁻¹(B) are closed in S (preimage of closed is closed)
--    - In Stone S, closed means countable intersection of decidables
--
-- 3. q⁻¹(A) ∩ q⁻¹(B) = q⁻¹(A ∩ B) = ∅ since A ∩ B = ∅
--
-- 4. By StoneSeparated (tex Lemma 1965), for disjoint closed subsets of Stone:
--    ∃ D : S → Bool with q⁻¹(A) ⊆ D and q⁻¹(B) ⊆ ¬D
--    (i.e., D separates the two closed subsets)
--
-- 5. Define the images under q:
--    - q(D) = { x : X | ∃ s : S, D(s) = true ∧ q(s) = x }
--    - q(¬D) = { x : X | ∃ s : S, D(s) = false ∧ q(s) = x }
--
-- 6. By CompactHausdorffClosed-backward (tex Lemma 1906):
--    q(D) and q(¬D) are closed in X
--    (image of decidable subset under surjection is closed)
--
-- 7. Define the open sets:
--    - U = ¬q(¬D) = { x : X | ∀ s : S, q(s) = x → D(s) = true }
--    - V = ¬q(D) = { x : X | ∀ s : S, q(s) = x → D(s) = false }
--    These are open because negation of closed is open.
--
-- 8. Verify A ⊆ U:
--    For a ∈ A, need to show a ∉ q(¬D).
--    If a ∈ q(¬D), then ∃ s with D(s) = false and q(s) = a.
--    Since q(s) = a ∈ A, we have s ∈ q⁻¹(A) ⊆ D, so D(s) = true. Contradiction.
--
-- 9. Verify B ⊆ V: Symmetric argument using q⁻¹(B) ⊆ ¬D.
--
-- 10. Verify U ∩ V = ∅:
--     If x ∈ U ∩ V, then x ∉ q(¬D) and x ∉ q(D).
--     By q surjective, ∃ s with q(s) = x.
--     Then D(s) = true (from x ∉ q(¬D)) and D(s) = false (from x ∉ q(D)).
--     Contradiction.
--
-- DEPENDENCIES:
-- - hasCHausStr.stoneCover: gives Stone S and surjection q : S ↠ X
-- - StoneSeparated: disjoint closed subsets of Stone are separated by decidable
-- - CompactHausdorffClosed-backward: image of decidable under q is closed
-- - negClosedIsOpen: negation of closed is open

module CHausSeperationOfClosedByOpensModule where
  open CompactHausdorffModule
  open CompactHausdorffClosedModule
  open StoneSeparatedModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)

  -- Two subsets are disjoint
  areDisjoint : {X : Type₀}
    → (A B : X → hProp ℓ-zero) → Type₀
  areDisjoint {X} A B = (x : X) → ¬ (fst (A x) × fst (B x))

  -- Subset containment
  subsetOf : {X : Type₀}
    → (A B : X → hProp ℓ-zero) → Type₀
  subsetOf {X} A B = (x : X) → fst (A x) → fst (B x)

  -- Main theorem (postulated)
  postulate
    CHausSeperationOfClosedByOpens : (X : CHaus)
      → (A B : fst X → hProp ℓ-zero)
      → ((x : fst X) → isClosedProp (A x))
      → ((x : fst X) → isClosedProp (B x))
      → areDisjoint A B
      → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
          ((x : fst X) → isOpenProp (U x)) ×
          ((x : fst X) → isOpenProp (V x)) ×
          subsetOf A U × subsetOf B V × areDisjoint U V ∥₁

-- =============================================================================
-- SigmaCompactHausdorff (tex Lemma 2098)
-- =============================================================================
--
-- Compact Hausdorff spaces are stable under Σ-types.
-- If X:CHaus and Y:X→CHaus, then Σ_{x:X} Y(x) is compact Hausdorff.
--
-- Proof sketch:
-- 1. By ClosedDependentSums, identity types in Σ_{x:X}Y(x) are closed
-- 2. By StoneAsClosedSubsetOfCantor, for any x:X there merely exists
--    closed C⊆2^ℕ with surjection Σ_{α:2^ℕ}C(α) ↠ Y(x)
-- 3. By local choice, we merely get S:Stone with p:S↠X such that
--    for all s:S we have C_s⊆2^ℕ closed with surjection Σ_{2^ℕ}C_s↠Y(p(s))
-- 4. This gives surjection Σ_{s:S,α:2^ℕ}C_s(α) ↠ Σ_{x:X}Y_x
-- 5. The source is Stone by StoneClosedUnderPullback and ClosedInStoneIsStone

module SigmaCompactHausdorffModule where
  open CompactHausdorffModule
  open StoneAsClosedSubsetOfCantorModule
  -- Uses localChoice-axiom for the proof
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)

  -- Sigma type of CHaus family
  SigmaCHausType : (X : CHaus) → (Y : fst X → CHaus) → Type₀
  SigmaCHausType X Y = Σ[ x ∈ fst X ] fst (Y x)

  -- Main theorem (postulated)
  postulate
    SigmaCompactHausdorff : (X : CHaus) (Y : fst X → CHaus)
      → hasCHausStr (SigmaCHausType X Y)

  -- Derived: Sigma of CHaus is CHaus
  CHausΣ : (X : CHaus) → (Y : fst X → CHaus) → CHaus
  CHausΣ X Y = SigmaCHausType X Y , SigmaCompactHausdorff X Y

-- =============================================================================
-- AlgebraCompactHausdorffCountablyPresented (tex Lemma 2112)
-- =============================================================================
--
-- For X:CHaus, 2^X is countably presented.
--
-- Proof:
-- 1. There is surjection q:S↠X with S:Stone
-- 2. This induces injection 2^X ↪ 2^S
-- 3. a:S→2 lies in 2^X iff ∀s,t:S, q(s)=_X q(t) → a(s)=a(t)
-- 4. Since equality in X is closed and equality in 2 is decidable,
--    the implication is open for every s,t:S
-- 5. By AllOpenSubspaceOpen, 2^X is an open subalgebra of 2^S
-- 6. Therefore 2^X is in ODisc and thus countably presented

module AlgebraCompactHausdorffCountablyPresentedModule where
  open CompactHausdorffModule
  open AllOpenSubspaceOpenModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)

  -- Boolean algebra of functions X → Bool
  BoolAlgOfCHaus : CHaus → Type₀
  BoolAlgOfCHaus X = fst X → Bool

  -- Main theorem (postulated)
  postulate
    AlgebraCompactHausdorffCountablyPresented : (X : CHaus)
      → ∥ Σ[ B ∈ Booleω ] ⟨ fst B ⟩ ≡ BoolAlgOfCHaus X ∥₁

-- =============================================================================
-- ConnectedComponentModule (tex 2138-2171)
-- =============================================================================
--
-- For X:CHaus and x:X, define Q_x as the connected component of x:
-- the intersection of all decidable D ⊆ X with x ∈ D.
--
-- Lemma 2144: Q_x is a countable intersection of decidable subsets
-- Lemma 2156: If Q_x ⊆ U open, then exists decidable E with x ∈ E ⊆ U

module ConnectedComponentModule where
  open CompactHausdorffModule
  open CHausFiniteIntersectionPropertyModule
  open AlgebraCompactHausdorffCountablyPresentedModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr)

  -- Decidable subset of CHaus
  DecSubsetCHaus : CHaus → Type₀
  DecSubsetCHaus X = fst X → Bool

  -- Membership in decidable subset (parameterized by CHaus)
  inDec : (X : CHaus) → fst X → DecSubsetCHaus X → Type₀
  inDec X x D = D x ≡ true

  -- Connected component of a point
  -- Q_x = ∩ { D decidable | x ∈ D }
  ConnectedComponent : (X : CHaus) → fst X → fst X → hProp ℓ-zero
  ConnectedComponent X x y =
    ((D : DecSubsetCHaus X) → inDec X x D → inDec X y D) ,
    isPropΠ (λ D → isPropΠ (λ _ → isSetBool (D y) true))

  -- Q_x is countable intersection of decidable subsets
  -- Uses AlgebraCompactHausdorffCountablyPresented to enumerate 2^X
  postulate
    ConnectedComponentClosedInCompactHausdorff : (X : CHaus) (x : fst X)
      → ∥ Σ[ D ∈ (ℕ → DecSubsetCHaus X) ]
          ((y : fst X) → fst (ConnectedComponent X x y)
            ≡ ((n : ℕ) → inDec X y (D n))) ∥₁

  -- If Q_x ⊆ U (open), then exists decidable E with x ∈ E ⊆ U
  postulate
    ConnectedComponentSubOpenHasDecidableInbetween : (X : CHaus) (x : fst X)
      → (U : fst X → hProp ℓ-zero) → ((y : fst X) → isOpenProp (U y))
      → ((y : fst X) → fst (ConnectedComponent X x y) → fst (U y))
      → ∥ Σ[ E ∈ DecSubsetCHaus X ] inDec X x E × ((y : fst X) → inDec X y E → fst (U y)) ∥₁

-- =============================================================================
-- ConnectedComponentConnectedModule (tex Lemma 2173)
-- =============================================================================
--
-- For X:CHaus with x:X, any map Q_x → 2 is constant.
--
-- PROOF OUTLINE (from tex lines 2176-2184):
-- 1. Assume Q_x = A ∪ B with A, B decidable disjoint subsets, and x ∈ A
-- 2. Q_x ⊆ X is closed (by ConnectedComponentClosedInCompactHausdorff)
-- 3. A, B ⊆ X are closed and disjoint (using ClosedTransitive)
-- 4. By CHausSeperationOfClosedByOpens, ∃ disjoint open U, V with A ⊆ U, B ⊆ V
-- 5. By ConnectedComponentSubOpenHasDecidableInbetween, ∃ decidable D with Q_x ⊆ D ⊆ U ∪ V
-- 6. E := D ∩ U = D ∩ ¬V is clopen (hence decidable)
-- 7. x ∈ E, so Q_x ⊆ E by definition of Q_x
-- 8. But B ⊆ Q_x ⊆ E and B ∩ E = ∅, so B = ∅
--
-- DEPENDENCIES:
-- - ConnectedComponentClosedInCompactHausdorff (postulate)
-- - CHausSeperationOfClosedByOpens (postulate)
-- - ConnectedComponentSubOpenHasDecidableInbetween (postulate)
-- - ClosedTransitive (subsets of closed subsets are closed)

module ConnectedComponentConnectedModule where
  open CompactHausdorffModule
  open ConnectedComponentModule
  open CHausSeperationOfClosedByOpensModule

  postulate
    ConnectedComponentConnected : (X : CHaus) (x : fst X)
      → (f : (Σ[ y ∈ fst X ] fst (ConnectedComponent X x y)) → Bool)
      → (y z : Σ[ y ∈ fst X ] fst (ConnectedComponent X x y))
      → f y ≡ f z

-- =============================================================================
-- StoneCompactHausdorffTotallyDisconnectedModule (tex Lemma 2186)
-- =============================================================================
--
-- X:CHaus is Stone iff ∀x:X, Q_x = {x}

module StoneCompactHausdorffTotallyDisconnectedModule where
  open CompactHausdorffModule
  open ConnectedComponentModule
  open AlgebraCompactHausdorffCountablyPresentedModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr)

  -- Q_x is singleton (totally disconnected)
  isTotallyDisconnected : CHaus → Type₀
  isTotallyDisconnected X =
    (x : fst X) → (y : fst X) → fst (ConnectedComponent X x y) → x ≡ y

  -- Stone iff totally disconnected CHaus
  -- Forward direction: Stone spaces are totally disconnected
  -- Proof: For S = Sp(B), points are BoolHom B Bool.
  -- ConnectedComponent x y means: for all decidable D, x ∈ D → y ∈ D.
  -- For each b ∈ B, evaluation D_b(z) = z $cr b is decidable.
  -- So x $cr b = true → y $cr b = true for all b.
  -- Homomorphisms preserve negation: x $cr (1-b) = 1 - x $cr b.
  -- So x $cr b = false → y $cr b = false. Hence x = y.

  open import Axioms.StoneDuality using (Sp; Booleω; evaluationMap)
  open import Cubical.Algebra.CommRing using (_$cr_; CommRingStr; IsCommRingHom; CommRingHom≡)
  open import Cubical.Algebra.BooleanRing using (BooleanRingStr; BooleanRing→CommRing)
  open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
  open import Cubical.Data.Bool using (true; false; true≢false; false≢true)
  open import Cubical.Data.Empty as ⊥ using (⊥)

  StoneCompactHausdorffTotallyDisconnected-forward : (S : Stone)
    → isTotallyDisconnected (Stone→CHaus S)
  StoneCompactHausdorffTotallyDisconnected-forward S x y qxy = goal
    where
    -- Extract B from Stone structure
    B : Booleω
    B = snd S .fst

    -- Path from Sp B to fst S
    p : Sp B ≡ fst S
    p = snd S .snd

    -- Transport x, y to Sp B
    x' : Sp B
    x' = transport (sym p) x

    y' : Sp B
    y' = transport (sym p) y

    -- Helper: for b ∈ B, make the decidable subset D_b
    D_b : ⟨ fst B ⟩ → DecSubsetCHaus (Stone→CHaus S)
    D_b b z = evaluationMap B b (transport (sym p) z)

    -- Key observation: D_b b z = evaluationMap B b (transport (sym p) z)
    -- So D_b b x = x' $cr b and D_b b y = y' $cr b
    -- (because x' = transport (sym p) x and y' = transport (sym p) y)

    -- For all b, x' $cr b = true → y' $cr b = true
    agree-on-true : (b : ⟨ fst B ⟩) → x' $cr b ≡ true → y' $cr b ≡ true
    agree-on-true b x'b≡true = qxy (D_b b) x'b≡true

    -- Boolean ring structure
    open BooleanRingStr (snd (fst B)) renaming (𝟙 to 1B; _-_ to _-B_)
    open CommRingStr (snd (BooleanRing→CommRing BoolBR)) renaming (1r to 1Bool; _-_ to _-Bool_)
    open IsCommRingHom

    -- For all b, x' $cr b = y' $cr b
    -- Case on x' $cr b: true case uses agree-on-true, false case uses complement
    agree-on-all : (b : ⟨ fst B ⟩) → x' $cr b ≡ y' $cr b
    agree-on-all b with x' $cr b | inspect (x' $cr_) b
    ... | true  | [ eq ] = sym (agree-on-true b eq)
    ... | false | [ eq ] with y' $cr b | inspect (y' $cr_) b
    ...   | false | [ eq' ] = refl
    ...   | true  | [ eq' ] = ⊥.rec (false≢true contra)
      where
      -- Complement ¬b = 1 - b in B
      -- In a Boolean ring, -_ is identity and a - b = a + (-b) (XOR)
      open BooleanRingStr (snd (fst B)) using (_+_) renaming (-_ to negB)
      open CommRingStr (snd (BooleanRing→CommRing BoolBR)) using () renaming (_+_ to _+Bool_; -_ to negBool)

      ¬b : ⟨ fst B ⟩
      ¬b = 1B -B b

      -- Key facts:
      -- 1. pres+ (snd x') : x' (a + b) = x' a + x' b
      -- 2. pres- (snd x') : x' (- a) = - x' a
      -- 3. pres1 (snd x') : x' 1B = true
      -- 4. In BoolBR: a - b = a + (-b), and - is identity, so a - b = a + b

      -- x' $cr ¬b = x' $cr (1B + negB b) = x' $cr 1B + x' $cr (negB b)
      --           = true + (- x' $cr b) = true + (- false) = true + false
      -- In BoolBR, + is XOR and - is id, so true + false = true

      x'-¬b-true : x' $cr ¬b ≡ true
      x'-¬b-true =
        pres+ (snd x') 1B (negB b) ∙
        cong₂ _+Bool_ (pres1 (snd x')) (pres- (snd x') b) ∙
        cong (λ z → true +Bool (negBool z)) eq

      -- y' $cr ¬b = true (by agree-on-true)
      y'-¬b-true : y' $cr ¬b ≡ true
      y'-¬b-true = agree-on-true ¬b x'-¬b-true

      -- y' $cr ¬b = y' $cr (1B + negB b) = true + (- true) = true + true = false
      -- In BoolBR, true + true = false (XOR)
      y'-¬b-false : y' $cr ¬b ≡ false
      y'-¬b-false =
        pres+ (snd y') 1B (negB b) ∙
        cong₂ _+Bool_ (pres1 (snd y')) (pres- (snd y') b) ∙
        cong (λ z → true +Bool (negBool z)) eq'

      contra : false ≡ true
      contra = sym y'-¬b-false ∙ y'-¬b-true

    -- Now x' = y' by CommRingHom≡ since they agree on all elements
    x'≡y' : x' ≡ y'
    x'≡y' = CommRingHom≡ (funExt agree-on-all)

    -- Transport back to get x ≡ y
    goal : x ≡ y
    goal = sym (transportTransport⁻ p x) ∙ cong (transport p) x'≡y' ∙ transportTransport⁻ p y

  -- For the backward direction, we need to show that a totally disconnected
  -- CHaus space X has Stone structure, i.e., there exists B : Booleω with Sp B ≡ fst X.
  --
  -- Proof sketch (from tex Lemma 2186):
  -- 1. Take B = 2^X (with countable presentation from AlgebraCompactHausdorffCountablyPresented)
  -- 2. The evaluation map e : X → Sp(2^X) is defined by e(x)(f) = f(x)
  -- 3. Injectivity: if e(x) = e(y), then for all f : X → Bool, f(x) = f(y)
  --    This means y ∈ Q_x, and by isTotallyDisconnected, x = y
  -- 4. Surjectivity: uses surjection q : S ↠ X from Stone S,
  --    which induces injection 2^X ↪ 2^S, hence surjection Sp(2^S) ↠ Sp(2^X)
  --    By surj-formal-axiom, e ∘ q = projection, so e is surjective.

  -- Helper: evaluation map from X to Sp(2^X)
  -- For x : X, define ev_x : (X → Bool) → Bool by ev_x(f) = f(x)
  -- This is a Boolean ring homomorphism (pointwise eval preserves operations)
  open import Axioms.StoneDuality using (2^; SpGeneralBooleanRing)
  open import BooleanRing.BoolRingUnivalence using (IsBoolRingHom)
  module ICRHom = IsCommRingHom

  -- ev_x is a Boolean ring homomorphism
  evalAtPointIsHom : (X : CHaus) (x : fst X)
    → IsBoolRingHom (snd (2^ (fst X))) (λ f → f x) (snd BoolBR)
  evalAtPointIsHom X x .ICRHom.pres0 = refl
  evalAtPointIsHom X x .ICRHom.pres1 = refl
  evalAtPointIsHom X x .ICRHom.pres+ f g = refl
  evalAtPointIsHom X x .ICRHom.pres· f g = refl
  evalAtPointIsHom X x .ICRHom.pres- f = refl

  -- The evaluation map X → Sp(2^X)
  evalCHaus : (X : CHaus) → fst X → SpGeneralBooleanRing (2^ (fst X))
  evalCHaus X x = (λ f → f x) , evalAtPointIsHom X x

  -- Injectivity: evaluation is injective when X is totally disconnected
  evalCHaus-injective : (X : CHaus) → isTotallyDisconnected X
    → (x y : fst X) → evalCHaus X x ≡ evalCHaus X y → x ≡ y
  evalCHaus-injective X totDisc x y ex≡ey = totDisc x y qxy
    where
    -- From ex≡ey, for all f : X → Bool, f(x) = f(y)
    -- A decidable subset D : X → Bool gives f(x) = D(x) = true → D(y) = true
    -- fst (evalCHaus X x) D = D x, fst (evalCHaus X y) D = D y
    -- So cong (λ h → fst h D) ex≡ey : D x ≡ D y
    qxy : fst (ConnectedComponent X x y)
    qxy D xInD = sym (cong (λ h → fst h D) ex≡ey) ∙ xInD

  -- Surjectivity proof infrastructure
  -- Key: precomposition by surjection is injective
  open import Cubical.Functions.Surjection using (isSurjection)

  -- If q : S → X is surjective, then precomposition 2^X → 2^S is injective
  precomp-surj-inj : {S X : Type₀} → (q : S → X) → isSurjection q
    → (f g : X → Bool) → (λ s → f (q s)) ≡ (λ s → g (q s)) → f ≡ g
  precomp-surj-inj q q-surj f g eq = funExt λ x →
    PT.rec (isSetBool (f x) (g x)) (λ { (s , qs≡x) →
      cong f (sym qs≡x) ∙ funExt⁻ eq s ∙ cong g qs≡x
    }) (q-surj x)

  -- PROOF OUTLINE for backward direction (tex Lemma 2186, lines 2186-2212):
  --
  -- Goal: isTotallyDisconnected X → hasStoneStr X
  --       i.e., X is totally disconnected CHaus ⇒ X is Stone
  --
  -- 1. ALGEBRA CONSTRUCTION:
  --    Let B = 2^X = (X → Bool) with Boolean ring structure
  --    By AlgebraCompactHausdorffCountablyPresented (tex Lemma 2112):
  --    There exists B' : Booleω with ⟨B'⟩ ≃ 2^X
  --
  -- 2. EVALUATION MAP:
  --    Define e : X → Sp(2^X) by e(x)(f) = f(x)
  --    This is evalCHaus defined above.
  --
  -- 3. INJECTIVITY (proved as evalCHaus-injective):
  --    If e(x) = e(y), then for all f : X → Bool, f(x) = f(y)
  --    This means y ∈ Q_x (connected component of x)
  --    By isTotallyDisconnected, x = y
  --
  -- 4. SURJECTIVITY:
  --    a) Let (S, q, q-surj) be the Stone cover from CHaus structure
  --    b) Precomposition (−) ∘ q : 2^X → 2^S is injective (by precomp-surj-inj)
  --    c) By contravariant Sp, Sp(2^S) → Sp(2^X) is surjective
  --    d) evalCHaus S : S → Sp(2^S) is an iso (S is Stone ⇒ Sp(2^S) = S)
  --    e) There's a commutative square:
  --         S ----q---→ X
  --         |           |
  --    eval_S|           |eval_X
  --         ↓           ↓
  --       Sp(2^S) --→ Sp(2^X)
  --    f) Since q is surjective and top-left → bottom-right is surjective,
  --       eval_X is surjective
  --
  -- 5. CONCLUSION:
  --    eval_X : X → Sp(2^X) is a bijection
  --    Since X is a set and Sp(2^X) is a set, eval_X is an equivalence
  --    hasStoneStr X = (B', ua(eval_X-equiv))
  --
  -- DEPENDENCIES:
  -- - evalCHaus-injective: PROVED (above)
  -- - precomp-surj-inj: PROVED (above)
  -- - AlgebraCompactHausdorffCountablyPresented: POSTULATE (tex Lemma 2112)
  -- - hasCHausStr.stoneCover: gives Stone S with surjection q : S ↠ X
  --
  -- The full proof requires piecing together truncated covers with
  -- the surj-formal-axiom. We keep this as a postulate pending
  -- infrastructure for AlgebraCompactHausdorffCountablyPresented.
  postulate
    StoneCompactHausdorffTotallyDisconnected-backward : (X : CHaus)
      → isTotallyDisconnected X
      → hasStoneStr (fst X)

-- =============================================================================
-- StoneSigmaClosedModule (tex Theorem 2214)
-- =============================================================================
--
-- If S:Stone and T:S→Stone, then Σ_{x:S} T(x) is Stone.

module StoneSigmaClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open CompactHausdorffModule
  open SigmaCompactHausdorffModule
  open StoneCompactHausdorffTotallyDisconnectedModule
  open ConnectedComponentModule
  open ConnectedComponentConnectedModule

  -- Sigma type of Stone family
  SigmaStoneType : (S : Stone) → (T : fst S → Stone) → Type₀
  SigmaStoneType S T = Σ[ x ∈ fst S ] fst (T x)

  -- CHaus structure on Sigma of Stone family
  -- Using Stone→CHaus and the fact that CHaus is closed under dependent sums
  ΣStoneCHaus : (S : Stone) → (T : fst S → Stone) → CHaus
  ΣStoneCHaus S T = CHausΣ (Stone→CHaus S) (λ x → Stone→CHaus (T x))

  -- Key lemma: projection preserves connected component membership
  -- If (x',y') ∈ Q_{(x,y)} in Σ-type, then x' ∈ Q_x in S
  proj₁-preserves-CC : (S : Stone) (T : fst S → Stone)
    → (x : fst S) (y : fst (T x)) (x' : fst S) (y' : fst (T x'))
    → fst (ConnectedComponent (ΣStoneCHaus S T) (x , y) (x' , y'))
    → fst (ConnectedComponent (Stone→CHaus S) x x')
  proj₁-preserves-CC S T x y x' y' ccσ D xInD = goal
    where
    -- Lift D : S → Bool to Dσ : Σ → Bool by Dσ(a,b) = D(a)
    Dσ : DecSubsetCHaus (ΣStoneCHaus S T)
    Dσ (a , b) = D a
    -- (x,y) ∈ Dσ since x ∈ D
    xyInDσ : inDec (ΣStoneCHaus S T) (x , y) Dσ
    xyInDσ = xInD
    -- By connected component, (x',y') ∈ Dσ
    x'y'InDσ : inDec (ΣStoneCHaus S T) (x' , y') Dσ
    x'y'InDσ = ccσ Dσ xyInDσ
    -- Hence x' ∈ D
    goal : inDec (Stone→CHaus S) x' D
    goal = x'y'InDσ

  -- Prove Σ of Stone family is totally disconnected
  -- The proof structure:
  -- 1. For (x',y') ∈ Q_{(x,y)}, first show x' ∈ Q_x using proj₁-preserves-CC (proved above)
  -- 2. Since S is Stone (hence totally disconnected), x = x'
  -- 3. Now need: y and (transport y' along x=x') are equal
  -- 4. For this, reduce to the fiber case where x = x' definitionally
  -- 5. In the fiber case, show y = y' using T(x) being Stone
  --
  -- The main difficulty is in step 5: lifting a decidable D : T(x) → Bool to
  -- Dσ : Σ_{a:S} T(a) → Bool. The type of the second component depends on the first,
  -- so we can't directly apply D to an element b : T(a) when a ≠ x.
  --
  -- Two approaches from the tex:
  -- A. Use ConnectedComponentConnected: any map Q_{(x,y)} → Bool is constant.
  --    Restricting to the fiber gives a map Q_y → Bool that must be constant.
  -- B. Use the Boole structure: since S = Sp(B), we can construct a path from a to x
  --    for elements in the same connected component.
  --
  -- Key lemma proved above: proj₁-preserves-CC shows x' ∈ Q_x.

  -- Proof of ΣStone-isTotallyDisconnected following tex Theorem 2214
  ΣStone-isTotallyDisconnected : (S : Stone) (T : fst S → Stone)
    → isTotallyDisconnected (ΣStoneCHaus S T)
  ΣStone-isTotallyDisconnected S T (x , y) (x' , y') ccσ = goal
    where
    -- Step 1: x' ∈ Q_x (by proj₁-preserves-CC)
    x'InQx : fst (ConnectedComponent (Stone→CHaus S) x x')
    x'InQx = proj₁-preserves-CC S T x y x' y' ccσ

    -- Step 2: x ≡ x' (since S is Stone, hence totally disconnected)
    x≡x' : x ≡ x'
    x≡x' = StoneCompactHausdorffTotallyDisconnected-forward S x x' x'InQx

    -- Step 3: Transport y' to T(x) along x≡x'
    y'-in-Tx : fst (T x)
    y'-in-Tx = subst (λ z → fst (T z)) (sym x≡x') y'

    -- Step 4: Show y ≡ y'-in-Tx using ConnectedComponentConnected
    -- The idea: for any g : T(x) → Bool, the map (x,y) ↦ g(snd ...)
    -- restricted to Q_{(x,y)} is constant.
    -- We need to show y and y'-in-Tx are in Q_y in T(x), then use T(x) being Stone.

    -- Key observation: (x', y') transported back gives (x, y'-in-Tx)
    -- Both (x,y) and (x, y'-in-Tx) are in Q_{(x,y)} of the Σ-type.
    -- For any g : T(x) → Bool, define f : Σ → Bool by f(a,b) = g(subst ... b) if a ∈ Q_x, else ...
    -- This is tricky because the transport depends on which point a is.

    -- Simpler approach: use ConnectedComponentConnected on the Σ-type directly.
    -- For any g : T(x) → Bool, define f : Q_{(x,y)} → Bool by f(a,b) = g(subst (sym x≡a') b)
    -- where x≡a' comes from isTotallyDisconnected S applied to a ∈ Q_x.

    -- Actually, the tex proof does: for z,z' ∈ Q_{(x,y)} ⊆ {x}×T(x),
    -- any g : T(x) → Bool composed with π₂ gives constant map on Q_{(x,y)}
    -- by ConnectedComponentConnected. Since T(x) is Stone, z = z'.

    -- We construct: for g : T(x) → Bool, the map f : Q_{(x,y)} → Bool
    -- f(a, b) = g(subst (T) (sym p_a) b) where p_a : x ≡ a comes from totally disconnected
    Qσ : Type₀
    Qσ = Σ[ p ∈ SigmaStoneType S T ] fst (ConnectedComponent (ΣStoneCHaus S T) (x , y) p)

    -- (x,y) is in Qσ
    xy-in-Qσ : Qσ
    xy-in-Qσ = (x , y) , λ D xInD → xInD  -- reflexivity of connected component

    -- (x', y') is in Qσ
    x'y'-in-Qσ : Qσ
    x'y'-in-Qσ = (x' , y') , ccσ

    -- For any g : T(x) → Bool, we can build a map Qσ → Bool
    -- f(a, b, cc) = g(subst T (sym p_a) b) where p_a = isTotallyDisconnected S x a (proj₁ cc)
    make-f : (g : fst (T x) → Bool) → Qσ → Bool
    make-f g ((a , b) , cc) = g (subst (λ z → fst (T z)) (sym p_a) b)
      where
      p_a : x ≡ a
      p_a = StoneCompactHausdorffTotallyDisconnected-forward S x a
            (proj₁-preserves-CC S T x y a b cc)

    -- By ConnectedComponentConnected, make-f g is constant on Qσ
    -- So make-f g xy-in-Qσ ≡ make-f g x'y'-in-Qσ for all g
    f-constant : (g : fst (T x) → Bool) → make-f g xy-in-Qσ ≡ make-f g x'y'-in-Qσ
    f-constant g = ConnectedComponentConnected (ΣStoneCHaus S T) (x , y) (make-f g) xy-in-Qσ x'y'-in-Qσ

    -- make-f g xy-in-Qσ = g(subst ... refl) = g(y) (since subst refl = id)
    -- But we need to be careful: p_x = isTotallyDisconnected S x x (proj₁ cc_x)
    -- The path p_x might not be refl definitionally.

    -- For xy-in-Qσ: p_x : x ≡ x, and we need subst (sym p_x) y
    -- For x'y'-in-Qσ: p_x' : x ≡ x', and we need subst (sym p_x') y' = y'-in-Tx (modulo path)

    -- Since isSet holds for S (Stone spaces are sets), all paths x ≡ x are equal to refl
    isSetS : isSet (fst S)
    isSetS = StoneEqualityClosedModule.hasStoneStr→isSet S

    -- The path from isTotallyDisconnected S x x ... must equal refl
    p_x : x ≡ x
    p_x = StoneCompactHausdorffTotallyDisconnected-forward S x x
          (proj₁-preserves-CC S T x y x y (λ D xInD → xInD))

    p_x≡refl : p_x ≡ refl
    p_x≡refl = isSetS x x p_x refl

    -- Similarly, the path for x' equals x≡x'
    p_x' : x ≡ x'
    p_x' = StoneCompactHausdorffTotallyDisconnected-forward S x x'
           (proj₁-preserves-CC S T x y x' y' ccσ)

    -- make-f g xy-in-Qσ = g (subst (sym p_x) y) = g (subst refl y) = g y
    make-f-xy : (g : fst (T x) → Bool) → make-f g xy-in-Qσ ≡ g y
    make-f-xy g = cong (λ p → g (subst (λ z → fst (T z)) (sym p) y)) p_x≡refl
                ∙ cong g (transportRefl y)

    -- make-f g x'y'-in-Qσ = g (subst (sym p_x') y') = g y'-in-Tx (if p_x' = x≡x')
    -- But p_x' is computed the same way as x≡x', so p_x' = x≡x' by isSet
    p_x'≡x≡x' : p_x' ≡ x≡x'
    p_x'≡x≡x' = isSetS x x' p_x' x≡x'

    make-f-x'y' : (g : fst (T x) → Bool) → make-f g x'y'-in-Qσ ≡ g y'-in-Tx
    make-f-x'y' g = cong (λ p → g (subst (λ z → fst (T z)) (sym p) y')) p_x'≡x≡x'

    -- Combining: for all g, g y ≡ g y'-in-Tx
    g-agrees : (g : fst (T x) → Bool) → g y ≡ g y'-in-Tx
    g-agrees g = sym (make-f-xy g) ∙ f-constant g ∙ make-f-x'y' g

    -- Now use isTotallyDisconnected for T(x) to conclude y ≡ y'-in-Tx
    -- We need: y'-in-Tx ∈ Q_y in T(x)
    y'-in-Qy : fst (ConnectedComponent (Stone→CHaus (T x)) y y'-in-Tx)
    y'-in-Qy D yInD = goal'
      where
      -- D : T(x) → Bool with y ∈ D
      -- Need: y'-in-Tx ∈ D, i.e., D y'-in-Tx ≡ true
      -- We have g-agrees D : D y ≡ D y'-in-Tx
      -- And yInD : D y ≡ true
      goal' : D y'-in-Tx ≡ true
      goal' = sym (g-agrees D) ∙ yInD

    y≡y'-in-Tx : y ≡ y'-in-Tx
    y≡y'-in-Tx = StoneCompactHausdorffTotallyDisconnected-forward (T x) y y'-in-Tx y'-in-Qy

    -- Final goal: (x, y) ≡ (x', y')
    -- We have x≡x' : x ≡ x' and y≡y'-in-Tx : y ≡ subst (sym x≡x') y'
    -- So (x, y) ≡ (x', y') via ΣPathP
    goal : (x , y) ≡ (x' , y')
    goal = ΣPathP (x≡x' , toPathP y'-path)
      where
      -- Need: PathP (λ i → fst (T (x≡x' i))) y y'
      -- We have y ≡ subst (sym x≡x') y' = y'-in-Tx
      -- toPathP converts: subst (sym x≡x') y' ≡ y' × y ≡ subst ... y'
      -- Actually toPathP : transport p a ≡ b → PathP (λ i → P i) a b
      -- We need: transport (λ i → fst (T (x≡x' i))) y ≡ y'
      -- i.e., subst (x≡x') y ≡ y'
      -- But we have y ≡ subst (sym x≡x') y', so subst x≡x' y ≡ subst x≡x' (subst (sym x≡x') y') ≡ y'
      y'-path : transport (λ i → fst (T (x≡x' i))) y ≡ y'
      y'-path = cong (subst (λ z → fst (T z)) x≡x') y≡y'-in-Tx
              ∙ transportTransport⁻ (cong (λ z → fst (T z)) x≡x') y'

  -- Main theorem: uses backward direction which is postulated
  StoneSigmaClosed : (S : Stone) (T : fst S → Stone)
    → hasStoneStr (SigmaStoneType S T)
  StoneSigmaClosed S T = StoneCompactHausdorffTotallyDisconnected-backward
    (ΣStoneCHaus S T)
    (ΣStone-isTotallyDisconnected S T)

  -- Derived: Sigma of Stone is Stone
  StoneΣ : (S : Stone) → (T : fst S → Stone) → Stone
  StoneΣ S T = SigmaStoneType S T , StoneSigmaClosed S T

-- =============================================================================
-- IntervalIsCHausModule (tex Theorem 2272)
-- =============================================================================
--
-- The unit interval I = [0,1] is a compact Hausdorff space.
-- Proof: cs : 2^ℕ → I is surjective (by LLPO)
-- Equality cs(α) = cs(β) iff ∀n, |cs_n(α) - cs_n(β)| ≤ 1/2^n
-- which is a countable conjunction of decidable props, hence closed.

