{-# OPTIONS --cubical --guardedness #-}

module work.Part11 where

open import work.Part10a public

-- Qualified import for PT.rec etc.
import Cubical.HITs.PropositionalTruncation as PT

-- =============================================================================
-- Part 11: work.agda lines 12801-13413 (BooleEpiMono, CHaus modules)
-- =============================================================================

module BooleEpiMonoModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)

  -- Morphisms in Boole: BoolHom (fst B) (fst C)
  -- The key facts about epi-mono factorization in Boole:
  -- 1. Any g : B → C has an overtly discrete kernel
  -- 2. Ker(g) is enumerable (countable)
  -- 3. B/Ker(g) is in Boole
  -- 4. Factorization B ↠ B/Ker(g) ↪ C corresponds to
  --    Sp(C) ↠ Sp(B/Ker(g)) ↪ Sp(B)
  -- 5. Surjections in Boole ↔ closed embeddings of spectra

  -- The main result we need: surjections in Boole give closed embeddings of spectra
  -- This is stated more precisely with explicit type arguments to avoid inference issues.
  postulate
    -- For surjective g : B → C, the induced Sp(C) → Sp(B) is a closed embedding
    -- This means: the image of Sp(C) in Sp(B) is a closed subset
    SurjInBoole→ClosedImage : (B C : Booleω)
      → (g : BoolHom (fst B) (fst C))
      → ((c : ⟨ fst C ⟩) → ∥ Σ[ b ∈ ⟨ fst B ⟩ ] fst g b ≡ c ∥₁)  -- g is surjective
      → (x : Sp B) → isClosedProp (∥ Σ[ y ∈ Sp C ] y ∘cr g ≡ x ∥₁ , squash₁)

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

  -- Complement of image
  complementImage : {X : Type₀}
    → (A : X → hProp ℓ-zero) → X → hProp ℓ-zero
  complementImage A x = (fst (A x) → ⊥) , isProp→ isProp⊥

  -- Countable union
  countableUnion : {X : Type₀}
    → (A : ℕ → (X → hProp ℓ-zero)) → X → hProp ℓ-zero
  countableUnion A x = ∥ Σ[ n ∈ ℕ ] fst (A n x) ∥₁ , squash₁

  -- Main theorem (postulated)
  postulate
    CompactHausdorffTopology-closed : (X : CHaus) (S : Stone)
      → (p : fst S → fst X) → isSurjection p
      → (A : fst X → hProp ℓ-zero) → ((x : fst X) → isClosedProp (A x))
      → ∥ Σ[ D ∈ (ℕ → DecSubset S) ]
          ((x : fst X) → fst (A x) ≡ fst (countableIntersectionClosed (λ n → imageDecSubset {S} {fst X} p (D n)) x)) ∥₁

    CompactHausdorffTopology-open : (X : CHaus) (S : Stone)
      → (p : fst S → fst X) → isSurjection p
      → (U : fst X → hProp ℓ-zero) → ((x : fst X) → isOpenProp (U x))
      → ∥ Σ[ D ∈ (ℕ → DecSubset S) ]
          ((x : fst X) → fst (U x) ≡ fst (countableUnion (λ n → complementImage (imageDecSubset {S} {fst X} p (D n))) x)) ∥₁

-- =============================================================================
-- CHausSeperationOfClosedByOpens (tex Lemma 2058)
-- =============================================================================
--
-- CHaus spaces are normal: given X:CHaus and A,B ⊆ X closed with A∩B=∅,
-- there exist U,V ⊆ X open such that A ⊆ U, B ⊆ V and U∩V=∅.
--
-- Proof sketch:
-- 1. Let q:S↠X be surjective with S:Stone
-- 2. q⁻¹(A) and q⁻¹(B) are closed in S
-- 3. By StoneSeparated, ∃D:S→2 with q⁻¹(A) ⊆ D and q⁻¹(B) ⊆ ¬D
-- 4. q(D) and q(¬D) are closed by CompactHausdorffClosed
-- 5. Define U = ¬q(¬D) and V = ¬q(D)
-- 6. Then A ⊆ U, B ⊆ V, and U∩V=∅

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
  postulate
    StoneCompactHausdorffTotallyDisconnected-forward : (S : Stone)
      → isTotallyDisconnected (Stone→CHaus S)

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
  open SigmaCompactHausdorffModule
  open StoneCompactHausdorffTotallyDisconnectedModule
  open ConnectedComponentModule
  open ConnectedComponentConnectedModule

  -- Sigma type of Stone family
  SigmaStoneType : (S : Stone) → (T : fst S → Stone) → Type₀
  SigmaStoneType S T = Σ[ x ∈ fst S ] fst (T x)

  -- Main theorem
  postulate
    StoneSigmaClosed : (S : Stone) (T : fst S → Stone)
      → hasStoneStr (SigmaStoneType S T)

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

