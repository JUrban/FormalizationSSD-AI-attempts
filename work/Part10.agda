{-# OPTIONS --cubical --guardedness #-}

module work.Part10 where

open import work.Part09 public

-- Additional imports for Part10
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×; isSetΣ)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq; secEq; retEq)
open import Cubical.Foundations.Univalence using (pathToEquiv; hPropExt)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; isoToPath; iso)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥) renaming (rec to ex-falso)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing using (CommRing; CommRingHom; _∘cr_; CommRingHom≡)
open import Axioms.StoneDuality using (Booleω; Sp)

-- Top-level helper for use in where blocks of nested modules
pathToEquiv' : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv' = pathToEquiv

-- =============================================================================
-- Part 10: work.agda lines 11506-12800 (StoneAsClosedSubsetOfCantor)
-- =============================================================================

module StoneAsClosedSubsetOfCantorModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Foundations.Equiv using (compEquiv)
  open ClosedInStoneIsStoneModule
  open StoneClosedSubsetsModule
  open CantorIsStoneModule

  -- Note: CantorSpace = ℕ → Bool is already defined at the top level (line 74)
  -- We use the global definition here.

  -- 2^ℕ is a Stone space: it's the spectrum of the free BA on ℕ
  -- This is now PROVED in CantorIsStoneModule above!

  CantorStone : Stone
  CantorStone = CantorSpace , CantorIsStone

  -- A closed subset of Cantor space
  ClosedSubsetOfCantor : Type₁
  ClosedSubsetOfCantor = Σ[ A ∈ (CantorSpace → hProp ℓ-zero) ] ((x : CantorSpace) → isClosedProp (A x))

  -- Main theorem: Stone spaces are precisely closed subsets of 2^ℕ
  --
  -- Forward: Stone → closed subset of 2^ℕ
  -- For S = Sp(B) where B : Booleω, by BooleAsCQuotient we have B ≅ 2[ℕ]/I
  -- for some ideal I. The quotient map 2[ℕ] → B induces
  -- Sp(B) ↪ Sp(2[ℕ]) = 2^ℕ as a closed embedding.
  --
  -- Backward: closed subset of 2^ℕ → Stone
  -- By ClosedInStoneIsStone, closed subsets of CantorStone are Stone.

  -- Any Stone space is (merely) a closed subset of 2^ℕ - PROOF
  --
  -- Proof structure:
  -- 1. S : Stone gives (B, path) : Σ[ B ∈ Booleω ] Sp B ≡ |S|
  -- 2. B : Booleω means ∥ has-Boole-ω' B ∥₁
  --    where has-Boole-ω' B = Σ[ f ∈ (ℕ → ⟨freeBA ℕ⟩) ] BooleanRingEquiv B (freeBA ℕ /Im f)
  -- 3. Using SpOfQuotientBySeq, Sp(freeBA ℕ /Im f) ≃ {x : Sp(freeBA ℕ) | ∀n. x(f n) = false}
  -- 4. Sp(freeBA ℕ) ≃ CantorSpace by freeBA-universal-property
  -- 5. So S ≃ Sp B ≃ Sp(freeBA ℕ /Im f) ≃ closed subset of CantorSpace

  module Stone→ClosedInCantorProof where
    open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv)
    open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
    open import Axioms.StoneDuality using (SpGeneralBooleanRing)
    import QuotientBool as QB
    open StoneClosedSubsetsModule.SpOfQuotientBySeq
    import Cubical.Foundations.Equiv as Eq
    open Eq using (compEquiv)

    -- Given an untruncated presentation, construct the closed subset
    Stone→Closed-from-pres : (B : BooleanRing ℓ-zero)
      → (pres : has-Boole-ω' B)
      → Σ[ A ∈ ClosedSubsetOfCantor ] (Sp (B , ∣ pres ∣₁) ≃ (Σ[ x ∈ CantorSpace ] fst (fst A x)))

    Stone→Closed-from-pres B (f , equiv) = (A , A-closed) , SpB≃ΣA
      where
      -- The quotient
      Q : BooleanRing ℓ-zero
      Q = freeBA ℕ QB./Im f

      -- The BooleanRing equivalence B ≃ Q
      B≃Q : ⟨ B ⟩ ≃ ⟨ Q ⟩
      B≃Q = fst equiv

      -- The closed subset predicate: x(f n) = false for all n
      -- First we transport via the isomorphism Sp(freeBA ℕ) ≃ CantorSpace
      -- A CantorSpace element α : ℕ → Bool corresponds to a BoolHom h where h(gen n) = α n
      -- The condition h(f n) = false becomes a condition on α
      --
      -- For α : CantorSpace, the corresponding h : Sp(freeBA ℕ) satisfies h(gen n) = α n
      -- The condition is: for all n, h(f n) = false
      -- Since f n is some expression in generators, this becomes a condition on α
      --
      -- Actually, simpler approach: define A directly using the character value
      -- For h : Sp(freeBA ℕ), define A(α) iff the hom corresponding to α maps all f n to 0

      -- The isomorphism between Sp(freeBA ℕ) and CantorSpace
      Sp-to-Cantor : SpGeneralBooleanRing (freeBA ℕ) → CantorSpace
      Sp-to-Cantor = Iso.fun Sp-freeBA-ℕ-Iso

      Cantor-to-Sp : CantorSpace → SpGeneralBooleanRing (freeBA ℕ)
      Cantor-to-Sp = Iso.inv Sp-freeBA-ℕ-Iso

      -- The predicate A on CantorSpace: α satisfies A iff the corresponding
      -- Sp(freeBA ℕ) element maps all f n to false
      A-pred : CantorSpace → Type ℓ-zero
      A-pred α = (n : ℕ) → fst (Cantor-to-Sp α) (f n) ≡ false

      A-isProp : (α : CantorSpace) → isProp (A-pred α)
      A-isProp α = isPropΠ (λ n → isSetBool _ _)

      A : CantorSpace → hProp ℓ-zero
      A α = A-pred α , A-isProp α

      -- A is closed: it's a countable intersection of decidable predicates
      -- Each condition "h(f n) = false" is decidable (closed)
      A-closed : (α : CantorSpace) → isClosedProp (A α)
      A-closed α = closedCountableIntersection P P-closed
        where
        h : SpGeneralBooleanRing (freeBA ℕ)
        h = Cantor-to-Sp α

        P : ℕ → hProp ℓ-zero
        P n = (fst h (f n) ≡ false) , isSetBool _ _

        P-closed : (n : ℕ) → isClosedProp (P n)
        P-closed n = StoneEqualityClosedModule.Bool-eq-closed (fst h (f n)) false

      -- Now we need SpB ≃ ΣA
      -- Sp B ≃ Sp Q (via equiv)
      -- Sp Q = {h : Sp(freeBA ℕ) | ∀n. h(f n) = false} (by SpOfQuotientBySeq)
      -- This corresponds to {α : CantorSpace | A α}

      -- The Sp-quotient-≃ gives us: Sp Q ≃ ClosedSubset
      -- where ClosedSubset = Σ[ h ∈ Sp(freeBA ℕ) ] ((n : ℕ) → fst h (f n) ≡ false)
      module SQS = SpOfQuotientBySeq (freeBA ℕ) f

      SpQ≃ClosedSubsetSp : BoolHom Q BoolBR ≃ SQS.ClosedSubset
      SpQ≃ClosedSubsetSp = SQS.Sp-quotient-≃

      -- Now transport the closed subset via Cantor iso
      -- The key insight: we need to transport the dependent type along the iso
      -- SQS.ClosedSubset = Σ[ h : Sp(freeBA ℕ) ] ((n : ℕ) → fst h (f n) ≡ false)
      -- We want: Σ[ α ∈ CantorSpace ] fst (A α)
      --        = Σ[ α ∈ CantorSpace ] ((n : ℕ) → fst (Cantor-to-Sp α) (f n) ≡ false)
      --
      -- Using the round-trip: Cantor-to-Sp (Sp-to-Cantor h) ≡ h

      Sp-freeBA-ℕ-≃ : SpGeneralBooleanRing (freeBA ℕ) ≃ CantorSpace
      Sp-freeBA-ℕ-≃ = isoToEquiv Sp-freeBA-ℕ-Iso

      -- Round trip property: Cantor-to-Sp ∘ Sp-to-Cantor ≡ id
      Cantor-Sp-roundtrip : (h : SpGeneralBooleanRing (freeBA ℕ)) → Cantor-to-Sp (Sp-to-Cantor h) ≡ h
      Cantor-Sp-roundtrip h = Iso.ret Sp-freeBA-ℕ-Iso h

      -- The fiber transport: for h : Sp(freeBA ℕ) with α = Sp-to-Cantor h,
      -- we have (fst h (f n) ≡ false) ≃ (fst (Cantor-to-Sp α) (f n) ≡ false)
      -- by substituting along the round-trip path
      fiber-transport : (h : SpGeneralBooleanRing (freeBA ℕ))
        → ((n : ℕ) → fst h (f n) ≡ false)
        ≃ ((n : ℕ) → fst (Cantor-to-Sp (Sp-to-Cantor h)) (f n) ≡ false)
      fiber-transport h = pathToEquiv' (cong (λ h' → (n : ℕ) → fst h' (f n) ≡ false) (sym (Cantor-Sp-roundtrip h)))

      ClosedSubsetSp≃ΣA : SQS.ClosedSubset ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      ClosedSubsetSp≃ΣA = Σ-cong-equiv Sp-freeBA-ℕ-≃ fiber-transport

      SpQ≃ΣA : BoolHom Q BoolBR ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      SpQ≃ΣA = compEquiv SpQ≃ClosedSubsetSp ClosedSubsetSp≃ΣA

      -- Now we need Sp B ≃ Sp Q
      -- B ≅ Q via equiv, so Sp B ≃ Sp Q
      -- Since equiv is a BooleanRingEquiv: ⟨B⟩ ≃ ⟨Q⟩ with the equivalence being a ring hom,
      -- composing with equiv⁻¹ gives the spectrum equivalence

      -- equiv-inv is a ring homomorphism (inverse of a ring isomorphism)
      -- For BooleanRingEquiv, the inverse is also a ring homomorphism
      open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanEquivToHomInv)

      equiv-inv-hom : BoolHom Q B
      equiv-inv-hom = BooleanEquivToHomInv B Q equiv

      -- Sp B ≃ Sp Q via precomposition with equiv-inv-hom
      SpB≃SpQ : Sp (B , ∣ (f , equiv) ∣₁) ≃ BoolHom Q BoolBR
      SpB≃SpQ = isoToEquiv SpB-SpQ-Iso
        where
        -- Forward: h : BoolHom B BoolBR ↦ h ∘ equiv-inv-hom : BoolHom Q BoolBR
        forward : BoolHom B BoolBR → BoolHom Q BoolBR
        forward h = h ∘cr equiv-inv-hom

        -- Backward: k : BoolHom Q BoolBR ↦ k ∘ equiv-hom : BoolHom B BoolBR
        equiv-hom : BoolHom B Q
        equiv-hom = fst B≃Q , snd equiv

        backward : BoolHom Q BoolBR → BoolHom B BoolBR
        backward k = k ∘cr equiv-hom

        -- Round-trips follow from the equivalence properties
        fwd∘bwd : (k : BoolHom Q BoolBR) → forward (backward k) ≡ k
        fwd∘bwd k = CommRingHom≡ (funExt λ q →
          cong (fst k) (secEq B≃Q q))

        bwd∘fwd : (h : BoolHom B BoolBR) → backward (forward h) ≡ h
        bwd∘fwd h = CommRingHom≡ (funExt λ b →
          cong (fst h) (retEq B≃Q b))

        SpB-SpQ-Iso : Iso (BoolHom B BoolBR) (BoolHom Q BoolBR)
        Iso.fun SpB-SpQ-Iso = forward
        Iso.inv SpB-SpQ-Iso = backward
        Iso.sec SpB-SpQ-Iso = fwd∘bwd
        Iso.ret SpB-SpQ-Iso = bwd∘fwd

      SpB≃ΣA : Sp (B , ∣ (f , equiv) ∣₁) ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      SpB≃ΣA = compEquiv SpB≃SpQ SpQ≃ΣA

    -- Now the main theorem: use truncation to handle the presentation
    -- Stone = TypeWithStr ℓ-zero hasStoneStr
    -- hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S
    -- Booleω = Σ[ B ∈ BooleanRing ℓ-zero ] ∥ has-Boole-ω' B ∥₁
    -- So S : Stone = (|S| , ((B , trunc-pres) , SpB≡S))
    Stone→ClosedInCantor : (S : Stone)
      → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (fst S ≃ (Σ[ x ∈ CantorSpace ] fst (fst A x))) ∥₁
    Stone→ClosedInCantor (|S| , ((B , trunc-pres) , SpB≡S)) =
      PT.rec squash₁ go trunc-pres
      where
      go : has-Boole-ω' B → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (|S| ≃ (Σ[ α ∈ CantorSpace ] fst (fst A α))) ∥₁
      go pres = ∣ fst (Stone→Closed-from-pres B pres) ,
                  compEquiv (pathToEquiv (sym SpB≡S)) (snd (Stone→Closed-from-pres B pres)) ∣₁

  open Stone→ClosedInCantorProof using (Stone→ClosedInCantor) public

  -- Converse: closed subset of 2^ℕ is Stone
  -- This follows from ClosedInStoneIsStone applied to CantorStone
  ClosedInCantor→Stone : (A : ClosedSubsetOfCantor)
    → hasStoneStr (Σ[ x ∈ CantorSpace ] (fst (fst A x)))
  ClosedInCantor→Stone (A , Aclosed) = ClosedInStoneIsStone CantorStone A Aclosed


-- End of Part10 - continued in Part10b
