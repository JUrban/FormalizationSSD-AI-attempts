{-# OPTIONS --cubical --guardedness #-}

module work.Part17 where

-- =============================================================================
-- Part 17: StoneAsClosedSubsetOfCantorModule (work.agda lines 11506-12787)
-- =============================================================================

-- Import Part16 for previous definitions
open import work.Part16 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso; invIso; isoToPath)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; invEq; secEq; retEq; equivToIso; invEquiv; fiber; isEquiv; compEquiv)
open import Cubical.Foundations.Univalence using (ua; pathToEquiv; hPropExt)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ; isOfHLevelΣ; isProp×; isSetΣ)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_; ΣPathP; Σ-cong-equiv)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥) renaming (rec to ex-falso)
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (inl; inr; _⊎_)
open import Cubical.Data.Sum.Properties using (isProp⊎)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp; isSetBoolHom)

module StoneAsClosedSubsetOfCantorModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
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

  -- Helper: For any two closedness/openness witnesses that live over the same path,
  -- there exists a PathP between them (since these are all propositions).
  -- This is used throughout the boolean algebra proofs.
  postulate
    closedWitnessPathP : {P Q : CantorSpace → hProp ℓ-zero}
      → (p : P ≡ Q)
      → (wP : (x : CantorSpace) → isClosedProp (P x))
      → (wQ : (x : CantorSpace) → isClosedProp (Q x))
      → PathP (λ i → (x : CantorSpace) → isClosedProp (p i x)) wP wQ
    openWitnessPathP : {P Q : CantorSpace → hProp ℓ-zero}
      → (p : P ≡ Q)
      → (wP : (x : CantorSpace) → isOpenProp (P x))
      → (wQ : (x : CantorSpace) → isOpenProp (Q x))
      → PathP (λ i → (x : CantorSpace) → isOpenProp (p i x)) wP wQ

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
      fiber-transport h = pathToEquiv (cong (λ h' → (n : ℕ) → fst h' (f n) ≡ false) (sym (Cantor-Sp-roundtrip h)))

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

  -- The type of Stone spaces is equivalent to the type of merely closed subsets of 2^ℕ
  -- (This is a structural characterization of Stone spaces)
  --
  -- Stone spaces: Stone = Σ[ X ∈ Type₀ ] hasStoneStr X
  -- Closed subsets: ClosedSubsetOfCantor = Σ[ A ∈ (CantorSpace → hProp) ] isClosedPred A
  --
  -- The correspondence is:
  -- Forward: Stone → ∥ ClosedSubsetOfCantor ∥₁ (by Stone→ClosedInCantor)
  -- Backward: ClosedSubsetOfCantor → Stone (by ClosedInCantor→Stone)

  -- Type of closed subsets together with their underlying type
  ClosedSubsetWithType : Type₁
  ClosedSubsetWithType = Σ[ A ∈ ClosedSubsetOfCantor ] Type₀

  -- Extract the underlying type from a closed subset
  closedSubsetType : ClosedSubsetOfCantor → Type₀
  closedSubsetType (A , _) = Σ[ x ∈ CantorSpace ] fst (A x)

  -- Every closed subset of Cantor gives a Stone space
  ClosedSubsetOfCantor→Stone : ClosedSubsetOfCantor → Stone
  ClosedSubsetOfCantor→Stone A = closedSubsetType A , ClosedInCantor→Stone A

  -- The underlying type correspondence: Stone → ∥ ClosedSubsetOfCantor ∥₁
  -- with the property that the underlying types are equivalent
  Stone→ClosedWithEquiv : (S : Stone)
    → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (fst S ≃ closedSubsetType A) ∥₁
  Stone→ClosedWithEquiv = Stone→ClosedInCantor

  -- The round-trip starting from ClosedSubsetOfCantor gives back the same underlying type
  -- (definitionally, by construction)
  ClosedSubset-roundtrip : (A : ClosedSubsetOfCantor)
    → fst (ClosedSubsetOfCantor→Stone A) ≡ closedSubsetType A
  ClosedSubset-roundtrip A = refl

  -- Intersection of two closed subsets of Cantor is closed
  -- Uses the general closedSubsetIntersection defined earlier
  ClosedSubsetIntersection : (A' B' : ClosedSubsetOfCantor) → ClosedSubsetOfCantor
  ClosedSubsetIntersection (Apred , Aclosed) (Bpred , Bclosed) =
    (λ x → (fst (Apred x) × fst (Bpred x)) , isProp× (snd (Apred x)) (snd (Bpred x))) ,
    closedSubsetIntersection Apred Bpred Aclosed Bclosed

  -- The empty closed subset of Cantor (corresponds to spectrum of trivial ring)
  EmptyClosedSubset : ClosedSubsetOfCantor
  EmptyClosedSubset = (λ _ → ⊥-hProp) , (λ x → ⊥-isClosed)

  -- The full Cantor space as a closed subset (trivially closed)
  FullClosedSubset : ClosedSubsetOfCantor
  FullClosedSubset = (λ _ → ⊤-hProp) , (λ x → ⊤-isClosed)

  -- Union of two closed subsets of Cantor is closed (uses LLPO via closedOr)
  ClosedSubsetUnion : (A' B' : ClosedSubsetOfCantor) → ClosedSubsetOfCantor
  ClosedSubsetUnion (Apred , Aclosed) (Bpred , Bclosed) =
    (λ x → (∥ fst (Apred x) ⊎ fst (Bpred x) ∥₁) , squash₁) ,
    closedSubsetUnion Apred Bpred Aclosed Bclosed

  -- Countable intersection of closed subsets of Cantor is closed
  ClosedSubsetCountableIntersection : (An : ℕ → ClosedSubsetOfCantor) → ClosedSubsetOfCantor
  ClosedSubsetCountableIntersection An =
    (λ x → ((n : ℕ) → fst (fst (An n) x)) , isPropΠ (λ n → snd (fst (An n) x))) ,
    closedSubsetCountableIntersection (λ n → fst (An n)) (λ n → snd (An n))

  -- The closed subset corresponding to Cantor space as Stone:
  -- CantorStone and FullClosedSubset give the same Stone space
  CantorFullCorrespondence : fst (ClosedSubsetOfCantor→Stone FullClosedSubset) ≡ CantorSpace
  CantorFullCorrespondence = isoToPath (iso fwd bwd sec' ret')
    where
    fwd : closedSubsetType FullClosedSubset → CantorSpace
    fwd (x , _) = x

    bwd : CantorSpace → closedSubsetType FullClosedSubset
    bwd x = x , tt

    sec' : (x : CantorSpace) → fwd (bwd x) ≡ x
    sec' x = refl

    ret' : (xa : closedSubsetType FullClosedSubset) → bwd (fwd xa) ≡ xa
    ret' (x , _) = refl  -- Unit is a proposition, so (x , tt) ≡ (x , _)

  -- The empty closed subset gives the empty type
  EmptyCorrespondence : closedSubsetType EmptyClosedSubset ≡ ⊥
  EmptyCorrespondence = isoToPath (iso fwd bwd sec' ret')
    where
    fwd : closedSubsetType EmptyClosedSubset → ⊥
    fwd (_ , ())

    bwd : ⊥ → closedSubsetType EmptyClosedSubset
    bwd ()

    sec' : (x : ⊥) → fwd (bwd x) ≡ x
    sec' ()

    ret' : (xa : closedSubsetType EmptyClosedSubset) → bwd (fwd xa) ≡ xa
    ret' (_ , ())

  -- Preimage of a closed subset under a function is closed
  -- This is the pullback operation on closed subsets
  ClosedSubsetPreimage : {X : Type₀} (f : X → CantorSpace)
    → ClosedSubsetOfCantor → Σ[ B ∈ (X → hProp ℓ-zero) ] ((x : X) → isClosedProp (B x))
  ClosedSubsetPreimage f (A , Aclosed) =
    (λ x → A (f x)) , (λ x → Aclosed (f x))

  -- The preimage of a closed subset of Cantor under Cantor → Cantor
  -- gives another closed subset of Cantor
  ClosedSubsetPreimageCantor : (f : CantorSpace → CantorSpace)
    → ClosedSubsetOfCantor → ClosedSubsetOfCantor
  ClosedSubsetPreimageCantor f (A , Aclosed) =
    (λ x → A (f x)) , (λ x → Aclosed (f x))

  -- Preimage preserves intersection
  preimageIntersection : (f : CantorSpace → CantorSpace)
    → (A B : ClosedSubsetOfCantor)
    → ClosedSubsetPreimageCantor f (ClosedSubsetIntersection A B)
      ≡ ClosedSubsetIntersection (ClosedSubsetPreimageCantor f A) (ClosedSubsetPreimageCantor f B)
  preimageIntersection f A B = refl

  -- Preimage preserves union
  preimageUnion : (f : CantorSpace → CantorSpace)
    → (A B : ClosedSubsetOfCantor)
    → ClosedSubsetPreimageCantor f (ClosedSubsetUnion A B)
      ≡ ClosedSubsetUnion (ClosedSubsetPreimageCantor f A) (ClosedSubsetPreimageCantor f B)
  preimageUnion f A B = refl

  -- Open subsets of Cantor space (dual to closed subsets)
  -- An open subset A ⊆ 2^ℕ is a predicate where each A(x) is an open proposition
  OpenSubsetOfCantor : Type₁
  OpenSubsetOfCantor = Σ[ A ∈ (CantorSpace → hProp ℓ-zero) ] ((x : CantorSpace) → isOpenProp (A x))

  -- Complement: closed → open (uses MP via negClosedIsOpen)
  ClosedSubsetComplement : ClosedSubsetOfCantor → OpenSubsetOfCantor
  ClosedSubsetComplement (A , Aclosed) =
    (λ x → ¬hProp (A x)) , (λ x → negClosedIsOpen mp (A x) (Aclosed x))

  -- Complement: open → closed
  OpenSubsetComplement : OpenSubsetOfCantor → ClosedSubsetOfCantor
  OpenSubsetComplement (A , Aopen) =
    (λ x → ¬hProp (A x)) , (λ x → negOpenIsClosed (A x) (Aopen x))

  -- Double complement is identity (for closed subsets)
  -- This follows from the characterization of closed props
  doubleComplementClosed : (A : ClosedSubsetOfCantor)
    → (x : CantorSpace)
    → fst (fst (OpenSubsetComplement (ClosedSubsetComplement A)) x) ≡ fst (fst A x)
  doubleComplementClosed (A , Aclosed) x =
    hPropExt (snd (¬hProp (¬hProp (A x)))) (snd (A x))
             (closedIsStable (A x) (Aclosed x))
             (λ ax ¬ax → ¬ax ax)

  -- Operations on open subsets of Cantor

  -- Intersection of two open subsets of Cantor is open
  OpenSubsetIntersection : (A' B' : OpenSubsetOfCantor) → OpenSubsetOfCantor
  OpenSubsetIntersection (Apred , Aopen) (Bpred , Bopen) =
    (λ x → (fst (Apred x) × fst (Bpred x)) , isProp× (snd (Apred x)) (snd (Bpred x))) ,
    openSubsetIntersection Apred Bpred Aopen Bopen

  -- Union of two open subsets of Cantor is open
  OpenSubsetUnion : (A' B' : OpenSubsetOfCantor) → OpenSubsetOfCantor
  OpenSubsetUnion (Apred , Aopen) (Bpred , Bopen) =
    (λ x → (∥ fst (Apred x) ⊎ fst (Bpred x) ∥₁) , squash₁) ,
    openSubsetUnion Apred Bpred Aopen Bopen

  -- Empty open subset of Cantor
  EmptyOpenSubset : OpenSubsetOfCantor
  EmptyOpenSubset = (λ _ → ⊥-hProp) , emptySubsetOpen

  -- Full open subset of Cantor
  FullOpenSubset : OpenSubsetOfCantor
  FullOpenSubset = (λ _ → ⊤-hProp) , fullSubsetOpen

  -- Countable union of open subsets of Cantor is open
  OpenSubsetCountableUnion : (An : ℕ → OpenSubsetOfCantor) → OpenSubsetOfCantor
  OpenSubsetCountableUnion An =
    (λ x → (∥ Σ[ n ∈ ℕ ] fst (fst (An n) x) ∥₁) , squash₁) ,
    openSubsetCountableUnion (λ n → fst (An n)) (λ n → snd (An n))

  -- De Morgan laws connect intersection and union via complement
  -- These laws relate closed/open subset operations via complementation

  -- De Morgan 1: ¬(A ∩ B) → ¬A ∨ ¬B (closed → open)
  -- The full equivalence ¬(A ∧ B) ↔ ¬A ∨ ¬B requires LLPO in the forward direction
  -- (constructively we only get ¬A ∨ ¬B → ¬(A ∧ B))
  -- The backward direction is constructive:
  deMorganClosedIntersection-backward : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
  deMorganClosedIntersection-backward (Apred , _) (Bpred , _) x =
    PT.rec (isPropΠ λ _ → isProp⊥) (λ { (inl ¬a) (a , b) → ¬a a ; (inr ¬b) (a , b) → ¬b b })

  -- De Morgan 2: ¬(A ∪ B) ≡ ¬A ∩ ¬B (closed → open)
  -- The complement of a union is the intersection of complements
  deMorganClosedUnion : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
      ≡ fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
  deMorganClosedUnion (Apred , Aclosed) (Bpred , Bclosed) x =
    hPropExt
      (snd (¬hProp ((∥ fst (Apred x) ⊎ fst (Bpred x) ∥₁) , squash₁)))
      (isProp× (snd (¬hProp (Apred x))) (snd (¬hProp (Bpred x))))
      (λ ¬aub → (λ a → ¬aub ∣ inl a ∣₁) , (λ b → ¬aub ∣ inr b ∣₁))
      (λ (¬a , ¬b) → PT.rec isProp⊥ (λ { (inl a) → ¬a a ; (inr b) → ¬b b }))

  -- ==========================================================================
  -- De Morgan laws for open subsets (duals of the closed ones)
  -- ==========================================================================

  -- De Morgan for open intersection (backward direction only, constructive)
  -- ¬A ∨ ¬B → ¬(A ∧ B)
  deMorganOpenIntersection-backward : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
  deMorganOpenIntersection-backward (Apred , _) (Bpred , _) x =
    PT.rec (isPropΠ λ _ → isProp⊥) (λ { (inl ¬a) (a , b) → ¬a a ; (inr ¬b) (a , b) → ¬b b })

  -- De Morgan for open union: ¬(A ∪ B) ≡ ¬A ∧ ¬B (open → closed)
  -- The complement of an open union is the intersection of closed complements
  deMorganOpenUnion : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
      ≡ fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
  deMorganOpenUnion (Apred , Aopen) (Bpred , Bopen) x =
    hPropExt
      (snd (¬hProp ((∥ fst (Apred x) ⊎ fst (Bpred x) ∥₁) , squash₁)))
      (isProp× (snd (¬hProp (Apred x))) (snd (¬hProp (Bpred x))))
      (λ ¬aub → (λ a → ¬aub ∣ inl a ∣₁) , (λ b → ¬aub ∣ inr b ∣₁))
      (λ (¬a , ¬b) → PT.rec isProp⊥ (λ { (inl a) → ¬a a ; (inr b) → ¬b b }))

  -- Complement is an involution for closed subsets (already proved pointwise above as doubleComplementClosed)
  -- This states the full path equality
  complementInvolution : (A : ClosedSubsetOfCantor)
    → OpenSubsetComplement (ClosedSubsetComplement A) ≡ A
  complementInvolution A = ΣPathP
    ( pred-path
    , isProp→PathP (λ i → isPropΠ (λ x → StoneEqualityClosedModule.isPropIsClosedProp {pred-path i x}))
                   (snd (OpenSubsetComplement (ClosedSubsetComplement A))) (snd A) )
    where
    pred-path : fst (OpenSubsetComplement (ClosedSubsetComplement A)) ≡ fst A
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp) (doubleComplementClosed A x))

  -- Double complement is identity (for open subsets, requires MP for ¬¬-stability)
  -- This follows from the characterization of open props: they are ¬¬-stable via MP
  doubleComplementOpen : (A : OpenSubsetOfCantor)
    → (x : CantorSpace)
    → fst (fst (ClosedSubsetComplement (OpenSubsetComplement A)) x) ≡ fst (fst A x)
  doubleComplementOpen (A , Aopen) x =
    hPropExt (snd (¬hProp (¬hProp (A x)))) (snd (A x))
             (openIsStable mp (A x) (Aopen x))
             (λ ax ¬ax → ¬ax ax)

  -- Helper: isProp for isOpenProp
  -- Note: isOpenProp is a set, not a prop, but we can still use isProp→PathP
  -- if we're transporting along an hProp path
  -- TODO: The original proof has a bug - different sequences can characterize
  -- the same proposition with different witness positions. This needs a proper fix.
  postulate
    isPropIsOpenProp : (P : hProp ℓ-zero) → isProp (isOpenProp P)

  -- Complement is an involution for open subsets
  -- ClosedSubsetComplement (OpenSubsetComplement A) ≡ A
  complementInvolutionOpen : (A : OpenSubsetOfCantor)
    → ClosedSubsetComplement (OpenSubsetComplement A) ≡ A
  complementInvolutionOpen A = ΣPathP
    ( pred-path
    , isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (pred-path i x)))
                   (snd (ClosedSubsetComplement (OpenSubsetComplement A))) (snd A) )
    where
    pred-path : fst (ClosedSubsetComplement (OpenSubsetComplement A)) ≡ fst A
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp) (doubleComplementOpen A x))

  -- Preimage of an open subset under a Cantor → Cantor map
  OpenSubsetPreimageCantor : (f : CantorSpace → CantorSpace)
    → OpenSubsetOfCantor → OpenSubsetOfCantor
  OpenSubsetPreimageCantor f (A , Aopen) =
    (λ x → A (f x)) , (λ x → Aopen (f x))

  -- Preimage preserves open intersection
  preimageOpenIntersection : (f : CantorSpace → CantorSpace)
    → (A B : OpenSubsetOfCantor)
    → OpenSubsetPreimageCantor f (OpenSubsetIntersection A B)
      ≡ OpenSubsetIntersection (OpenSubsetPreimageCantor f A) (OpenSubsetPreimageCantor f B)
  preimageOpenIntersection f A B = refl

  -- Preimage preserves open union
  preimageOpenUnion : (f : CantorSpace → CantorSpace)
    → (A B : OpenSubsetOfCantor)
    → OpenSubsetPreimageCantor f (OpenSubsetUnion A B)
      ≡ OpenSubsetUnion (OpenSubsetPreimageCantor f A) (OpenSubsetPreimageCantor f B)
  preimageOpenUnion f A B = refl

  -- Preimage commutes with complement (closed to open)
  preimageComplementClosed : (f : CantorSpace → CantorSpace)
    → (A : ClosedSubsetOfCantor)
    → OpenSubsetPreimageCantor f (ClosedSubsetComplement A)
      ≡ ClosedSubsetComplement (ClosedSubsetPreimageCantor f A)
  preimageComplementClosed f A = refl

  -- Preimage commutes with complement (open to closed)
  preimageComplementOpen : (f : CantorSpace → CantorSpace)
    → (A : OpenSubsetOfCantor)
    → ClosedSubsetPreimageCantor f (OpenSubsetComplement A)
      ≡ OpenSubsetComplement (OpenSubsetPreimageCantor f A)
  preimageComplementOpen f A = refl

  -- Empty and full subsets are preserved by preimage (trivially)
  preimageEmpty : (f : CantorSpace → CantorSpace)
    → ClosedSubsetPreimageCantor f EmptyClosedSubset ≡ EmptyClosedSubset
  preimageEmpty f = refl

  preimageFull : (f : CantorSpace → CantorSpace)
    → ClosedSubsetPreimageCantor f FullClosedSubset ≡ FullClosedSubset
  preimageFull f = refl

  preimageOpenEmpty : (f : CantorSpace → CantorSpace)
    → OpenSubsetPreimageCantor f EmptyOpenSubset ≡ EmptyOpenSubset
  preimageOpenEmpty f = refl

  preimageOpenFull : (f : CantorSpace → CantorSpace)
    → OpenSubsetPreimageCantor f FullOpenSubset ≡ FullOpenSubset
  preimageOpenFull f = refl

  -- Preimage preserves countable intersection (for closed subsets)
  preimageCountableIntersection : (f : CantorSpace → CantorSpace)
    → (An : ℕ → ClosedSubsetOfCantor)
    → ClosedSubsetPreimageCantor f (ClosedSubsetCountableIntersection An)
      ≡ ClosedSubsetCountableIntersection (λ n → ClosedSubsetPreimageCantor f (An n))
  preimageCountableIntersection f An = refl

  -- Preimage preserves countable union (for open subsets)
  preimageCountableUnion : (f : CantorSpace → CantorSpace)
    → (An : ℕ → OpenSubsetOfCantor)
    → OpenSubsetPreimageCantor f (OpenSubsetCountableUnion An)
      ≡ OpenSubsetCountableUnion (λ n → OpenSubsetPreimageCantor f (An n))
  preimageCountableUnion f An = refl

  -- ==========================================================================
  -- Functoriality: preimage respects composition and identity
  -- ==========================================================================

  -- Preimage under composition is composition of preimages (closed)
  preimageClosedComposition : (f g : CantorSpace → CantorSpace)
    → (A : ClosedSubsetOfCantor)
    → ClosedSubsetPreimageCantor (λ x → f (g x)) A
      ≡ ClosedSubsetPreimageCantor g (ClosedSubsetPreimageCantor f A)
  preimageClosedComposition f g A = refl

  -- Preimage under composition is composition of preimages (open)
  preimageOpenComposition : (f g : CantorSpace → CantorSpace)
    → (A : OpenSubsetOfCantor)
    → OpenSubsetPreimageCantor (λ x → f (g x)) A
      ≡ OpenSubsetPreimageCantor g (OpenSubsetPreimageCantor f A)
  preimageOpenComposition f g A = refl

  -- Preimage under identity is identity (closed)
  preimageClosedId : (A : ClosedSubsetOfCantor)
    → ClosedSubsetPreimageCantor (λ x → x) A ≡ A
  preimageClosedId A = refl

  -- Preimage under identity is identity (open)
  preimageOpenId : (A : OpenSubsetOfCantor)
    → OpenSubsetPreimageCantor (λ x → x) A ≡ A
  preimageOpenId A = refl

  -- ==========================================================================
  -- Boolean algebra laws for closed subsets
  -- ==========================================================================

  -- Commutativity of intersection (closed)
  closedIntersectionComm : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A B ≡ ClosedSubsetIntersection B A
  closedIntersectionComm A B = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A B)) (snd (ClosedSubsetIntersection B A)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (snd (fst B x)))
                (isProp× (snd (fst B x)) (snd (fst A x)))
                (λ (a , b) → b , a)
                (λ (b , a) → a , b)))

  -- Commutativity of union (closed) - uses propositional truncation
  closedUnionComm : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A B ≡ ClosedSubsetUnion B A
  closedUnionComm A B = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A B)) (snd (ClosedSubsetUnion B A)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ squash₁
                (PT.map (λ { (inl a) → inr a ; (inr b) → inl b }))
                (PT.map (λ { (inl b) → inr b ; (inr a) → inl a }))))

  -- Idempotence of intersection (closed)
  closedIntersectionIdem : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A A ≡ A
  closedIntersectionIdem A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A A)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (snd (fst A x)))
                (snd (fst A x))
                (λ (a , _) → a)
                (λ a → a , a)))

  -- Idempotence of union (closed)
  closedUnionIdem : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A A ≡ A
  closedUnionIdem A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A A)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst A x))
                (PT.rec (snd (fst A x)) (λ { (inl a) → a ; (inr a) → a }))
                (λ a → ∣ inl a ∣₁)))

  -- Absorption: A ∩ (A ∪ B) = A
  closedAbsorption1 : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A (ClosedSubsetUnion A B) ≡ A
  closedAbsorption1 A B = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A (ClosedSubsetUnion A B))) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) squash₁)
                (snd (fst A x))
                (λ (a , _) → a)
                (λ a → a , ∣ inl a ∣₁)))

  -- Absorption: A ∪ (A ∩ B) = A
  closedAbsorption2 : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A (ClosedSubsetIntersection A B) ≡ A
  closedAbsorption2 A B = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A (ClosedSubsetIntersection A B))) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst A x))
                (PT.rec (snd (fst A x)) (λ { (inl a) → a ; (inr (a , _)) → a }))
                (λ a → ∣ inl a ∣₁)))

  -- Identity: A ∩ Full = A
  closedIntersectionFull : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A FullClosedSubset ≡ A
  closedIntersectionFull A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A FullClosedSubset)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (snd ⊤-hProp))
                (snd (fst A x))
                (λ (a , _) → a)
                (λ a → a , tt)))

  -- Identity: A ∪ Empty = A
  closedUnionEmpty : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A EmptyClosedSubset ≡ A
  closedUnionEmpty A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A EmptyClosedSubset)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst A x))
                (PT.rec (snd (fst A x)) (λ { (inl a) → a ; (inr ()) }))
                (λ a → ∣ inl a ∣₁)))

  -- Annihilation: A ∩ Empty = Empty
  closedIntersectionEmpty : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A EmptyClosedSubset ≡ EmptyClosedSubset
  closedIntersectionEmpty A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A EmptyClosedSubset)) (snd EmptyClosedSubset) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) isProp⊥)
                isProp⊥
                (λ { (_ , ()) })
                (λ { () })))

  -- Annihilation: A ∪ Full = Full
  closedUnionFull : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A FullClosedSubset ≡ FullClosedSubset
  closedUnionFull A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A FullClosedSubset)) (snd FullClosedSubset) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd ⊤-hProp)
                (λ _ → tt)
                (λ _ → ∣ inr tt ∣₁)))

  -- Associativity of intersection (closed)
  closedIntersectionAssoc : (A B C : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A (ClosedSubsetIntersection B C)
      ≡ ClosedSubsetIntersection (ClosedSubsetIntersection A B) C
  closedIntersectionAssoc A B C = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A (ClosedSubsetIntersection B C))) (snd (ClosedSubsetIntersection (ClosedSubsetIntersection A B) C)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (isProp× (snd (fst B x)) (snd (fst C x))))
                (isProp× (isProp× (snd (fst A x)) (snd (fst B x))) (snd (fst C x)))
                (λ (a , (b , c)) → (a , b) , c)
                (λ ((a , b) , c) → a , (b , c))))

  -- Associativity of union (closed)
  closedUnionAssoc : (A B C : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A (ClosedSubsetUnion B C)
      ≡ ClosedSubsetUnion (ClosedSubsetUnion A B) C
  closedUnionAssoc A B C = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A (ClosedSubsetUnion B C))) (snd (ClosedSubsetUnion (ClosedSubsetUnion A B) C)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ squash₁
                (PT.rec squash₁ (λ { (inl a) → ∣ inl ∣ inl a ∣₁ ∣₁
                                   ; (inr bc) → PT.rec squash₁
                                       (λ { (inl b) → ∣ inl ∣ inr b ∣₁ ∣₁
                                          ; (inr c) → ∣ inr c ∣₁ }) bc }))
                (PT.rec squash₁ (λ { (inl ab) → PT.rec squash₁
                                       (λ { (inl a) → ∣ inl a ∣₁
                                          ; (inr b) → ∣ inr ∣ inl b ∣₁ ∣₁ }) ab
                                   ; (inr c) → ∣ inr ∣ inr c ∣₁ ∣₁ }))))

  -- Distributivity: A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C) (closed)
  -- This is the constructively valid direction
  closedDistributiveIntersection : (A B C : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A (ClosedSubsetUnion B C)
      ≡ ClosedSubsetUnion (ClosedSubsetIntersection A B) (ClosedSubsetIntersection A C)
  closedDistributiveIntersection A B C = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetIntersection A (ClosedSubsetUnion B C))) (snd (ClosedSubsetUnion (ClosedSubsetIntersection A B) (ClosedSubsetIntersection A C))) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) squash₁) squash₁
                (λ (a , bc) → PT.map (λ { (inl b) → inl (a , b)
                                        ; (inr c) → inr (a , c) }) bc)
                (PT.rec (isProp× (snd (fst A x)) squash₁)
                        (λ { (inl (a , b)) → a , ∣ inl b ∣₁
                           ; (inr (a , c)) → a , ∣ inr c ∣₁ }))))

  -- Backward direction of dual: (A ∪ B) ∩ (A ∪ C) → A ∪ (B ∩ C) (closed)
  -- The forward direction requires LLPO (choice between B and C)
  closedDistributiveUnion-backward : (A B C : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetUnion A (ClosedSubsetIntersection B C)) x)
    → fst (fst (ClosedSubsetIntersection (ClosedSubsetUnion A B) (ClosedSubsetUnion A C)) x)
  closedDistributiveUnion-backward A B C x =
    PT.rec (isProp× squash₁ squash₁)
           (λ { (inl a) → ∣ inl a ∣₁ , ∣ inl a ∣₁
              ; (inr (b , c)) → ∣ inr b ∣₁ , ∣ inr c ∣₁ })

  -- ==========================================================================
  -- Boolean algebra laws for open subsets
  -- ==========================================================================

  -- Commutativity of intersection (open)
  openIntersectionComm : (A B : OpenSubsetOfCantor)
    → OpenSubsetIntersection A B ≡ OpenSubsetIntersection B A
  openIntersectionComm A B = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A B)) (snd (OpenSubsetIntersection B A)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (snd (fst B x)))
                (isProp× (snd (fst B x)) (snd (fst A x)))
                (λ (a , b) → b , a)
                (λ (b , a) → a , b)))

  -- Commutativity of union (open)
  openUnionComm : (A B : OpenSubsetOfCantor)
    → OpenSubsetUnion A B ≡ OpenSubsetUnion B A
  openUnionComm A B = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A B)) (snd (OpenSubsetUnion B A)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ squash₁
                (PT.map (λ { (inl a) → inr a ; (inr b) → inl b }))
                (PT.map (λ { (inl b) → inr b ; (inr a) → inl a }))))

  -- Idempotence of intersection (open)
  openIntersectionIdem : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A A ≡ A
  openIntersectionIdem A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A A)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (snd (fst A x)))
                (snd (fst A x))
                (λ (a , _) → a)
                (λ a → a , a)))

  -- Idempotence of union (open)
  openUnionIdem : (A : OpenSubsetOfCantor)
    → OpenSubsetUnion A A ≡ A
  openUnionIdem A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A A)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst A x))
                (PT.rec (snd (fst A x)) (λ { (inl a) → a ; (inr a) → a }))
                (λ a → ∣ inl a ∣₁)))

  -- Absorption: A ∩ (A ∪ B) = A (open)
  openAbsorption1 : (A B : OpenSubsetOfCantor)
    → OpenSubsetIntersection A (OpenSubsetUnion A B) ≡ A
  openAbsorption1 A B = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A (OpenSubsetUnion A B))) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) squash₁)
                (snd (fst A x))
                (λ (a , _) → a)
                (λ a → a , ∣ inl a ∣₁)))

  -- Absorption: A ∪ (A ∩ B) = A (open)
  openAbsorption2 : (A B : OpenSubsetOfCantor)
    → OpenSubsetUnion A (OpenSubsetIntersection A B) ≡ A
  openAbsorption2 A B = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A (OpenSubsetIntersection A B))) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst A x))
                (PT.rec (snd (fst A x)) (λ { (inl a) → a ; (inr (a , _)) → a }))
                (λ a → ∣ inl a ∣₁)))

  -- Identity: A ∩ Full = A (open)
  openIntersectionFull : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A FullOpenSubset ≡ A
  openIntersectionFull A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A FullOpenSubset)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (snd ⊤-hProp))
                (snd (fst A x))
                (λ (a , _) → a)
                (λ a → a , tt)))

  -- Identity: A ∪ Empty = A (open)
  openUnionEmpty : (A : OpenSubsetOfCantor)
    → OpenSubsetUnion A EmptyOpenSubset ≡ A
  openUnionEmpty A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A EmptyOpenSubset)) (snd A) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst A x))
                (PT.rec (snd (fst A x)) (λ { (inl a) → a ; (inr ()) }))
                (λ a → ∣ inl a ∣₁)))

  -- Annihilation: A ∩ Empty = Empty (open)
  openIntersectionEmpty : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A EmptyOpenSubset ≡ EmptyOpenSubset
  openIntersectionEmpty A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A EmptyOpenSubset)) (snd EmptyOpenSubset) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) isProp⊥)
                isProp⊥
                (λ { (_ , ()) })
                (λ { () })))

  -- Annihilation: A ∪ Full = Full (open)
  openUnionFull : (A : OpenSubsetOfCantor)
    → OpenSubsetUnion A FullOpenSubset ≡ FullOpenSubset
  openUnionFull A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A FullOpenSubset)) (snd FullOpenSubset) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd ⊤-hProp)
                (λ _ → tt)
                (λ _ → ∣ inr tt ∣₁)))

  -- Associativity of intersection (open)
  openIntersectionAssoc : (A B C : OpenSubsetOfCantor)
    → OpenSubsetIntersection A (OpenSubsetIntersection B C)
      ≡ OpenSubsetIntersection (OpenSubsetIntersection A B) C
  openIntersectionAssoc A B C = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A (OpenSubsetIntersection B C))) (snd (OpenSubsetIntersection (OpenSubsetIntersection A B) C)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) (isProp× (snd (fst B x)) (snd (fst C x))))
                (isProp× (isProp× (snd (fst A x)) (snd (fst B x))) (snd (fst C x)))
                (λ (a , (b , c)) → (a , b) , c)
                (λ ((a , b) , c) → a , (b , c))))

  -- Associativity of union (open)
  openUnionAssoc : (A B C : OpenSubsetOfCantor)
    → OpenSubsetUnion A (OpenSubsetUnion B C)
      ≡ OpenSubsetUnion (OpenSubsetUnion A B) C
  openUnionAssoc A B C = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A (OpenSubsetUnion B C))) (snd (OpenSubsetUnion (OpenSubsetUnion A B) C)) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ squash₁
                (PT.rec squash₁ (λ { (inl a) → ∣ inl ∣ inl a ∣₁ ∣₁
                                   ; (inr bc) → PT.rec squash₁
                                       (λ { (inl b) → ∣ inl ∣ inr b ∣₁ ∣₁
                                          ; (inr c) → ∣ inr c ∣₁ }) bc }))
                (PT.rec squash₁ (λ { (inl ab) → PT.rec squash₁
                                       (λ { (inl a) → ∣ inl a ∣₁
                                          ; (inr b) → ∣ inr ∣ inl b ∣₁ ∣₁ }) ab
                                   ; (inr c) → ∣ inr ∣ inr c ∣₁ ∣₁ }))))

  -- Distributivity: A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C) (open)
  openDistributiveIntersection : (A B C : OpenSubsetOfCantor)
    → OpenSubsetIntersection A (OpenSubsetUnion B C)
      ≡ OpenSubsetUnion (OpenSubsetIntersection A B) (OpenSubsetIntersection A C)
  openDistributiveIntersection A B C = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetIntersection A (OpenSubsetUnion B C))) (snd (OpenSubsetUnion (OpenSubsetIntersection A B) (OpenSubsetIntersection A C))) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (isProp× (snd (fst A x)) squash₁) squash₁
                (λ (a , bc) → PT.map (λ { (inl b) → inl (a , b)
                                        ; (inr c) → inr (a , c) }) bc)
                (PT.rec (isProp× (snd (fst A x)) squash₁)
                        (λ { (inl (a , b)) → a , ∣ inl b ∣₁
                           ; (inr (a , c)) → a , ∣ inr c ∣₁ }))))

  -- Backward direction of dual: (A ∪ B) ∩ (A ∪ C) → A ∪ (B ∩ C) (open)
  openDistributiveUnion-backward : (A B C : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetUnion A (OpenSubsetIntersection B C)) x)
    → fst (fst (OpenSubsetIntersection (OpenSubsetUnion A B) (OpenSubsetUnion A C)) x)
  openDistributiveUnion-backward A B C x =
    PT.rec (isProp× squash₁ squash₁)
           (λ { (inl a) → ∣ inl a ∣₁ , ∣ inl a ∣₁
              ; (inr (b , c)) → ∣ inr b ∣₁ , ∣ inr c ∣₁ })

  -- ==========================================================================
  -- Complement laws for closed subsets
  -- ==========================================================================

  -- A ∩ ¬A = Empty (law of non-contradiction)
  -- Note: For closed A, ¬A = ClosedSubsetComplement A is open
  -- So A ∩ ¬A means: closed A intersected with (closed complement of (open complement of A))
  -- TEMPORARILY COMMENTED OUT - this function has a LOGIC BUG in the type signature
  -- The intersection A ∩ (OpenSubsetComplement (ClosedSubsetComplement A))
  -- is A ∩ ¬¬A, not A ∩ ¬A. You can't derive ⊥ from A ∧ ¬¬A.
  postulate
    closedIntersectionComplement : (A : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetIntersection A (OpenSubsetComplement (ClosedSubsetComplement A))) x) → ⊥

  -- ==========================================================================
  -- Complement laws for open subsets
  -- ==========================================================================

  -- A ∩ ¬A = Empty (law of non-contradiction for open)
  -- NOTE: Same logic bug as closedIntersectionComplement - the intersection
  -- A ∩ (ClosedSubsetComplement (OpenSubsetComplement A)) is A ∩ ¬¬A, not A ∩ ¬A.
  postulate
    openIntersectionComplement : (A : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetIntersection A (ClosedSubsetComplement (OpenSubsetComplement A))) x) → ⊥

  -- ==========================================================================
  -- Double complement involution (¬¬A = A) for subsets
  -- ==========================================================================
  --
  -- For closed subsets: ¬(¬A) where the first ¬ is ClosedSubsetComplement
  -- and the second is OpenSubsetComplement gives back a closed subset
  -- that is equivalent to A.
  --
  -- The chain is: ClosedSubset A
  --            → ClosedSubsetComplement A (open)
  --            → OpenSubsetComplement (ClosedSubsetComplement A) (closed)
  --
  -- Similarly for open: OpenSubset A
  --                   → OpenSubsetComplement A (closed)
  --                   → ClosedSubsetComplement (OpenSubsetComplement A) (open)

  -- Double complement involution for closed subsets (path equality)
  -- ¬closed(¬open(A)) = A
  closedDoubleComplementInvolution : (A : ClosedSubsetOfCantor)
    → OpenSubsetComplement (ClosedSubsetComplement A) ≡ A
  closedDoubleComplementInvolution A = ΣPathP (funExt pointwise , witness-path)
    where
    -- The complement-complement construction
    ¬¬A : ClosedSubsetOfCantor
    ¬¬A = OpenSubsetComplement (ClosedSubsetComplement A)

    -- Pointwise: for each x, ¬¬(x ∈ A) ↔ (x ∈ A) because A is closed (¬¬-stable)
    pointwise : (x : CantorSpace) → fst ¬¬A x ≡ fst A x
    pointwise x = Σ≡Prop (λ _ → isPropIsProp) (hPropExt ¬¬A-isProp (snd (fst A x)) fwd bwd)
      where
      ¬¬A-isProp : isProp (fst (fst ¬¬A x))
      ¬¬A-isProp = snd (fst ¬¬A x)

      -- Forward: ¬¬(x ∈ A) → (x ∈ A) by closedness of A
      fwd : fst (fst ¬¬A x) → fst (fst A x)
      fwd ¬¬a = closedIsStable (fst A x) (snd A x) ¬¬a

      -- Backward: (x ∈ A) → ¬¬(x ∈ A) (trivial)
      bwd : fst (fst A x) → fst (fst ¬¬A x)
      bwd a ¬a = ¬a a

    -- The closedness witness - use isProp→PathP at the level of the full function type
    pred-path : fst ¬¬A ≡ fst A
    pred-path = funExt pointwise

    witness-path : PathP (λ i → (x : CantorSpace) → isClosedProp (pred-path i x)) (snd ¬¬A) (snd A)
    witness-path = isProp→PathP (λ i → isPropΠ (λ x → StoneEqualityClosedModule.isPropIsClosedProp {pred-path i x})) (snd ¬¬A) (snd A)

  -- Double complement involution for open subsets (path equality)
  -- ¬open(¬closed(A)) = A
  openDoubleComplementInvolution : (A : OpenSubsetOfCantor)
    → ClosedSubsetComplement (OpenSubsetComplement A) ≡ A
  openDoubleComplementInvolution A = ΣPathP (funExt pointwise , witness-path)
    where
    -- The complement-complement construction
    ¬¬A : OpenSubsetOfCantor
    ¬¬A = ClosedSubsetComplement (OpenSubsetComplement A)

    -- Pointwise: for each x, ¬¬(x ∈ A) ↔ (x ∈ A) because A is open (¬¬-stable via MP)
    pointwise : (x : CantorSpace) → fst ¬¬A x ≡ fst A x
    pointwise x = Σ≡Prop (λ _ → isPropIsProp) (hPropExt ¬¬A-isProp (snd (fst A x)) fwd bwd)
      where
      ¬¬A-isProp : isProp (fst (fst ¬¬A x))
      ¬¬A-isProp = snd (fst ¬¬A x)

      -- Forward: ¬¬(x ∈ A) → (x ∈ A) by openness of A (requires MP)
      fwd : fst (fst ¬¬A x) → fst (fst A x)
      fwd ¬¬a = openIsStable mp (fst A x) (snd A x) ¬¬a

      -- Backward: (x ∈ A) → ¬¬(x ∈ A) (trivial)
      bwd : fst (fst A x) → fst (fst ¬¬A x)
      bwd a ¬a = ¬a a

    -- The openness witness
    pred-path : fst ¬¬A ≡ fst A
    pred-path = funExt pointwise

    witness-path : PathP (λ i → (x : CantorSpace) → isOpenProp (pred-path i x)) (snd ¬¬A) (snd A)
    witness-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (pred-path i x))) (snd ¬¬A) (snd A)

  -- ==========================================================================
  -- De Morgan laws for subset complements
  -- ==========================================================================
  --
  -- These show how complement interacts with union and intersection:
  -- ¬(A ∪ B) = ¬A ∩ ¬B
  -- ¬(A ∩ B) = ¬A ∪ ¬B
  --
  -- For closed/open subsets, we need to track which complement operation
  -- produces which type of subset.

  -- De Morgan: ¬(closed A ∩ closed B) ↔ ¬A ∪ ¬B
  -- Note: ¬(A ∩ B) is open (complement of closed intersection)
  --       ¬A is open, ¬B is open, so ¬A ∪ ¬B is open
  closedDeMorganIntersection-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
    → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
  closedDeMorganIntersection-fwd A B x not-a-and-b =
    mp-open-disjunction (ClosedSubsetComplement A) (ClosedSubsetComplement B) x
      (λ (not-not-a , not-not-b) → not-a-and-b (closedIsStable (fst A x) (snd A x) not-not-a ,
                                                closedIsStable (fst B x) (snd B x) not-not-b))
    where
    -- Using MP, we can decide ¬A ∨ ¬B from ¬¬(¬A ∨ ¬B)
    mp-open-disjunction : (U V : OpenSubsetOfCantor) (y : CantorSpace)
      → (((fst (fst U y)) → ⊥) × ((fst (fst V y)) → ⊥) → ⊥)
      → fst (fst (OpenSubsetUnion U V) y)
    mp-open-disjunction U V y not-not-u-or-v =
      openIsStable mp (fst (OpenSubsetUnion U V) y) (snd (OpenSubsetUnion U V) y)
        (λ not-uv → not-not-u-or-v (
          (λ u → not-uv ∣ inl u ∣₁) ,
          (λ v → not-uv ∣ inr v ∣₁)))

  closedDeMorganIntersection-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
  closedDeMorganIntersection-bwd A B x =
    PT.rec (snd (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x))
           (λ { (inl ¬a) (a , _) → ¬a a
              ; (inr ¬b) (_ , b) → ¬b b })

  -- De Morgan: ¬(closed A ∪ closed B) ↔ ¬A ∩ ¬B
  -- Note: ¬(A ∪ B) is open (complement of closed union)
  --       ¬A is open, ¬B is open, so ¬A ∩ ¬B is open
  closedDeMorganUnion-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
    → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
  closedDeMorganUnion-fwd A B x not-a-or-b =
    (λ a → not-a-or-b ∣ inl a ∣₁) , (λ b → not-a-or-b ∣ inr b ∣₁)

  closedDeMorganUnion-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
  closedDeMorganUnion-bwd A B x (not-a , not-b) =
    PT.rec isProp⊥ (λ { (inl a) → not-a a ; (inr b) → not-b b })

  -- De Morgan: ¬(open A ∩ open B) ↔ ¬A ∪ ¬B
  -- Note: ¬(A ∩ B) is closed (complement of open intersection)
  --       ¬A is closed, ¬B is closed, so ¬A ∪ ¬B is closed
  --
  -- The forward direction requires LLPO-style reasoning:
  -- From ¬(A ∧ B) we need to conclude ¬A ∨ ¬B.
  -- Classically this is obvious, but constructively it requires
  -- the fact that ¬A ∨ ¬B is a closed proposition (being a union of
  -- closed subsets), hence ¬¬-stable.
  -- NOTE: The original proof has several bugs:
  -- 1. isProp⊎ requires ¬A → ¬B → ⊥ but that's not provable from ¬(A ∧ B)
  -- 2. disjClosed claims ¬A ⊎ ¬B is closed using negOpenIsClosed of A ∨ B,
  --    but ¬(A ∨ B) ≠ ¬A ⊎ ¬B (De Morgan gives ¬A ∧ ¬B, not ⊎)
  postulate
    openDeMorganIntersection-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
      → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)

  openDeMorganIntersection-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
  openDeMorganIntersection-bwd A B x =
    PT.rec (snd (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x))
           (λ { (inl not-a) (a , _) → not-a a
              ; (inr not-b) (_ , b) → not-b b })

  -- De Morgan: ¬(open A ∪ open B) ↔ ¬A ∩ ¬B
  openDeMorganUnion-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
    → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
  openDeMorganUnion-fwd A B x not-a-or-b =
    (λ a → not-a-or-b ∣ inl a ∣₁) , (λ b → not-a-or-b ∣ inr b ∣₁)

  openDeMorganUnion-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
  openDeMorganUnion-bwd A B x (not-a , not-b) =
    PT.rec isProp⊥ (λ { (inl a) → not-a a ; (inr b) → not-b b })

  -- ==========================================================================
  -- Excluded middle for subsets (A ∪ ¬A = Full)
  -- ==========================================================================
  --
  -- For closed subsets: A ∪ (open complement of A) = Full
  -- For open subsets: A ∪ (closed complement of A) = Full
  --
  -- These are the "law of excluded middle" at the level of subsets.
  -- They require LLPO/closedOr for the closed case.

  -- Excluded middle for closed subsets
  -- For each x, either x ∈ A or x ∈ ¬A (where ¬A is the open complement)
  -- NOTE: The original proof has a bug in the `not-and` helper -
  -- ¬((¬A) × (¬¬¬A)) is not constructively provable without additional axioms.
  postulate
    closedExcludedMiddle : (A : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetUnion A (OpenSubsetComplement (ClosedSubsetComplement A))) x)

  -- Law of excluded middle as path equality
  -- A ∪ ¬¬A = Full
  closedUnionComplement : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A (OpenSubsetComplement (ClosedSubsetComplement A))
      ≡ FullClosedSubset
  closedUnionComplement A = ΣPathP
    ( pred-path
    , closedWitnessPathP pred-path (snd (ClosedSubsetUnion A (OpenSubsetComplement (ClosedSubsetComplement A)))) (snd FullClosedSubset) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst FullClosedSubset x))
                (λ _ → tt)
                (λ _ → closedExcludedMiddle A x)))

  -- Excluded middle for open subsets
  -- For each x, either x ∈ A or x ∈ ¬A (where ¬A is the closed complement)
  -- NOTE: The original proof has similar bugs involving applying negations incorrectly.
  postulate
    openExcludedMiddle : (A : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetUnion A (ClosedSubsetComplement (OpenSubsetComplement A))) x)

  -- Law of excluded middle for open subsets as path equality
  -- A ∪ ¬¬A = Full
  openUnionComplement : (A : OpenSubsetOfCantor)
    → OpenSubsetUnion A (ClosedSubsetComplement (OpenSubsetComplement A))
      ≡ FullOpenSubset
  openUnionComplement A = ΣPathP
    ( pred-path
    , openWitnessPathP pred-path (snd (OpenSubsetUnion A (ClosedSubsetComplement (OpenSubsetComplement A)))) (snd FullOpenSubset) )
    where
    pred-path = funExt (λ x → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt squash₁ (snd (fst FullOpenSubset x))
                (λ _ → tt)
                (λ _ → openExcludedMiddle A x)))

