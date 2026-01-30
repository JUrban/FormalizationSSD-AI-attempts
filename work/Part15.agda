{-# OPTIONS --cubical --guardedness #-}

module work.Part15 where

-- =============================================================================
-- Part 15: quotientBySeqPreservesBooleω (work.agda lines 10800-11272)
-- =============================================================================

-- Import Part14 for previous definitions
open import work.Part14 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso; invIso; isoToPath)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; invEq; secEq; retEq; equivToIso; invEquiv; equivFun)
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
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom; invBooleanRingEquiv)
open import BooleanRing.BoolRingUnivalence using (BoolRingPath)

-- Note: compBoolRingEquiv, commRingPath→boolRingEquiv are already re-exported from Part11
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp; isSetBoolHom; StoneDualityAxiom; SDHomVersion; evaluationMap)

-- =============================================================================
-- Continuation of StoneClosedSubsetsModule with quotientBySeqPreservesBooleω
-- =============================================================================

module StoneClosedSubsetsModuleCont where
  open SDDecToElemModule
  open StoneEqualityClosedModule
  open StoneClosedSubsetsModule
  open SpOfQuotientBySeq

  -- =============================================================================
  -- The main lemma: quotient by sequence preserves Booleω
  -- PROOF: Use PT.rec to eliminate the truncated presentation of B,
  -- then construct the presentation of B/d using the helper module.
  -- =============================================================================

  quotientBySeqPreservesBooleω : (B : Booleω) (d : ℕ → ⟨ fst B ⟩)
    → ∥ Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))) ∥₁
  quotientBySeqPreservesBooleω B d = PT.rec squash₁ construct (snd B)
    where
    -- The quotient ring (renamed to avoid clash with Part14's B/d)
    B/d-outer : BooleanRing ℓ-zero
    B/d-outer = fst B QB./Im d

    -- Given an untruncated presentation, construct the witness
    -- Using countableChoice to get uniform lifts
    construct : has-Boole-ω' (fst B) →
                ∥ Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))) ∥₁
    construct (f , equiv) = PT.rec squash₁ (λ lifts → ∣ constructFromLifts lifts ∣₁) lifts-exist
      where
      -- Open the helper module for Sp equivalence (with alias to avoid ambiguity)
      module SPQ = SpOfQuotientBySeq (fst B) d
      open SPQ

      -- The quotient ring B/d
      B/d-ring : BooleanRing ℓ-zero
      B/d-ring = fst B QB./Im d

      -- Step 1: Transport d through equiv to get d' : ℕ → ⟨ freeBA ℕ /Im f ⟩
      d' : ℕ → ⟨ freeBA ℕ QB./Im f ⟩
      d' n = fst (fst equiv) (d n)

      -- The quotient map π-f
      π-f : ⟨ freeBA ℕ ⟩ → ⟨ freeBA ℕ QB./Im f ⟩
      π-f = fst QB.quotientImageHom

      -- Step 2: For each n, d'(n) has a preimage (by surjectivity of quotient map)
      d'-has-preimage : (n : ℕ) → ∥ Σ[ x ∈ ⟨ freeBA ℕ ⟩ ] π-f x ≡ d' n ∥₁
      d'-has-preimage n = QB.quotientImageHomSurjective (d' n)

      -- Step 3: Use countableChoice to get uniform lifts
      LiftType : ℕ → Type ℓ-zero
      LiftType n = Σ[ x ∈ ⟨ freeBA ℕ ⟩ ] π-f x ≡ d' n

      lifts-exist : ∥ ((n : ℕ) → LiftType n) ∥₁
      lifts-exist = countableChoice LiftType d'-has-preimage

      -- Step 4: Given uniform lifts, construct the presentation
      constructFromLifts : ((n : ℕ) → LiftType n) →
                           Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
      constructFromLifts lifts = C , Sp-equiv
        where
        -- Extract the lift function and the proof that it's a section
        g : ℕ → ⟨ freeBA ℕ ⟩
        g n = fst (lifts n)

        g-is-section : (n : ℕ) → π-f (g n) ≡ d' n
        g-is-section n = snd (lifts n)

        -- Now we can construct the presentation following quotientPreservesBooleω pattern

        -- Using ℕ⊎ℕ≅ℕ to combine f and g
        encode : ℕ ⊎ ℕ → ℕ
        encode = Iso.fun ℕ⊎ℕ≅ℕ

        decode : ℕ → ℕ ⊎ ℕ
        decode = Iso.inv ℕ⊎ℕ≅ℕ

        -- The combined presentation function
        h : ℕ → ⟨ freeBA ℕ ⟩
        h n with decode n
        ... | inl m = f m    -- relations from the original presentation
        ... | inr m = g m    -- relations from d' (via lifts)

        -- Step 2: BoolQuotientEquiv gives us path between quotients
        step2-path : BooleanRing→CommRing (freeBA ℕ QB./Im (⊎.rec f g)) ≡
                     BooleanRing→CommRing ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
        step2-path = BoolQuotientEquiv (freeBA ℕ) f g

        step2-equiv : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g))
                                       ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
        step2-equiv = commRingPath→boolRingEquiv
                        (freeBA ℕ QB./Im (⊎.rec f g))
                        ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
                        step2-path

        -- Step 3: h ≡ (⊎.rec f g) ∘ decode (same pattern as quotientPreservesBooleω)
        h≡rec∘decode-pointwise : (n : ℕ) → h n ≡ ⊎.rec f g (decode n)
        h≡rec∘decode-pointwise n with decode n
        ... | inl m = refl
        ... | inr m = refl

        h≡rec∘decode : h ≡ (⊎.rec f g) ∘ decode
        h≡rec∘decode = funExt h≡rec∘decode-pointwise

        rec-of-decode : (n : ℕ) → ⊎.rec f g (decode n) ≡ h n
        rec-of-decode n = sym (h≡rec∘decode-pointwise n)

        encode∘decode : (n : ℕ) → encode (decode n) ≡ n
        encode∘decode = Iso.sec ℕ⊎ℕ≅ℕ

        decode∘encode : (x : ℕ ⊎ ℕ) → decode (encode x) ≡ x
        decode∘encode = Iso.ret ℕ⊎ℕ≅ℕ

        -- Quotient rings
        rec-quotient : BooleanRing ℓ-zero
        rec-quotient = freeBA ℕ QB./Im (⊎.rec f g)

        h-quotient : BooleanRing ℓ-zero
        h-quotient = freeBA ℕ QB./Im h

        -- Quotient maps
        π-rec : BoolHom (freeBA ℕ) rec-quotient
        π-rec = QB.quotientImageHom

        π-h : BoolHom (freeBA ℕ) h-quotient
        π-h = QB.quotientImageHom

        -- Forward: π-rec sends h n to 0
        π-rec-sends-h-to-0 : (n : ℕ) → π-rec $cr (h n) ≡ BooleanRingStr.𝟘 (snd rec-quotient)
        π-rec-sends-h-to-0 n =
          π-rec $cr (h n)
            ≡⟨ cong (π-rec $cr_) (sym (rec-of-decode n)) ⟩
          π-rec $cr ((⊎.rec f g) (decode n))
            ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = ⊎.rec f g} (decode n) ⟩
          BooleanRingStr.𝟘 (snd rec-quotient) ∎

        step3-forward-hom : BoolHom h-quotient rec-quotient
        step3-forward-hom = QB.inducedHom {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

        -- Backward: π-h sends (⊎.rec f g) x to 0
        rec-eq-h-encode : (x : ℕ ⊎ ℕ) → (⊎.rec f g) x ≡ h (encode x)
        rec-eq-h-encode x =
          (⊎.rec f g) x
            ≡⟨ cong (⊎.rec f g) (sym (decode∘encode x)) ⟩
          (⊎.rec f g) (decode (encode x))
            ≡⟨ rec-of-decode (encode x) ⟩
          h (encode x) ∎

        π-h-sends-rec-to-0 : (x : ℕ ⊎ ℕ) → π-h $cr ((⊎.rec f g) x) ≡ BooleanRingStr.𝟘 (snd h-quotient)
        π-h-sends-rec-to-0 x =
          π-h $cr ((⊎.rec f g) x)
            ≡⟨ cong (π-h $cr_) (rec-eq-h-encode x) ⟩
          π-h $cr (h (encode x))
            ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = h} (encode x) ⟩
          BooleanRingStr.𝟘 (snd h-quotient) ∎

        step3-backward-hom : BoolHom rec-quotient h-quotient
        step3-backward-hom = QB.inducedHom {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient π-h π-h-sends-rec-to-0

        step3-forward : ⟨ h-quotient ⟩ → ⟨ rec-quotient ⟩
        step3-forward = fst step3-forward-hom

        step3-backward : ⟨ rec-quotient ⟩ → ⟨ h-quotient ⟩
        step3-backward = fst step3-backward-hom

        -- Eval properties
        step3-forward-eval : step3-forward-hom ∘cr π-h ≡ π-rec
        step3-forward-eval = QB.evalInduce {B = freeBA ℕ} {f = h} rec-quotient {π-rec} {π-rec-sends-h-to-0}

        step3-backward-eval : step3-backward-hom ∘cr π-rec ≡ π-h
        step3-backward-eval = QB.evalInduce {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient {π-h} {π-h-sends-rec-to-0}

        -- isSet properties
        h-quotient-isSet : isSet ⟨ h-quotient ⟩
        h-quotient-isSet = BooleanRingStr.is-set (snd h-quotient)

        rec-quotient-isSet : isSet ⟨ rec-quotient ⟩
        rec-quotient-isSet = BooleanRingStr.is-set (snd rec-quotient)

        -- Round-trips
        step3-backward∘forward-on-π : (x : ⟨ freeBA ℕ ⟩) → step3-backward (step3-forward (fst π-h x)) ≡ fst π-h x
        step3-backward∘forward-on-π x =
          step3-backward (step3-forward (fst π-h x))
            ≡⟨ cong step3-backward (cong (λ hom → fst hom x) step3-forward-eval) ⟩
          step3-backward (fst π-rec x)
            ≡⟨ cong (λ hom → fst hom x) step3-backward-eval ⟩
          fst π-h x ∎

        step3-backward∘forward-ext : (step3-backward ∘ step3-forward) ∘ fst π-h ≡ (λ x → x) ∘ fst π-h
        step3-backward∘forward-ext = funExt step3-backward∘forward-on-π

        step3-backward∘forward : (x : ⟨ h-quotient ⟩) → step3-backward (step3-forward x) ≡ x
        step3-backward∘forward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = h}
                                           (⟨ h-quotient ⟩ , h-quotient-isSet) step3-backward∘forward-ext)

        step3-forward∘backward-on-π : (y : ⟨ freeBA ℕ ⟩) → step3-forward (step3-backward (fst π-rec y)) ≡ fst π-rec y
        step3-forward∘backward-on-π y =
          step3-forward (step3-backward (fst π-rec y))
            ≡⟨ cong step3-forward (cong (λ hom → fst hom y) step3-backward-eval) ⟩
          step3-forward (fst π-h y)
            ≡⟨ cong (λ hom → fst hom y) step3-forward-eval ⟩
          fst π-rec y ∎

        step3-forward∘backward-ext : (step3-forward ∘ step3-backward) ∘ fst π-rec ≡ (λ y → y) ∘ fst π-rec
        step3-forward∘backward-ext = funExt step3-forward∘backward-on-π

        step3-forward∘backward : (y : ⟨ rec-quotient ⟩) → step3-forward (step3-backward y) ≡ y
        step3-forward∘backward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = ⊎.rec f g}
                                           (⟨ rec-quotient ⟩ , rec-quotient-isSet) step3-forward∘backward-ext)

        -- Step 3 iso
        step3-iso : Iso ⟨ h-quotient ⟩ ⟨ rec-quotient ⟩
        Iso.fun step3-iso = step3-forward
        Iso.inv step3-iso = step3-backward
        Iso.sec step3-iso = step3-forward∘backward
        Iso.ret step3-iso = step3-backward∘forward

        step3-equiv-fun : ⟨ h-quotient ⟩ ≃ ⟨ rec-quotient ⟩
        step3-equiv-fun = isoToEquiv step3-iso

        step3-equiv' : BooleanRingEquiv h-quotient rec-quotient
        step3-equiv' = step3-equiv-fun , snd step3-forward-hom

        step3-h-eq : freeBA ℕ QB./Im h ≡ freeBA ℕ QB./Im (⊎.rec f g)
        step3-h-eq = equivFun (BoolRingPath h-quotient rec-quotient) step3-equiv'

        step3-equiv : BooleanRingEquiv (freeBA ℕ QB./Im h) (freeBA ℕ QB./Im (⊎.rec f g))
        step3-equiv = invEq (BoolRingPath _ _) step3-h-eq

        -- Now Step 1: B/d-ring ≃ (freeBA ℕ /Im f) /Im d'
        -- This is similar to the step1 in quotientPreservesBooleω but using equiv instead of BoolBR
        -- We need to transport the quotient structure through equiv

        -- The target quotient ring
        target-ring : BooleanRing ℓ-zero
        target-ring = (freeBA ℕ QB./Im f) QB./Im d'

        -- embBR-hom equivalent: equiv as a BoolHom
        equiv-hom : BoolHom (fst B) (freeBA ℕ QB./Im f)
        equiv-hom = fst (fst equiv) , snd equiv

        -- Quotient map to target
        π-d' : BoolHom (freeBA ℕ QB./Im f) target-ring
        π-d' = QB.quotientImageHom

        -- Composite: π-d' ∘ equiv : (fst B) → target-ring
        -- This sends d n to 0 because d' n = equiv (d n), and d' n is 0 in target-ring
        composite-hom-1 : BoolHom (fst B) target-ring
        composite-hom-1 = π-d' ∘cr equiv-hom

        composite-sends-d-to-0 : (n : ℕ) → composite-hom-1 $cr (d n) ≡ BooleanRingStr.𝟘 (snd target-ring)
        composite-sends-d-to-0 n = QB.zeroOnImage {f = d'} n

        -- Induced hom: B/d-ring → target-ring
        step1-forward-hom : BoolHom B/d-ring target-ring
        step1-forward-hom = QB.inducedHom target-ring composite-hom-1 composite-sends-d-to-0

        -- Backward: equiv⁻¹ then quotient by d
        -- π_d : (fst B) → B/d-ring
        π-d : BoolHom (fst B) B/d-ring
        π-d = QB.quotientImageHom

        -- equiv⁻¹ as BoolHom
        equiv⁻¹-hom : BoolHom (freeBA ℕ QB./Im f) (fst B)
        equiv⁻¹-hom = fst (fst (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)) ,
                      snd (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)

        -- Composite backward: π-d ∘ equiv⁻¹
        backward-composite-1 : BoolHom (freeBA ℕ QB./Im f) B/d-ring
        backward-composite-1 = π-d ∘cr equiv⁻¹-hom

        -- This sends d' n to 0: d' n = equiv (d n), so equiv⁻¹ (d' n) = d n, and π-d (d n) = 0
        backward-composite-sends-d'-to-0 : (n : ℕ) → backward-composite-1 $cr (d' n) ≡ BooleanRingStr.𝟘 (snd B/d-ring)
        backward-composite-sends-d'-to-0 n =
          backward-composite-1 $cr (d' n)
            ≡⟨ refl ⟩
          π-d $cr (equiv⁻¹-hom $cr (fst (fst equiv) (d n)))
            ≡⟨ cong (π-d $cr_) (Iso.ret (equivToIso (fst equiv)) (d n)) ⟩
          π-d $cr (d n)
            ≡⟨ QB.zeroOnImage {f = d} n ⟩
          BooleanRingStr.𝟘 (snd B/d-ring) ∎

        -- Induced hom: target-ring → B/d-ring
        step1-backward-hom : BoolHom target-ring B/d-ring
        step1-backward-hom = QB.inducedHom B/d-ring backward-composite-1 backward-composite-sends-d'-to-0

        step1-forward-fun : ⟨ B/d-ring ⟩ → ⟨ target-ring ⟩
        step1-forward-fun = fst step1-forward-hom

        step1-backward-fun : ⟨ target-ring ⟩ → ⟨ B/d-ring ⟩
        step1-backward-fun = fst step1-backward-hom

        -- eval properties for step1
        step1-forward-eval : step1-forward-hom ∘cr π-d ≡ composite-hom-1
        step1-forward-eval = QB.evalInduce {B = fst B} {f = d} target-ring {composite-hom-1} {composite-sends-d-to-0}

        step1-backward-eval : step1-backward-hom ∘cr π-d' ≡ backward-composite-1
        step1-backward-eval = QB.evalInduce {B = freeBA ℕ QB./Im f} {f = d'} B/d-ring
                                {backward-composite-1} {backward-composite-sends-d'-to-0}

        -- Retract: equiv⁻¹ ∘ equiv = id
        equiv⁻¹∘equiv≡id : (x : ⟨ fst B ⟩) → fst equiv⁻¹-hom (fst (fst equiv) x) ≡ x
        equiv⁻¹∘equiv≡id = Iso.ret (equivToIso (fst equiv))

        -- Section: equiv ∘ equiv⁻¹ = id
        equiv∘equiv⁻¹≡id : (y : ⟨ freeBA ℕ QB./Im f ⟩) → fst (fst equiv) (fst equiv⁻¹-hom y) ≡ y
        equiv∘equiv⁻¹≡id = Iso.sec (equivToIso (fst equiv))

        -- isSet for step1
        B/d-ring-isSet : isSet ⟨ B/d-ring ⟩
        B/d-ring-isSet = BooleanRingStr.is-set (snd B/d-ring)

        target-ring-isSet : isSet ⟨ target-ring ⟩
        target-ring-isSet = BooleanRingStr.is-set (snd target-ring)

        -- Round-trips for step1
        step1-backward∘forward-on-π : (x : ⟨ fst B ⟩) → step1-backward-fun (step1-forward-fun (fst π-d x)) ≡ fst π-d x
        step1-backward∘forward-on-π x =
          step1-backward-fun (step1-forward-fun (fst π-d x))
            ≡⟨ cong step1-backward-fun (cong (λ hom → fst hom x) step1-forward-eval) ⟩
          step1-backward-fun (fst composite-hom-1 x)
            ≡⟨ refl ⟩
          step1-backward-fun (fst π-d' (fst (fst equiv) x))
            ≡⟨ cong (λ hom → fst hom (fst (fst equiv) x)) step1-backward-eval ⟩
          fst backward-composite-1 (fst (fst equiv) x)
            ≡⟨ refl ⟩
          fst π-d (fst equiv⁻¹-hom (fst (fst equiv) x))
            ≡⟨ cong (fst π-d) (equiv⁻¹∘equiv≡id x) ⟩
          fst π-d x ∎

        step1-backward∘forward-ext : (step1-backward-fun ∘ step1-forward-fun) ∘ fst π-d ≡ (λ x → x) ∘ fst π-d
        step1-backward∘forward-ext = funExt step1-backward∘forward-on-π

        step1-backward∘forward : (x : ⟨ B/d-ring ⟩) → step1-backward-fun (step1-forward-fun x) ≡ x
        step1-backward∘forward = funExt⁻ (QB.quotientImageHomEpi {B = fst B} {f = d}
                                           (⟨ B/d-ring ⟩ , B/d-ring-isSet) step1-backward∘forward-ext)

        step1-forward∘backward-on-π : (y : ⟨ freeBA ℕ QB./Im f ⟩) →
                                       step1-forward-fun (step1-backward-fun (fst π-d' y)) ≡ fst π-d' y
        step1-forward∘backward-on-π y =
          step1-forward-fun (step1-backward-fun (fst π-d' y))
            ≡⟨ cong step1-forward-fun (cong (λ hom → fst hom y) step1-backward-eval) ⟩
          step1-forward-fun (fst backward-composite-1 y)
            ≡⟨ refl ⟩
          step1-forward-fun (fst π-d (fst equiv⁻¹-hom y))
            ≡⟨ cong (λ hom → fst hom (fst equiv⁻¹-hom y)) step1-forward-eval ⟩
          fst composite-hom-1 (fst equiv⁻¹-hom y)
            ≡⟨ refl ⟩
          fst π-d' (fst (fst equiv) (fst equiv⁻¹-hom y))
            ≡⟨ cong (fst π-d') (equiv∘equiv⁻¹≡id y) ⟩
          fst π-d' y ∎

        step1-forward∘backward-ext : (step1-forward-fun ∘ step1-backward-fun) ∘ fst π-d' ≡ (λ y → y) ∘ fst π-d'
        step1-forward∘backward-ext = funExt step1-forward∘backward-on-π

        step1-forward∘backward : (y : ⟨ target-ring ⟩) → step1-forward-fun (step1-backward-fun y) ≡ y
        step1-forward∘backward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ QB./Im f} {f = d'}
                                           (⟨ target-ring ⟩ , target-ring-isSet) step1-forward∘backward-ext)

        -- Step 1 iso
        step1-iso : Iso ⟨ B/d-ring ⟩ ⟨ target-ring ⟩
        Iso.fun step1-iso = step1-forward-fun
        Iso.inv step1-iso = step1-backward-fun
        Iso.sec step1-iso = step1-forward∘backward
        Iso.ret step1-iso = step1-backward∘forward

        step1-equiv-fun : ⟨ B/d-ring ⟩ ≃ ⟨ target-ring ⟩
        step1-equiv-fun = isoToEquiv step1-iso

        step1-equiv : BooleanRingEquiv B/d-ring target-ring
        step1-equiv = step1-equiv-fun , snd step1-forward-hom

        -- Now we need to show d' = π-f ∘ g (pointwise)
        -- We have g-is-section : (n : ℕ) → π-f (g n) ≡ d' n
        -- But wait, π-f here is fst QB.quotientImageHom for freeBA ℕ → freeBA ℕ /Im f
        -- which is the same as fst QB.quotientImageHom ∘ g used in step2-equiv
        open IsCommRingHom

        d'≡π-f∘g-pointwise : (n : ℕ) → d' n ≡ fst QB.quotientImageHom (g n)
        d'≡π-f∘g-pointwise n = sym (g-is-section n)

        d'≡π-f∘g : d' ≡ fst QB.quotientImageHom ∘ g
        d'≡π-f∘g = funExt d'≡π-f∘g-pointwise

        -- Transport step1-equiv along d' = π-f ∘ g
        step1-equiv' : BooleanRingEquiv B/d-ring ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
        step1-equiv' = subst (λ seq → BooleanRingEquiv B/d-ring ((freeBA ℕ QB./Im f) QB./Im seq))
                         d'≡π-f∘g step1-equiv

        -- Now combine: B/d-ring → target' → rec-quotient → h-quotient
        -- Intermediate types
        A'-seq : BooleanRing ℓ-zero
        A'-seq = B/d-ring

        B'-seq : BooleanRing ℓ-zero
        B'-seq = (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)

        C'-seq : BooleanRing ℓ-zero
        C'-seq = freeBA ℕ QB./Im (⊎.rec f g)

        D'-seq : BooleanRing ℓ-zero
        D'-seq = freeBA ℕ QB./Im h

        -- inv step2: B'-seq → C'-seq
        invStep2-seq : BooleanRingEquiv B'-seq C'-seq
        invStep2-seq = invBooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g))
                                            ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
                                            step2-equiv

        -- inv step3: C'-seq → D'-seq
        invStep3-seq : BooleanRingEquiv C'-seq D'-seq
        invStep3-seq = invBooleanRingEquiv (freeBA ℕ QB./Im h)
                                            (freeBA ℕ QB./Im (⊎.rec f g))
                                            step3-equiv

        -- Compose: A'-seq → B'-seq → C'-seq → D'-seq
        step12-seq : BooleanRingEquiv A'-seq C'-seq
        step12-seq = compBoolRingEquiv A'-seq B'-seq C'-seq step1-equiv' invStep2-seq

        B/d-equiv : BooleanRingEquiv B/d-ring (freeBA ℕ QB./Im h)
        B/d-equiv = compBoolRingEquiv A'-seq C'-seq D'-seq step12-seq invStep3-seq

        -- Now the presentation is complete
        B/d-presentation : has-Boole-ω' B/d-ring
        B/d-presentation = h , B/d-equiv

        -- The Booleω
        C : Booleω
        C = B/d-ring , ∣ B/d-presentation ∣₁

        -- The Sp equivalence from SpOfQuotientBySeq
        Sp-equiv : Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))
        Sp-equiv = SPQ.Sp-quotient-≃

  -- =============================================================================
  -- Image characterization: closed subsets of Stone spaces are images of Stone maps
  -- This is direction (v) → (iv) from the theorem.
  -- Requires LocalChoice axiom.
  -- =============================================================================
  postulate
    closedSubset→StoneImage : (S : Stone) (A : fst S → hProp ℓ-zero)
      → ((x : fst S) → isClosedProp (A x))
      → ∥ Σ[ T ∈ Stone ] Σ[ f ∈ (fst T → fst S) ]
          ((x : fst S) → fst (A x) ≃ ∥ Σ[ t ∈ fst T ] f t ≡ x ∥₁) ∥₁

  -- Combined: ClosedInStoneIsStone follows from the equivalences
  -- A closed ⊆ S is Stone because:
  -- (v) A closed → (iv) A is image of T : Stone → (ii) A = ⋂Dₙ → (iii) A ≃ Sp(B/dₙ)

open StoneClosedSubsetsModuleCont public
