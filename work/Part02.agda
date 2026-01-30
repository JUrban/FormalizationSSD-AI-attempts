{-# OPTIONS --cubical --guardedness #-}

module work.Part02 where

-- =============================================================================
-- Part 02: Minimal stub to verify module splitting works
-- =============================================================================

-- Import Part01 for base definitions
open import work.Part01 public

-- Import core types from Prelude and CommRing (needed for type signatures)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Algebra.CommRing
open import Axioms.StoneDuality using (Sp; Booleω)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)

-- Additional imports needed for this part
-- Note: Bool-Booleω, Sp, Booleω come from Part01 via public re-export
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
open import CountablyPresentedBooleanRings.PresentedBoole using (isPropIsBoolRingHom)
open import BooleanRing.BoolRingUnivalence using (IsBoolRingHom)

-- Re-export key types for use by downstream modules
BoolHom' : {ℓ ℓ' : Level} → BooleanRing ℓ → BooleanRing ℓ' → Type (ℓ-max ℓ ℓ')
BoolHom' A B = CommRingHom (BooleanRing→CommRing A) (BooleanRing→CommRing B)

-- =============================================================================
-- Sp-Bool results (lines 700-755 from work.agda)
-- =============================================================================

-- The identity Boolean ring homomorphism on BoolBR
private
  idBoolHom : BoolHom BoolBR BoolBR
  fst idBoolHom = idfun Bool
  snd idBoolHom .IsCommRingHom.pres0 = refl
  snd idBoolHom .IsCommRingHom.pres1 = refl
  snd idBoolHom .IsCommRingHom.pres+ _ _ = refl
  snd idBoolHom .IsCommRingHom.pres· _ _ = refl
  snd idBoolHom .IsCommRingHom.pres- _ = refl

-- Sp(Bool-Booleω) is inhabited - the spectrum is non-empty
Sp-Bool-inhabited : ∥ Sp Bool-Booleω ∥₁
Sp-Bool-inhabited = ∣ idBoolHom ∣₁

-- Sp(BoolBR) is contractible: there is exactly one Boolean ring homomorphism BoolBR → BoolBR
Sp-Bool-isContr : isContr (Sp Bool-Booleω)
Sp-Bool-isContr = idBoolHom , path-to-id
  where
  -- IsCommRingHom is a proposition
  isProp-IsCommRingHom : (f : Bool → Bool) → isProp (IsCommRingHom (BooleanRing→CommRing BoolBR .snd) f (BooleanRing→CommRing BoolBR .snd))
  isProp-IsCommRingHom f = isPropIsCommRingHom (snd (BooleanRing→CommRing BoolBR)) f (snd (BooleanRing→CommRing BoolBR))

  -- Any Boolean ring hom h : BoolBR → BoolBR equals the identity
  path-to-id : (h : Sp Bool-Booleω) → idBoolHom ≡ h
  path-to-id h = Σ≡Prop isProp-IsCommRingHom funEq
    where
    open IsCommRingHom (snd h)

    -- h must preserve 1: h(true) = true
    h-true : fst h true ≡ true
    h-true = pres1

    -- For false: h(false) = h(true + true) = h(true) + h(true) = true + true = false
    -- In BoolBR, true + true = false (xor operation: _⊕_)
    h-false : fst h false ≡ false
    h-false = sym (
      true ⊕ true   ≡⟨ refl ⟩
      false         ≡⟨ sym (cong₂ _⊕_ h-true h-true) ⟩
      fst h true ⊕ fst h true ≡⟨ sym (pres+ true true) ⟩
      fst h (true ⊕ true)     ≡⟨ refl ⟩
      fst h false ∎)

    funEq : idfun Bool ≡ fst h
    funEq = funExt λ { false → sym h-false ; true → sym h-true }

-- =============================================================================
-- Stub: More content will be added as we verify each piece compiles
-- =============================================================================

-- Note: quotientPreservesBooleω and mp-derivation modules have complex
-- dependencies that require careful import management. They will be added
-- in subsequent iterations after verifying this base compiles.
