{-# OPTIONS --cubical --guardedness #-}

module work.Part11 where

-- =============================================================================
-- Part 11: normalizeTerm, surjectivity proofs, f-kernel, and ClosedPropAsSpectrum
--          (lines 8500-9500 of work.agda)
-- =============================================================================

-- Import Part10 for previous definitions
open import work.Part10 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; compEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ; isPropIsCommRingHom)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; inj-m+; +-zero; injSuc; snotz; znots)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; idBoolEquiv; has-Countability-structure; idBoolHom)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp)
open import BooleanRing.FreeBooleanRing.SurjectiveTerms using (TermsOf_[_]; Tvar; Tconst; _+T_; -T_; _·T_; includeTerm)
open import BooleanRing.FreeBooleanRing.freeBATerms using (freeBATerms; includeBATermsSurj; equalityFromEqualityOnGenerators;
  includeBATerms-Tvar; includeBATerms-+; includeBATerms-·; includeBATerms--; includeBATerms-0; includeBATerms-1)
open import Cubical.Functions.Surjection using (isSurjection; compSurjection; _↠_)

-- Open BooleanRingStr for B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; _+_ to _+×_)

-- _+∞_ and -∞ needed locally
open BooleanRingStr (snd B∞) using () renaming (_+_ to _+∞_ ; -_ to -∞_)

-- =============================================================================
-- normalizeTerm function (lines 8485-8505)
-- =============================================================================

-- Normalize a term to a normal form
normalizeTerm : freeBATerms ℕ → B∞-NormalForm
normalizeTerm (Tvar n) = joinForm (n ∷ [])
normalizeTerm (Tconst false) = joinForm []
normalizeTerm (Tconst true) = meetNegForm []
normalizeTerm (t +T s) = xor-nf (normalizeTerm t) (normalizeTerm s)
normalizeTerm (-T t) = normalizeTerm t
normalizeTerm (t ·T s) = meet-nf (normalizeTerm t) (normalizeTerm s)

-- =============================================================================
-- normalizeTerm correctness proof (lines 8507-8600)
-- =============================================================================

-- Direct interpretation into B∞
interpretB∞ : freeBATerms ℕ → ⟨ B∞ ⟩
interpretB∞ (Tvar n) = g∞ n
interpretB∞ (Tconst false) = 𝟘∞
interpretB∞ (Tconst true) = 𝟙∞
interpretB∞ (t +T s) = interpretB∞ t +∞ interpretB∞ s
interpretB∞ (-T t) = -∞ interpretB∞ t
interpretB∞ (t ·T s) = interpretB∞ t ·∞ interpretB∞ s

-- Negation is identity in Boolean rings
negation-is-id-B∞ : (x : ⟨ B∞ ⟩) → -∞ x ≡ x
negation-is-id-B∞ x =
  -∞ x
    ≡⟨ sym (BooleanRingStr.+IdR (snd B∞) (-∞ x)) ⟩
  -∞ x +∞ 𝟘∞
    ≡⟨ cong (-∞ x +∞_) (sym (char2-B∞ x)) ⟩
  -∞ x +∞ (x +∞ x)
    ≡⟨ BooleanRingStr.+Assoc (snd B∞) (-∞ x) x x ⟩
  (-∞ x +∞ x) +∞ x
    ≡⟨ cong (_+∞ x) (BooleanRingStr.+InvL (snd B∞) x) ⟩
  𝟘∞ +∞ x
    ≡⟨ BooleanRingStr.+IdL (snd B∞) x ⟩
  x ∎

-- Main correctness theorem: normalizeTerm is correct
normalizeTerm-correct : (t : freeBATerms ℕ) → ⟦ normalizeTerm t ⟧nf ≡ interpretB∞ t
normalizeTerm-correct (Tvar n) =
  finJoin∞ (n ∷ [])
    ≡⟨ refl ⟩
  g∞ n ∨∞ finJoin∞ []
    ≡⟨ zero-join-right (g∞ n) ⟩
  g∞ n ∎
normalizeTerm-correct (Tconst false) = refl
normalizeTerm-correct (Tconst true) = refl
normalizeTerm-correct (t +T s) =
  ⟦ xor-nf (normalizeTerm t) (normalizeTerm s) ⟧nf
    ≡⟨ xor-nf-correct (normalizeTerm t) (normalizeTerm s) ⟩
  ⟦ normalizeTerm t ⟧nf +∞ ⟦ normalizeTerm s ⟧nf
    ≡⟨ cong₂ _+∞_ (normalizeTerm-correct t) (normalizeTerm-correct s) ⟩
  interpretB∞ t +∞ interpretB∞ s ∎
normalizeTerm-correct (-T t) =
  ⟦ normalizeTerm t ⟧nf
    ≡⟨ normalizeTerm-correct t ⟩
  interpretB∞ t
    ≡⟨ sym (negation-is-id-B∞ (interpretB∞ t)) ⟩
  -∞ interpretB∞ t ∎
normalizeTerm-correct (t ·T s) =
  ⟦ meet-nf (normalizeTerm t) (normalizeTerm s) ⟧nf
    ≡⟨ meet-nf-correct (normalizeTerm t) (normalizeTerm s) ⟩
  ⟦ normalizeTerm t ⟧nf ∧∞ ⟦ normalizeTerm s ⟧nf
    ≡⟨ cong₂ _∧∞_ (normalizeTerm-correct t) (normalizeTerm-correct s) ⟩
  interpretB∞ t ∧∞ interpretB∞ s
    ≡⟨ refl ⟩
  interpretB∞ t ·∞ interpretB∞ s ∎

-- =============================================================================
-- Connection to quotient map and surjectivity (lines 8600-8750)
-- =============================================================================

-- The homomorphism from terms to B∞
termHom : freeBATerms ℕ → ⟨ B∞ ⟩
termHom = interpretB∞

-- Normal form exists for any element in the image of termHom
normalForm-from-term : (t : freeBATerms ℕ) → Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ termHom t
normalForm-from-term t = normalizeTerm t , normalizeTerm-correct t

-- The quotient map π∞ is surjective
π∞-surj : isSurjection (fst π∞)
π∞-surj = QB.quotientImageHomSurjective

-- The composition π∞ ∘ includeBATermsSurj is surjective
π∞-includeTerms-surj : isSurjection (fst π∞ ∘ fst includeBATermsSurj)
π∞-includeTerms-surj = compSurjection (fst includeBATermsSurj , snd includeBATermsSurj) (fst π∞ , π∞-surj) .snd

-- Define the composition for clarity
π∞-from-terms : freeBATerms ℕ → ⟨ B∞ ⟩
π∞-from-terms t = fst π∞ (fst includeBATermsSurj t)

-- π∞ preservation properties
private
  open module π∞-hom = IsCommRingHom (snd π∞) renaming
    (pres+ to π∞-+' ; pres· to π∞-·' ; pres- to π∞-neg' ; pres0 to π∞-0' ; pres1 to π∞-1')
  π∞-0 : fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ))) ≡ 𝟘∞
  π∞-0 = π∞-0'
  π∞-1 : fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ))) ≡ 𝟙∞
  π∞-1 = π∞-1'
  π∞-+ : (x y : ⟨ freeBA ℕ ⟩) → fst π∞ (BooleanRingStr._+_ (snd (freeBA ℕ)) x y) ≡ fst π∞ x +∞ fst π∞ y
  π∞-+ = π∞-+'
  π∞-· : (x y : ⟨ freeBA ℕ ⟩) → fst π∞ (BooleanRingStr._·_ (snd (freeBA ℕ)) x y) ≡ fst π∞ x ·∞ fst π∞ y
  π∞-· = π∞-·'
  π∞-neg : (x : ⟨ freeBA ℕ ⟩) → fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) x) ≡ -∞ fst π∞ x
  π∞-neg = π∞-neg'

-- The equality proof: interpretB∞ = π∞ ∘ includeBATermsSurj
interpretB∞-eq-composition : (t : freeBATerms ℕ) → interpretB∞ t ≡ π∞-from-terms t
interpretB∞-eq-composition (Tvar n) =
  g∞ n
    ≡⟨ refl ⟩
  fst π∞ (generator n)
    ≡⟨ cong (fst π∞) (sym (includeBATerms-Tvar n)) ⟩
  fst π∞ (fst includeBATermsSurj (Tvar n)) ∎
interpretB∞-eq-composition (Tconst false) =
  𝟘∞
    ≡⟨ sym π∞-0 ⟩
  fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-0) ⟩
  fst π∞ (fst includeBATermsSurj (Tconst false)) ∎
interpretB∞-eq-composition (Tconst true) =
  𝟙∞
    ≡⟨ sym π∞-1 ⟩
  fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-1) ⟩
  fst π∞ (fst includeBATermsSurj (Tconst true)) ∎
interpretB∞-eq-composition (t +T s) =
  interpretB∞ t +∞ interpretB∞ s
    ≡⟨ cong₂ _+∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t +∞ π∞-from-terms s
    ≡⟨ sym (π∞-+ (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._+_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-+ t s)) ⟩
  π∞-from-terms (t +T s) ∎
interpretB∞-eq-composition (-T t) =
  -∞ interpretB∞ t
    ≡⟨ cong -∞_ (interpretB∞-eq-composition t) ⟩
  -∞ π∞-from-terms t
    ≡⟨ sym (π∞-neg (fst includeBATermsSurj t)) ⟩
  fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj t))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-- t)) ⟩
  π∞-from-terms (-T t) ∎
interpretB∞-eq-composition (t ·T s) =
  interpretB∞ t ·∞ interpretB∞ s
    ≡⟨ cong₂ _·∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t ·∞ π∞-from-terms s
    ≡⟨ sym (π∞-· (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._·_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-· t s)) ⟩
  π∞-from-terms (t ·T s) ∎

-- interpretB∞ is surjective
interpretB∞-surjective : isSurjection interpretB∞
interpretB∞-surjective x = PT.map helper (π∞-includeTerms-surj x)
  where
  helper : Σ[ t ∈ freeBATerms ℕ ] π∞-from-terms t ≡ x → Σ[ t ∈ freeBATerms ℕ ] interpretB∞ t ≡ x
  helper pair = fst pair , interpretB∞-eq-composition (fst pair) ∙ snd pair

-- B∞-NormalForm is a set
open import Cubical.Data.List using (isOfHLevelList)
open import Cubical.Data.Nat using (isSetℕ)

isSetListℕ : isSet (List ℕ)
isSetListℕ = isOfHLevelList 0 isSetℕ

isSetB∞-NormalForm : isSet B∞-NormalForm
isSetB∞-NormalForm = Discrete→isSet discreteNF
  where
  open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec)
  open import Cubical.Data.List using (discreteList)
  open import Cubical.Data.Nat using (discreteℕ)

  discreteListℕ : Discrete (List ℕ)
  discreteListℕ = discreteList discreteℕ

  discreteNF : Discrete B∞-NormalForm
  discreteNF (joinForm ns) (joinForm ms) with discreteListℕ ns ms
  ... | yes p = yes (cong joinForm p)
  ... | no ¬p = no (λ eq → ¬p (joinForm-inj eq))
    where
    joinForm-inj : joinForm ns ≡ joinForm ms → ns ≡ ms
    joinForm-inj p = cong (λ { (joinForm x) → x ; (meetNegForm _) → [] }) p
  discreteNF (joinForm _) (meetNegForm _) = no (λ p → joinForm≢meetNegForm p)
    where
    joinForm≢meetNegForm : ∀ {ns ms} → joinForm ns ≡ meetNegForm ms → ⊥.⊥
    joinForm≢meetNegForm p = transport (cong (λ { (joinForm _) → Unit ; (meetNegForm _) → ⊥.⊥ }) p) tt
  discreteNF (meetNegForm _) (joinForm _) = no (λ p → meetNegForm≢joinForm p)
    where
    meetNegForm≢joinForm : ∀ {ns ms} → meetNegForm ns ≡ joinForm ms → ⊥.⊥
    meetNegForm≢joinForm p = transport (cong (λ { (joinForm _) → ⊥.⊥ ; (meetNegForm _) → Unit }) p) tt
  discreteNF (meetNegForm ns) (meetNegForm ms) with discreteListℕ ns ms
  ... | yes p = yes (cong meetNegForm p)
  ... | no ¬p = no (λ eq → ¬p (meetNegForm-inj eq))
    where
    meetNegForm-inj : meetNegForm ns ≡ meetNegForm ms → ns ≡ ms
    meetNegForm-inj p = cong (λ { (joinForm _) → [] ; (meetNegForm x) → x }) p

-- Truncated version: every element has some normal form (truncated)
normalFormExists-trunc : (x : ⟨ B∞ ⟩) → ∥ Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ x ∥₁
normalFormExists-trunc x = PT.map
  (λ pair → normalizeTerm (fst pair) , normalizeTerm-correct (fst pair) ∙ snd pair)
  (interpretB∞-surjective x)

-- =============================================================================
-- f-kernel using truncated normal forms (lines 9040-9098)
-- =============================================================================

-- f-kernel: if f(x) = (0,0), then x = 0
f-kernel-from-trunc : (x : ⟨ B∞ ⟩) → fst f x ≡ (𝟘∞ , 𝟘∞) → x ≡ 𝟘∞
f-kernel-from-trunc x fx=0 = PT.rec (BooleanRingStr.is-set (snd B∞) x 𝟘∞)
  (λ pair → let nf = fst pair
                eq = snd pair
            in sym eq ∙ f-kernel-normalForm nf (cong (fst f) eq ∙ fx=0))
  (normalFormExists-trunc x)

-- f-injective using the truncated approach
f-injective-from-trunc : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective-from-trunc x y fx=fy =
  let xy-diff : ⟨ B∞ ⟩
      xy-diff = x +∞ y

      f-xy-diff : fst f xy-diff ≡ (𝟘∞ , 𝟘∞)
      f-xy-diff =
        fst f (x +∞ y)
          ≡⟨ f-pres+ x y ⟩
        (fst f x) +× (fst f y)
          ≡⟨ cong (_+× (fst f y)) fx=fy ⟩
        (fst f y) +× (fst f y)
          ≡⟨ char2-B∞×B∞ (fst f y) ⟩
        (𝟘∞ , 𝟘∞) ∎

      xy=0 : xy-diff ≡ 𝟘∞
      xy=0 = f-kernel-from-trunc xy-diff f-xy-diff

      x=y : x ≡ y
      x=y = BooleanRing-xor-eq-to-eq' x y xy=0

  in x=y
  where
  BooleanRing-xor-eq-to-eq' : (a b : ⟨ B∞ ⟩) → a +∞ b ≡ 𝟘∞ → a ≡ b
  BooleanRing-xor-eq-to-eq' a b ab=0 =
    a
      ≡⟨ sym (BooleanRingStr.+IdR (snd B∞) a) ⟩
    a +∞ 𝟘∞
      ≡⟨ cong (a +∞_) (sym (char2-B∞ b)) ⟩
    a +∞ (b +∞ b)
      ≡⟨ BooleanRingStr.+Assoc (snd B∞) a b b ⟩
    (a +∞ b) +∞ b
      ≡⟨ cong (_+∞ b) ab=0 ⟩
    𝟘∞ +∞ b
      ≡⟨ BooleanRingStr.+IdL (snd B∞) b ⟩
    b ∎

-- Verification that f-injective can be replaced by f-injective-from-trunc
f-injective-verified : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective-verified = f-injective-from-trunc

-- =============================================================================
-- ClosedPropAsSpectrum (tex Lemma 251) (lines 9174-9276)
-- =============================================================================

module ClosedPropAsSpectrum where
  open import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

  -- The quotient ring BoolBR /Im α
  BoolBR-quotient : binarySequence → BooleanRing ℓ-zero
  BoolBR-quotient α = BoolBR QB./Im α

  -- Forward: all false → spectrum is inhabited
  all-false→Sp : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
               → BoolHom (BoolBR-quotient α) BoolBR
  all-false→Sp α all-false = QB.inducedHom {B = BoolBR} {f = α} BoolBR id-hom α-to-0
    where
    id-hom : BoolHom BoolBR BoolBR
    id-hom = idBoolHom BoolBR

    α-to-0 : (n : ℕ) → id-hom $cr (α n) ≡ BooleanRingStr.𝟘 (snd BoolBR)
    α-to-0 n = all-false n

  -- Backward: spectrum inhabited → all false
  Sp→all-false : (α : binarySequence) → BoolHom (BoolBR-quotient α) BoolBR
               → ((n : ℕ) → α n ≡ false)
  Sp→all-false α h n = αn-is-false (α n) refl
    where
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)

    π : ⟨ BoolBR ⟩ → ⟨ BoolBR-quotient α ⟩
    π = fst QB.quotientImageHom

    h-π-αn≡0 : fst h (π (α n)) ≡ false
    h-π-αn≡0 = cong (fst h) (QB.zeroOnImage {B = BoolBR} {f = α} n) ∙ h-pres0

    αn-is-false : (b : Bool) → α n ≡ b → b ≡ false
    αn-is-false false _ = refl
    αn-is-false true αn≡true = ex-falso (true≢false contradiction)
      where
      open IsCommRingHom (snd QB.quotientImageHom) renaming (pres1 to π-pres1)

      h-π-αn≡true : fst h (π (α n)) ≡ true
      h-π-αn≡true = cong (λ x → fst h (π x)) αn≡true
                  ∙ cong (fst h) π-pres1
                  ∙ h-pres1

      contradiction : true ≡ false
      contradiction = sym h-π-αn≡true ∙ h-π-αn≡0

  -- The equivalence: (∀n. αn = false) ↔ Sp(BoolBR /Im α)
  closedPropAsSpectrum : (α : binarySequence)
                       → ((n : ℕ) → α n ≡ false) ↔ BoolHom (BoolBR-quotient α) BoolBR
  closedPropAsSpectrum α = all-false→Sp α , Sp→all-false α

open ClosedPropAsSpectrum public

-- =============================================================================
-- ClosedPropIffStone (tex Corollary 1628) (lines 9277-9529)
-- =============================================================================
--
-- A proposition P is closed if and only if it is a Stone space.

module ClosedPropIffStone where
  open import Axioms.StoneDuality using (hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp)
  open ClosedPropAsSpectrum

  -- quotientPreservesBooleω is proven in work.agda at line 794
  -- It's a complex proof that requires additional infrastructure
  postulate
    quotientPreservesBooleω : (α : binarySequence) → ∥ has-Boole-ω' (BoolBR QB./Im α) ∥₁

  -- A closed proposition has Stone structure
  -- We show that if P ↔ (∀n. αn = false), then P ↔ Sp(BoolBR /Im α)
  -- and BoolBR /Im α is a Booleω

  closedProp→hasStoneStr : (P : hProp ℓ-zero) → isClosedProp P → hasStoneStr (fst P)
  closedProp→hasStoneStr P Pclosed = Booleω-P , Sp-eq
    where
    -- Extract the witness α from the closed structure
    α : binarySequence
    α = fst Pclosed

    -- P ↔ (∀n. αn = false)
    P→all-false : fst P → ((n : ℕ) → α n ≡ false)
    P→all-false = fst (snd Pclosed)

    all-false→P : ((n : ℕ) → α n ≡ false) → fst P
    all-false→P = snd (snd Pclosed)

    -- The quotient ring
    B-quotient : BooleanRing ℓ-zero
    B-quotient = BoolBR-quotient α

    -- The spectrum of the quotient
    Sp-quotient : Type ℓ-zero
    Sp-quotient = BoolHom B-quotient BoolBR

    -- From ClosedPropAsSpectrum: (∀n. αn = false) ↔ Sp(BoolBR /Im α)
    all-false↔Sp : ((n : ℕ) → α n ≡ false) ↔ Sp-quotient
    all-false↔Sp = closedPropAsSpectrum α

    -- P ↔ Sp-quotient (composing the biconditionals)
    P→Sp : fst P → Sp-quotient
    P→Sp p = fst all-false↔Sp (P→all-false p)

    Sp→P : Sp-quotient → fst P
    Sp→P h = all-false→P (snd all-false↔Sp h)

    -- The quotient is a Booleω
    B-quotient-Booleω : Booleω
    B-quotient-Booleω = B-quotient , quotientPreservesBooleω α

    -- P is an hProp by assumption
    isPropP : isProp (fst P)
    isPropP = snd P

    -- Sp-quotient is an hSet
    isSetSp-quotient : isSet Sp-quotient
    isSetSp-quotient = isSetSp B-quotient

    -- The intermediate type is a proposition
    all-false-type : Type ℓ-zero
    all-false-type = (n : ℕ) → α n ≡ false

    isProp-all-false : isProp all-false-type
    isProp-all-false = isPropΠ (λ n → isSetBool (α n) false)

    -- P ≃ all-false-type (since P is equivalent via biconditional and both are props)
    P≃all-false : fst P ≃ all-false-type
    P≃all-false = propBiimpl→Equiv isPropP isProp-all-false P→all-false all-false→P

    -- The round-trip identity for Sp-quotient
    Sp-roundtrip : (h : Sp-quotient) → fst all-false↔Sp (snd all-false↔Sp h) ≡ h
    Sp-roundtrip h = QB.inducedHomUnique {B = BoolBR} {f = α} BoolBR id-hom α-to-0 h h-comp
      where

      id-hom : BoolHom BoolBR BoolBR
      id-hom = idBoolHom BoolBR

      -- The proof that all αn = false, extracted from h
      all-false-from-h : (n : ℕ) → α n ≡ false
      all-false-from-h = snd all-false↔Sp h

      -- α maps to 0 under id-hom (since all αn = false)
      α-to-0 : (n : ℕ) → id-hom $cr (α n) ≡ BooleanRingStr.𝟘 (snd BoolBR)
      α-to-0 n = all-false-from-h n

      -- We need to show id-hom ≡ (h ∘cr QB.quotientImageHom)
      π : ⟨ BoolBR ⟩ → ⟨ B-quotient ⟩
      π = fst QB.quotientImageHom

      open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
      open IsCommRingHom (snd QB.quotientImageHom) renaming (pres0 to π-pres0 ; pres1 to π-pres1)

      h∘π-on-false : fst h (π false) ≡ false
      h∘π-on-false = cong (fst h) π-pres0 ∙ h-pres0

      h∘π-on-true : fst h (π true) ≡ true
      h∘π-on-true = cong (fst h) π-pres1 ∙ h-pres1

      h∘π≡id-pointwise : (b : Bool) → fst h (π b) ≡ b
      h∘π≡id-pointwise false = h∘π-on-false
      h∘π≡id-pointwise true = h∘π-on-true

      h-comp : id-hom ≡ (h ∘cr QB.quotientImageHom)
      h-comp = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing BoolBR)) f
                                                  (snd (BooleanRing→CommRing BoolBR)))
                      (sym (funExt h∘π≡id-pointwise))

    isProp-Sp-quotient : isProp Sp-quotient
    isProp-Sp-quotient h₁ h₂ =
      let all-f₁ = snd all-false↔Sp h₁
          all-f₂ = snd all-false↔Sp h₂
          all-f-eq : all-f₁ ≡ all-f₂
          all-f-eq = isProp-all-false all-f₁ all-f₂
      in h₁                                    ≡⟨ sym (Sp-roundtrip h₁) ⟩
         fst all-false↔Sp all-f₁               ≡⟨ cong (fst all-false↔Sp) all-f-eq ⟩
         fst all-false↔Sp all-f₂               ≡⟨ Sp-roundtrip h₂ ⟩
         h₂                                    ∎

    all-false≃Sp : all-false-type ≃ Sp-quotient
    all-false≃Sp = propBiimpl→Equiv isProp-all-false isProp-Sp-quotient
                    (fst all-false↔Sp) (snd all-false↔Sp)

    P≃Sp : fst P ≃ Sp-quotient
    P≃Sp = compEquiv P≃all-false all-false≃Sp

    -- The Booleω witness
    Booleω-P : Booleω
    Booleω-P = B-quotient-Booleω

    -- The path Sp(B-quotient) ≡ fst P
    Sp-eq : Sp Booleω-P ≡ fst P
    Sp-eq = sym (ua P≃Sp)

  -- A closed hProp determines a Stone space
  closedProp→Stone : (P : hProp ℓ-zero) → isClosedProp P → Stone
  closedProp→Stone P Pclosed = fst P , closedProp→hasStoneStr P Pclosed

open ClosedPropIffStone public
