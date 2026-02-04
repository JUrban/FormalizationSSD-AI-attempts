{-# OPTIONS --cubical --guardedness #-}

-- Part05a: f-injective infrastructure
-- This module provides the f-injective proof needed before Part05's use of Sp-f-surjective

module work.Part05a where

open import work.Part04 public

-- Additional imports for Part05a
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; isSetBool; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no; Discrete; Discrete→isSet)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isSetΠ)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Functions.Surjection using (isSurjection ; compSurjection)
open import BooleanRing.FreeBooleanRing.freeBATerms using
  (includeBATermsSurj ; freeBATerms ; includeBATerms-Tvar ;
   includeBATerms-+ ; includeBATerms-· ; includeBATerms-- ; includeBATerms-0 ; includeBATerms-1)
open import BooleanRing.FreeBooleanRing.SurjectiveTerms using (TermsOf_[_]; Tvar; Tconst; _+T_; -T_; _·T_; includeTerm)

-- =============================================================================
-- Part 05a: f-injective infrastructure
-- =============================================================================

-- The quotient map π∞ is surjective
π∞-surj : isSurjection (fst π∞)
π∞-surj = QB.quotientImageHomSurjective

-- The composition π∞ ∘ includeBATermsSurj is surjective
π∞-includeTerms-surj : isSurjection (fst π∞ ∘ fst includeBATermsSurj)
π∞-includeTerms-surj = compSurjection (fst includeBATermsSurj , snd includeBATermsSurj) (fst π∞ , π∞-surj) .snd

-- Define the composition for clarity
π∞-from-terms : freeBATerms ℕ → ⟨ B∞ ⟩
π∞-from-terms t = fst π∞ (fst includeBATermsSurj t)

-- Direct interpretation into B∞ (mirrors the structure of terms)
interpretB∞ : freeBATerms ℕ → ⟨ B∞ ⟩
interpretB∞ (Tvar n) = g∞ n
interpretB∞ (Tconst false) = 𝟘∞
interpretB∞ (Tconst true) = 𝟙∞
interpretB∞ (t +T s) = interpretB∞ t +∞ interpretB∞ s
interpretB∞ (-T t) = interpretB∞ t  -- ring negation is identity in Boolean rings
interpretB∞ (t ·T s) = interpretB∞ t ·∞ interpretB∞ s

-- Operations on π∞ (needed for composition proof)
π∞-0 : fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ))) ≡ 𝟘∞
π∞-0 = IsCommRingHom.pres0 (snd π∞)

π∞-1 : fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ))) ≡ 𝟙∞
π∞-1 = IsCommRingHom.pres1 (snd π∞)

π∞-gen : (n : ℕ) → fst π∞ (generator n) ≡ g∞ n
π∞-gen n = refl  -- by definition of g∞

private
  _+Free_ = BooleanRingStr._+_ (snd (freeBA ℕ))
  _·Free_ = BooleanRingStr._·_ (snd (freeBA ℕ))
  -Free_ = BooleanRingStr.-_ (snd (freeBA ℕ))

π∞-+ : (a b : ⟨ freeBA ℕ ⟩) → fst π∞ (a +Free b) ≡ fst π∞ a +∞ fst π∞ b
π∞-+ a b = IsCommRingHom.pres+ (snd π∞) a b

π∞-· : (a b : ⟨ freeBA ℕ ⟩) → fst π∞ (a ·Free b) ≡ fst π∞ a ·∞ fst π∞ b
π∞-· a b = IsCommRingHom.pres· (snd π∞) a b

π∞-neg : (a : ⟨ freeBA ℕ ⟩) → fst π∞ (-Free a) ≡ BooleanRingStr.-_ (snd B∞) (fst π∞ a)
π∞-neg a = IsCommRingHom.pres- (snd π∞) a

-- Proof that interpretB∞ equals π∞ ∘ includeBATermsSurj
-- Key: both are ring homomorphisms that agree on generators
interpretB∞-eq-composition : (t : freeBATerms ℕ) → interpretB∞ t ≡ π∞-from-terms t
interpretB∞-eq-composition (Tvar n) =
  g∞ n
    ≡⟨ sym (π∞-gen n) ⟩
  fst π∞ (generator n)
    ≡⟨ cong (fst π∞) (sym (includeBATerms-Tvar n)) ⟩
  π∞-from-terms (Tvar n) ∎
interpretB∞-eq-composition (Tconst false) =
  𝟘∞
    ≡⟨ sym π∞-0 ⟩
  fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-0) ⟩
  π∞-from-terms (Tconst false) ∎
interpretB∞-eq-composition (Tconst true) =
  𝟙∞
    ≡⟨ sym π∞-1 ⟩
  fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-1) ⟩
  π∞-from-terms (Tconst true) ∎
interpretB∞-eq-composition (t +T s) =
  interpretB∞ t +∞ interpretB∞ s
    ≡⟨ cong₂ _+∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t +∞ π∞-from-terms s
    ≡⟨ sym (π∞-+ (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._+_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-+ t s)) ⟩
  π∞-from-terms (t +T s) ∎
interpretB∞-eq-composition (-T t) =
  interpretB∞ t  -- -t = t in Boolean rings
    ≡⟨ interpretB∞-eq-composition t ⟩
  π∞-from-terms t
    ≡⟨ cong (fst π∞) (BooleanRing-neg-id t) ⟩
  fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj t))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-- t)) ⟩
  π∞-from-terms (-T t) ∎
  where
  -- In Boolean rings, x = -x (from characteristic 2: x + x = 0)
  -- Using BooleanAlgebraStr.-IsId from the Cubical library
  BooleanRing-neg-id : (s : freeBATerms ℕ) →
    fst includeBATermsSurj s ≡ BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj s)
  BooleanRing-neg-id s = BooleanAlgebraStr.-IsId (freeBA ℕ) {x = fst includeBATermsSurj s}
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

-- =============================================================================
-- Normal Forms for B∞ (use definitions from Part04)
-- =============================================================================

-- B∞-NormalForm, ⟦_⟧nf, finJoin∞, finMeetNeg∞ are already defined in Part04
-- and are re-exported via `open import work.Part04 public`

-- Additional imports for normal form infrastructure
open import Cubical.Data.List using (isOfHLevelList)
open import Cubical.Data.Nat using (isSetℕ; discreteℕ)
open import Cubical.Data.List using (discreteList)

isSetListℕ : isSet (List ℕ)
isSetListℕ = isOfHLevelList 0 isSetℕ

discreteListℕ : Discrete (List ℕ)
discreteListℕ = discreteList discreteℕ

-- B∞-NormalForm has decidable equality (needed for proving it's a set)
discreteNF : Discrete B∞-NormalForm
discreteNF (joinForm ns) (joinForm ms) with discreteListℕ ns ms
... | yes p = yes (cong joinForm p)
... | no ¬p = no (λ eq → ¬p (joinForm-inj eq))
  where
  joinForm-inj : joinForm ns ≡ joinForm ms → ns ≡ ms
  joinForm-inj p = cong (λ { (joinForm x) → x ; (meetNegForm _) → [] }) p
discreteNF (joinForm _) (meetNegForm _) = no (λ p → joinForm≢meetNegForm p)
  where
  joinForm≢meetNegForm : ∀ {ns ms} → joinForm ns ≡ meetNegForm ms → ⊥
  joinForm≢meetNegForm p = transport (cong (λ { (joinForm _) → Unit ; (meetNegForm _) → ⊥ }) p) tt
discreteNF (meetNegForm _) (joinForm _) = no (λ p → meetNegForm≢joinForm p)
  where
  meetNegForm≢joinForm : ∀ {ns ms} → meetNegForm ns ≡ joinForm ms → ⊥
  meetNegForm≢joinForm p = transport (cong (λ { (joinForm _) → ⊥ ; (meetNegForm _) → Unit }) p) tt
discreteNF (meetNegForm ns) (meetNegForm ms) with discreteListℕ ns ms
... | yes p = yes (cong meetNegForm p)
... | no ¬p = no (λ eq → ¬p (meetNegForm-inj eq))
  where
  meetNegForm-inj : meetNegForm ns ≡ meetNegForm ms → ns ≡ ms
  meetNegForm-inj p = cong (λ { (joinForm _) → [] ; (meetNegForm x) → x }) p

isSetB∞-NormalForm : isSet B∞-NormalForm
isSetB∞-NormalForm = Discrete→isSet discreteNF

-- =============================================================================
-- List operations for normal forms (needed for normalizeTerm)
-- =============================================================================

-- Membership test
_∈?_ : ℕ → List ℕ → Bool
n ∈? [] = false
n ∈? (m ∷ ms) with discreteℕ n m
... | yes _ = true
... | no _ = n ∈? ms

-- List intersection
_∩L_ : List ℕ → List ℕ → List ℕ
[] ∩L ms = []
(n ∷ ns) ∩L ms with n ∈? ms
... | true = n ∷ (ns ∩L ms)
... | false = ns ∩L ms

-- List difference
_∖L_ : List ℕ → List ℕ → List ℕ
[] ∖L ms = []
(n ∷ ns) ∖L ms with n ∈? ms
... | true = ns ∖L ms
... | false = n ∷ (ns ∖L ms)

-- Symmetric difference
_△L_ : List ℕ → List ℕ → List ℕ
ns △L ms = (ns ++ ms) ∖L (ns ∩L ms)

-- =============================================================================
-- normalizeTerm function
-- =============================================================================

-- XOR of two normal forms
xor-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
xor-nf (joinForm ns) (joinForm ms) = joinForm (ns △L ms)
xor-nf (joinForm ns) (meetNegForm ms) = meetNegForm (ns △L ms)
xor-nf (meetNegForm ns) (joinForm ms) = meetNegForm (ms △L ns)
xor-nf (meetNegForm ns) (meetNegForm ms) = joinForm (ns △L ms)

-- Meet of two normal forms
meet-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
meet-nf (joinForm ns) (joinForm ms) = joinForm (ns ∩L ms)
meet-nf (joinForm ns) (meetNegForm ms) = joinForm (ns ∖L ms)
meet-nf (meetNegForm ns) (joinForm ms) = joinForm (ms ∖L ns)
meet-nf (meetNegForm ns) (meetNegForm ms) = meetNegForm (ns ++ ms)

-- Normalize a term to a normal form
normalizeTerm : freeBATerms ℕ → B∞-NormalForm
normalizeTerm (Tvar n) = joinForm (n ∷ [])
normalizeTerm (Tconst false) = joinForm []
normalizeTerm (Tconst true) = meetNegForm []
normalizeTerm (t +T s) = xor-nf (normalizeTerm t) (normalizeTerm s)
normalizeTerm (-T t) = normalizeTerm t
normalizeTerm (t ·T s) = meet-nf (normalizeTerm t) (normalizeTerm s)

-- =============================================================================
-- normalizeTerm correctness (postulated for now)
-- =============================================================================

-- For now, we postulate the correctness of normalizeTerm
-- This is proved in Part06.agda but requires significant infrastructure
postulate
  normalizeTerm-correct : (t : freeBATerms ℕ) → ⟦ normalizeTerm t ⟧nf ≡ interpretB∞ t

-- =============================================================================
-- Truncated normal form existence
-- =============================================================================

-- Every element has a normal form (truncated)
normalFormExists-trunc : (x : ⟨ B∞ ⟩) → ∥ Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ x ∥₁
normalFormExists-trunc x = PT.map
  (λ pair → normalizeTerm (fst pair) , normalizeTerm-correct (fst pair) ∙ snd pair)
  (interpretB∞-surjective x)

-- =============================================================================
-- f-kernel using truncated normal forms
-- =============================================================================

-- Characteristic 2 properties
char2-B∞ : (x : ⟨ B∞ ⟩) → x +∞ x ≡ 𝟘∞
char2-B∞ x = BooleanAlgebraStr.characteristic2 B∞ {x}

char2-B∞×B∞ : (z : ⟨ B∞×B∞ ⟩) → z +× z ≡ (𝟘∞ , 𝟘∞)
char2-B∞×B∞ (a , b) = cong₂ _,_ (char2-B∞ a) (char2-B∞ b)

-- f-kernel on normal forms (copied from Part05, needed for f-kernel-from-trunc)
-- This is the key lemma that links normal forms to f-kernel
postulate
  f-kernel-normalForm-05a : (nf : B∞-NormalForm) → fst f ⟦ nf ⟧nf ≡ (𝟘∞ , 𝟘∞) → ⟦ nf ⟧nf ≡ 𝟘∞

-- f-kernel using truncated approach
f-kernel-from-trunc-05a : (x : ⟨ B∞ ⟩) → fst f x ≡ (𝟘∞ , 𝟘∞) → x ≡ 𝟘∞
f-kernel-from-trunc-05a x fx=0 = PT.rec (BooleanRingStr.is-set (snd B∞) x 𝟘∞)
  (λ pair → let nf = fst pair
                eq = snd pair
            in sym eq ∙ f-kernel-normalForm-05a nf (cong (fst f) eq ∙ fx=0))
  (normalFormExists-trunc x)

-- =============================================================================
-- f-injective proof (the key theorem)
-- =============================================================================

-- f-injective using the truncated approach
f-injective-05a : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective-05a x y fx=fy =
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
      xy=0 = f-kernel-from-trunc-05a xy-diff f-xy-diff

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

-- =============================================================================
-- Summary
-- =============================================================================
-- Part05a provides:
-- - f-injective-05a : proof that f : B∞ → B∞×B∞ is injective
-- - normalFormExists-trunc : every element of B∞ has a normal form (truncated)
-- - f-kernel-from-trunc-05a : f-kernel is trivial
--
-- These can be used to replace the f-injective postulate in Part04 once
-- the file structure is reorganized to avoid circular dependencies.
--
-- Current status: f-injective-05a depends on two technical postulates:
-- 1. normalizeTerm-correct : (t : freeBATerms ℕ) → ⟦ normalizeTerm t ⟧nf ≡ interpretB∞ t
-- 2. f-kernel-normalForm-05a : (nf : B∞-NormalForm) → fst f ⟦ nf ⟧nf ≡ (𝟘∞ , 𝟘∞) → ⟦ nf ⟧nf ≡ 𝟘∞
--
-- These are proved in Part05.agda and Part06.agda respectively, creating the
-- forward reference issue. Once properly restructured, all postulates can be eliminated.
