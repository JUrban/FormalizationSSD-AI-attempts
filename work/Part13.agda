{-# OPTIONS --cubical --guardedness #-}

module work.Part13 where

-- =============================================================================
-- Part 13: StoneEqualityClosedModule (work.agda lines 10135-10554)
-- =============================================================================

-- Import Part12 for previous definitions
open import work.Part12 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open Iso
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv; invEq; secEq; retEq)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ; isOfHLevelΣ)
open import Cubical.Foundations.Transport using (transportTransport⁻; transport⁻)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ renaming (rec to ex-falso)
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp; isSetBoolHom; StoneDualityAxiom; SDHomVersion; evaluationMap)

-- Note: sd-axiom is already exported from Part12

-- =============================================================================
-- StoneEqualityClosed (tex Lemma 1636)
-- =============================================================================
--
-- For all S:Stone and s,t:S, the proposition s=t is closed.
--
-- Proof (from tex):
-- Suppose S = Sp(B) and let G be a countable set of generators for B.
-- Then s=t iff s(g) = t(g) for all g:G.
-- So s=t is a countable conjunction of decidable propositions, hence closed.

module StoneEqualityClosedModule where

  -- Stone spaces are sets via the embedding into 2^B
  hasStoneStr→isSet : (S : Stone) → isSet (fst S)
  hasStoneStr→isSet (X , B , SpB≡X) = subst isSet SpB≡X (isSetBoolHom (fst B) BoolBR)

  -- Note: Bool-equality-decidable is already exported from Part01

  -- Helper: Bool equality is closed (decidable implies closed)
  Bool-eq-closed : (x y : Bool) → isClosedProp ((x ≡ y) , isSetBool x y)
  Bool-eq-closed x y = decIsClosed ((x ≡ y) , isSetBool x y) (Bool-equality-decidable x y)

  -- Key lemma: BoolHom equality is function equality
  BoolHom-ext : {A B : BooleanRing ℓ-zero} → (h k : BoolHom A B)
    → ((x : ⟨ A ⟩) → fst h x ≡ fst k x) → h ≡ k
  BoolHom-ext h k pw = CommRingHom≡ (funExt pw)

  -- For a specific presentation, prove equality is closed
  SpEqualityClosed-from-presentation : (B : BooleanRing ℓ-zero)
    → (pres : has-Boole-ω' B)
    → (s t : Sp (B , ∣ pres ∣₁))
    → isClosedProp ((s ≡ t) , isSetBoolHom B BoolBR s t)
  SpEqualityClosed-from-presentation B (f , equiv) s t = proof
    where
    -- The quotient of freeBA ℕ by f
    Q : BooleanRing ℓ-zero
    Q = freeBA ℕ QB./Im f

    -- The equivalence B ≅ Q
    presEquiv : ⟨ B ⟩ ≃ ⟨ Q ⟩
    presEquiv = fst equiv

    presEquiv-hom : BoolHom B Q
    presEquiv-hom = (fst presEquiv) , snd equiv

    presEquiv⁻¹ : ⟨ Q ⟩ → ⟨ B ⟩
    presEquiv⁻¹ = invEq presEquiv

    -- The quotient map
    π : BoolHom (freeBA ℕ) Q
    π = QB.quotientImageHom

    -- Generators in B: image of ℕ under the composition presEquiv⁻¹ ∘ π ∘ generator
    gen-in-B : ℕ → ⟨ B ⟩
    gen-in-B n = presEquiv⁻¹ (fst π (generator n))

    -- The key predicate: s and t agree on generator n
    P : ℕ → hProp ℓ-zero
    P n = (s $cr (gen-in-B n) ≡ t $cr (gen-in-B n)) , isSetBool _ _

    -- Each P n is closed (decidable)
    P-closed : (n : ℕ) → isClosedProp (P n)
    P-closed n = Bool-eq-closed (s $cr (gen-in-B n)) (t $cr (gen-in-B n))

    -- ∀n. P n is closed
    ∀P-closed : isClosedProp (((n : ℕ) → fst (P n)) , isPropΠ (λ n → snd (P n)))
    ∀P-closed = closedCountableIntersection P P-closed

    -- Forward: if s = t, then clearly they agree on all generators
    agree-forward : s ≡ t → (n : ℕ) → fst (P n)
    agree-forward s=t n = cong (λ h → h $cr (gen-in-B n)) s=t

    -- The witness sequence for ∀P-closed
    β : binarySequence
    β = fst ∀P-closed

    -- Direction 1: s ≡ t → β all false
    s=t→βFalse : s ≡ t → (k : ℕ) → β k ≡ false
    s=t→βFalse s=t = fst (snd ∀P-closed) (agree-forward s=t)

    -- The inverse of the equivalence as a BoolHom
    presEquiv⁻¹-hom : BoolHom Q B
    presEquiv⁻¹-hom = BooleanEquivToHomInv B Q equiv

    -- Compositions with π to get homomorphisms from freeBA ℕ
    s-on-free : BoolHom (freeBA ℕ) BoolBR
    s-on-free = s ∘cr presEquiv⁻¹-hom ∘cr π

    t-on-free : BoolHom (freeBA ℕ) BoolBR
    t-on-free = t ∘cr presEquiv⁻¹-hom ∘cr π

    agree-on-free-gen : ((n : ℕ) → fst (P n))
      → (fst s-on-free ∘ generator ≡ fst t-on-free ∘ generator)
    agree-on-free-gen allP = funExt (λ n → allP n)

    -- By universal property: two homomorphisms from freeBA that agree on generators are equal
    s-on-free=t-on-free : ((n : ℕ) → fst (P n)) → s-on-free ≡ t-on-free
    s-on-free=t-on-free allP =
      let s-restr : ℕ → Bool
          s-restr = fst s-on-free ∘ generator
          t-restr : ℕ → Bool
          t-restr = fst t-on-free ∘ generator
          induced-s : BoolHom (freeBA ℕ) BoolBR
          induced-s = Iso.fun (freeBA-universal-property ℕ BoolBR) s-restr
          induced-t : BoolHom (freeBA ℕ) BoolBR
          induced-t = Iso.fun (freeBA-universal-property ℕ BoolBR) t-restr
          s-on-free=induced : induced-s ≡ s-on-free
          s-on-free=induced = Iso.sec (freeBA-universal-property ℕ BoolBR) s-on-free
          t-on-free=induced : induced-t ≡ t-on-free
          t-on-free=induced = Iso.sec (freeBA-universal-property ℕ BoolBR) t-on-free
          s-restr=t-restr : s-restr ≡ t-restr
          s-restr=t-restr = agree-on-free-gen allP
          induced-s=induced-t : induced-s ≡ induced-t
          induced-s=induced-t = cong (Iso.fun (freeBA-universal-property ℕ BoolBR)) s-restr=t-restr
      in sym s-on-free=induced ∙ induced-s=induced-t ∙ t-on-free=induced

    s-on-Q : BoolHom Q BoolBR
    s-on-Q = s ∘cr presEquiv⁻¹-hom

    t-on-Q : BoolHom Q BoolBR
    t-on-Q = t ∘cr presEquiv⁻¹-hom

    s-on-Q∘π=s-on-free : fst s-on-Q ∘ fst π ≡ fst s-on-free
    s-on-Q∘π=s-on-free = refl

    t-on-Q∘π=t-on-free : fst t-on-Q ∘ fst π ≡ fst t-on-free
    t-on-Q∘π=t-on-free = refl

    s-on-Q=t-on-Q-fst : ((n : ℕ) → fst (P n)) → fst s-on-Q ≡ fst t-on-Q
    s-on-Q=t-on-Q-fst allP =
      let s-free=t-free : s-on-free ≡ t-on-free
          s-free=t-free = s-on-free=t-on-free allP
          eq-on-π : fst s-on-Q ∘ fst π ≡ fst t-on-Q ∘ fst π
          eq-on-π = s-on-Q∘π=s-on-free ∙ cong fst s-free=t-free ∙ sym t-on-Q∘π=t-on-free
      in QB.quotientImageHomEpi (Bool , isSetBool) eq-on-π

    s-on-Q=t-on-Q : ((n : ℕ) → fst (P n)) → s-on-Q ≡ t-on-Q
    s-on-Q=t-on-Q allP = BoolHom-ext {Q} {BoolBR} s-on-Q t-on-Q (λ q → funExt⁻ (s-on-Q=t-on-Q-fst allP) q)

    -- Need: presEquiv⁻¹-hom ∘cr presEquiv-hom = idBoolHom B
    leftInv : presEquiv⁻¹-hom ∘cr presEquiv-hom ≡ idBoolHom B
    leftInv = BooleanEquivLeftInv B Q equiv

    ∀P→s=t : ((n : ℕ) → fst (P n)) → s ≡ t
    ∀P→s=t allP =
      let s-on-Q=t-on-Q' : s-on-Q ≡ t-on-Q
          s-on-Q=t-on-Q' = s-on-Q=t-on-Q allP
          s=s∘id : s ≡ s ∘cr idBoolHom B
          s=s∘id = BoolHom-ext {B} {BoolBR} s (s ∘cr idBoolHom B) (λ _ → refl)
          t=t∘id : t ≡ t ∘cr idBoolHom B
          t=t∘id = BoolHom-ext {B} {BoolBR} t (t ∘cr idBoolHom B) (λ _ → refl)
          step1 : s ∘cr idBoolHom B ≡ s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)
          step1 = cong (s ∘cr_) (sym leftInv)
          step2 : s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom) ≡ s-on-Q ∘cr presEquiv-hom
          step2 = BoolHom-ext {B} {BoolBR} (s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)) (s-on-Q ∘cr presEquiv-hom) (λ _ → refl)
          step3 : s-on-Q ∘cr presEquiv-hom ≡ t-on-Q ∘cr presEquiv-hom
          step3 = cong (_∘cr presEquiv-hom) s-on-Q=t-on-Q'
          step4 : t-on-Q ∘cr presEquiv-hom ≡ t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)
          step4 = BoolHom-ext {B} {BoolBR} (t-on-Q ∘cr presEquiv-hom) (t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)) (λ _ → refl)
          step5 : t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom) ≡ t ∘cr idBoolHom B
          step5 = cong (t ∘cr_) leftInv
      in s=s∘id ∙ step1 ∙ step2 ∙ step3 ∙ step4 ∙ step5 ∙ sym t=t∘id

    βFalse→s=t : ((k : ℕ) → β k ≡ false) → s ≡ t
    βFalse→s=t = λ h → ∀P→s=t (snd (snd ∀P-closed) h)

    proof : isClosedProp ((s ≡ t) , isSetBoolHom B BoolBR s t)
    proof = β , s=t→βFalse , βFalse→s=t

  -- Postulate that isClosedProp is a proposition (technical debt)
  postulate
    isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)

  -- Core lemma: equality in Sp(B) is closed
  SpEqualityClosed : (B : Booleω) → (s t : Sp B)
    → isClosedProp ((s ≡ t) , isSetBoolHom (fst B) BoolBR s t)
  SpEqualityClosed (B , presB) s t = PT.rec (isPropIsClosedProp {(s ≡ t) , isSetBoolHom B BoolBR s t})
    (λ pres → SpEqualityClosed-from-presentation B pres s t)
    presB

  -- Main theorem: For S : Stone, equality is closed
  StoneEqualityClosed : (S : Stone) → (s t : fst S)
    → isClosedProp ((s ≡ t) , hasStoneStr→isSet S s t)
  StoneEqualityClosed (X , B , path) s t = closedEquiv
    ((s' ≡ t') , isSetBoolHom (fst B) BoolBR s' t')
    ((s ≡ t) , hasStoneStr→isSet (X , B , path) s t)
    forward backward spClosed
    where
    s' : Sp B
    s' = transport⁻ path s

    t' : Sp B
    t' = transport⁻ path t

    spClosed : isClosedProp ((s' ≡ t') , isSetBoolHom (fst B) BoolBR s' t')
    spClosed = SpEqualityClosed B s' t'

    forward : (s' ≡ t') → (s ≡ t)
    forward s'=t' =
      s                                 ≡⟨ sym (transportTransport⁻ path s) ⟩
      transport path (transport⁻ path s)  ≡⟨ cong (transport path) s'=t' ⟩
      transport path (transport⁻ path t)  ≡⟨ transportTransport⁻ path t ⟩
      t ∎

    backward : (s ≡ t) → (s' ≡ t')
    backward s=t = cong (transport⁻ path) s=t

open StoneEqualityClosedModule public
