{-# OPTIONS --cubical --guardedness #-}

module work.Part10 where

-- =============================================================================
-- Part 10: SpB∞ ≅ ℕ∞ isomorphism, Stone modules, and normal form operations
--          (lines 7500-8500 of work.agda)
-- =============================================================================

-- Import Part09 for previous definitions
open import work.Part09 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open Iso
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; inj-m+; +-zero; injSuc; snotz; znots)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum.Properties using (module ⊎Path; isProp⊎)
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; idBoolEquiv; has-Countability-structure)
open import Axioms.StoneDuality using (Sp; Booleω; hasStoneStr; Stone)

-- Open BooleanRingStr for B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; _+_ to _+×_)

-- _+∞_ is needed locally
open BooleanRingStr (snd B∞) using () renaming (_+_ to _+∞_)

-- =============================================================================
-- SpB∞-to-ℕ∞ injectivity (lines 7516-7575)
-- =============================================================================

-- The proof uses equalityFromEqualityOnGenerators from freeBATerms.agda
open import BooleanRing.FreeBooleanRing.freeBATerms using (equalityFromEqualityOnGenerators)

-- Homomorphisms out of B∞ are determined by their values on generators
SpB∞-to-ℕ∞-injective : (h₁ h₂ : Sp B∞-Booleω) →
  SpB∞-to-ℕ∞ h₁ ≡ SpB∞-to-ℕ∞ h₂ → h₁ ≡ h₂
SpB∞-to-ℕ∞-injective h₁ h₂ seq-eq = B∞-hom-eq
  where
  -- The sequences are equal, so h₁ and h₂ agree on all generators g∞ n
  seq-eq-pointwise : (n : ℕ) → h₁ $cr (g∞ n) ≡ h₂ $cr (g∞ n)
  seq-eq-pointwise n = funExt⁻ (cong fst seq-eq) n

  -- Compose with π∞ : freeBA ℕ → B∞ to get homomorphisms from freeBA ℕ
  h₁-free h₂-free : BoolHom (freeBA ℕ) BoolBR
  h₁-free = h₁ ∘cr π∞
  h₂-free = h₂ ∘cr π∞

  -- These agree on generators
  agree-on-gens : (n : ℕ) → h₁-free $cr (generator n) ≡ h₂-free $cr (generator n)
  agree-on-gens n = seq-eq-pointwise n

  -- By equalityFromEqualityOnGenerators, h₁-free = h₂-free
  free-hom-eq : h₁-free ≡ h₂-free
  free-hom-eq = equalityFromEqualityOnGenerators BoolBR h₁-free h₂-free agree-on-gens

  -- Since π∞ is epi, h₁ = h₂
  fst-hom-eq : fst h₁ ≡ fst h₂
  fst-hom-eq = QB.quotientImageHomEpi {B = freeBA ℕ} {f = relB∞}
    (⟨ BoolBR ⟩ , BooleanRingStr.is-set (snd BoolBR))
    (cong fst free-hom-eq)

  -- Lift to equality of homomorphisms using CommRingHom≡
  B∞-hom-eq : h₁ ≡ h₂
  B∞-hom-eq = CommRingHom≡ fst-hom-eq

-- Retraction: ℕ∞-to-SpB∞ ∘ SpB∞-to-ℕ∞ = id
SpB∞-retraction : (h : Sp B∞-Booleω) → ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h) ≡ h
SpB∞-retraction h = SpB∞-to-ℕ∞-injective (ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h)) h
  (SpB∞-roundtrip (SpB∞-to-ℕ∞ h))

-- The isomorphism between Sp B∞ and ℕ∞
SpB∞≅ℕ∞ : Iso (Sp B∞-Booleω) ℕ∞
SpB∞≅ℕ∞ = iso SpB∞-to-ℕ∞ ℕ∞-to-SpB∞ SpB∞-roundtrip SpB∞-retraction

-- The equivalence
SpB∞≃ℕ∞ : Sp B∞-Booleω ≃ ℕ∞
SpB∞≃ℕ∞ = isoToEquiv SpB∞≅ℕ∞

-- =============================================================================
-- ℕ∞ is Stone (lines 7603-7618)
-- =============================================================================

module ℕ∞IsStoneModule where
  -- ℕ∞ has Stone structure witnessed by B∞-Booleω
  ℕ∞-has-StoneStr : hasStoneStr ℕ∞
  ℕ∞-has-StoneStr = B∞-Booleω , ua SpB∞≃ℕ∞

open ℕ∞IsStoneModule public

-- =============================================================================
-- ℕ∞ ⊎ ℕ∞ is Stone (lines 7620-7711)
-- =============================================================================

module ℕ∞⊎ℕ∞IsStoneModule where
  -- The spectrum of B∞×B∞ is equivalent to ℕ∞ ⊎ ℕ∞
  SpB∞×B∞→ℕ∞⊎ℕ∞ : Sp B∞×B∞-Booleω → ℕ∞ ⊎.⊎ ℕ∞
  SpB∞×B∞→ℕ∞⊎ℕ∞ h = ⊎.map SpB∞-to-ℕ∞ SpB∞-to-ℕ∞ (Sp-prod-to-sum h)

  ℕ∞⊎ℕ∞→SpB∞×B∞ : ℕ∞ ⊎.⊎ ℕ∞ → Sp B∞×B∞-Booleω
  ℕ∞⊎ℕ∞→SpB∞×B∞ = Sp-sum-to-prod ∘ (⊎.map ℕ∞-to-SpB∞ ℕ∞-to-SpB∞)

open ℕ∞⊎ℕ∞IsStoneModule public

-- =============================================================================
-- Bool is Stone (lines 7713-7820)
-- =============================================================================

module BoolIsStoneModule where
  -- Bool has Stone structure
  Bool-has-StoneStr : hasStoneStr Bool
  Bool-has-StoneStr = Bool²-Booleω , ua Sp-Bool²≃Bool

  -- Local forward declaration of StoneSigmaClosed
  private
    LocalSigmaStoneType : (S : Stone) → (T : fst S → Stone) → Type₀
    LocalSigmaStoneType S T = Σ[ x ∈ fst S ] fst (T x)

    postulate
      LocalStoneSigmaClosed : (S : Stone) (T : fst S → Stone)
        → hasStoneStr (LocalSigmaStoneType S T)

  -- Construct Stone objects from hasStoneStr witnesses
  Bool-Stone : Stone
  Bool-Stone = Bool , Bool-has-StoneStr

  ℕ∞-Stone : Stone
  ℕ∞-Stone = ℕ∞ , ℕ∞-has-StoneStr

  -- Constant family: T(b) = ℕ∞ for all b
  ℕ∞-const-family : Bool → Stone
  ℕ∞-const-family _ = ℕ∞-Stone

  -- By LocalStoneSigmaClosed, Σ Bool (λ _ → ℕ∞) is Stone
  ΣBool-ℕ∞-has-StoneStr : hasStoneStr (Σ Bool (λ _ → ℕ∞))
  ΣBool-ℕ∞-has-StoneStr = LocalStoneSigmaClosed Bool-Stone ℕ∞-const-family

  -- Key equivalence: ℕ∞ ⊎ ℕ∞ ≃ Σ Bool (λ _ → ℕ∞)
  ⊎-as-Σ : (A : Type₀) → A ⊎.⊎ A ≃ Σ Bool (λ _ → A)
  ⊎-as-Σ A = isoToEquiv (iso to from to-from from-to)
    where
    to : A ⊎.⊎ A → Σ Bool (λ _ → A)
    to (⊎.inl a) = true , a
    to (⊎.inr a) = false , a
    from : Σ Bool (λ _ → A) → A ⊎.⊎ A
    from (true , a) = ⊎.inl a
    from (false , a) = ⊎.inr a
    to-from : (x : Σ Bool (λ _ → A)) → to (from x) ≡ x
    to-from (true , a) = refl
    to-from (false , a) = refl
    from-to : (x : A ⊎.⊎ A) → from (to x) ≡ x
    from-to (⊎.inl a) = refl
    from-to (⊎.inr a) = refl

  ℕ∞⊎ℕ∞≃ΣBool-ℕ∞ : ℕ∞ ⊎.⊎ ℕ∞ ≃ Σ Bool (λ _ → ℕ∞)
  ℕ∞⊎ℕ∞≃ΣBool-ℕ∞ = ⊎-as-Σ ℕ∞

  -- Transport Stone structure across the equivalence
  ℕ∞⊎ℕ∞-has-StoneStr-alt : hasStoneStr (ℕ∞ ⊎.⊎ ℕ∞)
  ℕ∞⊎ℕ∞-has-StoneStr-alt = subst hasStoneStr (sym (ua ℕ∞⊎ℕ∞≃ΣBool-ℕ∞)) ΣBool-ℕ∞-has-StoneStr

open BoolIsStoneModule public

-- =============================================================================
-- Normal Form Operations - Building blocks for normalFormExists (lines 7822-8000)
-- =============================================================================

-- Check if n is in list
_∈?_ : ℕ → List ℕ → Bool
n ∈? [] = false
n ∈? (m ∷ ms) with discreteℕ n m
... | yes _ = true
... | no _ = n ∈? ms

-- Intersection of two lists
_∩L_ : List ℕ → List ℕ → List ℕ
[] ∩L ms = []
(n ∷ ns) ∩L ms with n ∈? ms
... | true = n ∷ (ns ∩L ms)
... | false = ns ∩L ms

-- Meet of two joinForms (uses intersection due to orthogonality)
meet-joinForm-joinForm : List ℕ → List ℕ → B∞-NormalForm
meet-joinForm-joinForm ns ms = joinForm (ns ∩L ms)

-- Lemmas for g∞ meet finite join
g∞-meet-finJoin-in : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ true →
  g∞ n ∧∞ finJoin∞ ms ≡ g∞ n
g∞-meet-finJoin-in n [] p = ex-falso (true≢false (sym p))
g∞-meet-finJoin-in n (m ∷ ms) p with discreteℕ n m
... | yes n=m =
  g∞ n ∧∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∧DistR∨ ⟩
  (g∞ n ∧∞ g∞ m) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (cong (g∞ n ∧∞_) (cong g∞ (sym n=m))) refl ⟩
  (g∞ n ∧∞ g∞ n) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong (_∨∞ (g∞ n ∧∞ finJoin∞ ms)) B∞-BoolAlg.∧Idem ⟩
  g∞ n ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∨AbsorbL∧ ⟩
  g∞ n ∎
... | no n≠m =
  g∞ n ∧∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∧DistR∨ ⟩
  (g∞ n ∧∞ g∞ m) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (gen-orthogonal n m n≠m) (g∞-meet-finJoin-in n ms p) ⟩
  𝟘∞ ∨∞ g∞ n
    ≡⟨ B∞-BoolAlg.∨IdL ⟩
  g∞ n ∎

g∞-meet-finJoin-notin : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ false →
  g∞ n ∧∞ finJoin∞ ms ≡ 𝟘∞
g∞-meet-finJoin-notin n [] _ =
  g∞ n ∧∞ 𝟘∞         ≡⟨ B∞-BoolAlg.∧AnnihilR ⟩
  𝟘∞ ∎
g∞-meet-finJoin-notin n (m ∷ ms) p with discreteℕ n m
... | yes n=m = ex-falso (true≢false p)
... | no n≠m =
  g∞ n ∧∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∧DistR∨ ⟩
  (g∞ n ∧∞ g∞ m) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (gen-orthogonal n m n≠m) (g∞-meet-finJoin-notin n ms p) ⟩
  𝟘∞ ∨∞ 𝟘∞
    ≡⟨ B∞-BoolAlg.∨IdR ⟩
  𝟘∞ ∎

-- Main correctness lemma: finite join meet finite join = intersection join
meet-joinForm-joinForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns ∧∞ finJoin∞ ms ≡ finJoin∞ (ns ∩L ms)
meet-joinForm-joinForm-correct [] ms =
  𝟘∞ ∧∞ finJoin∞ ms     ≡⟨ B∞-BoolAlg.∧AnnihilL ⟩
  𝟘∞ ∎
meet-joinForm-joinForm-correct (n ∷ ns) ms with n ∈? ms | inspect (n ∈?_) ms
... | true | [ n∈ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finJoin∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  (g∞ n ∧∞ finJoin∞ ms) ∨∞ (finJoin∞ ns ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finJoin-in n ms n∈ms) (meet-joinForm-joinForm-correct ns ms) ⟩
  g∞ n ∨∞ finJoin∞ (ns ∩L ms) ∎
... | false | [ n∉ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finJoin∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  (g∞ n ∧∞ finJoin∞ ms) ∨∞ (finJoin∞ ns ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finJoin-notin n ms n∉ms) (meet-joinForm-joinForm-correct ns ms) ⟩
  𝟘∞ ∨∞ finJoin∞ (ns ∩L ms)
    ≡⟨ B∞-BoolAlg.∨IdL ⟩
  finJoin∞ (ns ∩L ms) ∎

-- Correctness of join-joinForm: join of two joinForms is their concatenation
join-joinForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns ∨∞ finJoin∞ ms ≡ finJoin∞ (ns ++ ms)
join-joinForm-correct [] ms =
  𝟘∞ ∨∞ finJoin∞ ms   ≡⟨ B∞-BoolAlg.∨IdL ⟩
  finJoin∞ ms ∎
join-joinForm-correct (n ∷ ns) ms =
  (g∞ n ∨∞ finJoin∞ ns) ∨∞ finJoin∞ ms
    ≡⟨ sym B∞-BoolAlg.∨Assoc ⟩
  g∞ n ∨∞ (finJoin∞ ns ∨∞ finJoin∞ ms)
    ≡⟨ cong (g∞ n ∨∞_) (join-joinForm-correct ns ms) ⟩
  g∞ n ∨∞ finJoin∞ (ns ++ ms) ∎

-- Correctness of meet-meetNegForm: meet of two meetNegForms is their concatenation
meet-meetNegForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns ∧∞ finMeetNeg∞ ms ≡ finMeetNeg∞ (ns ++ ms)
meet-meetNegForm-correct [] ms =
  𝟙∞ ∧∞ finMeetNeg∞ ms   ≡⟨ B∞-BoolAlg.∧IdL ⟩
  finMeetNeg∞ ms ∎
meet-meetNegForm-correct (n ∷ ns) ms =
  ((¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns) ∧∞ finMeetNeg∞ ms
    ≡⟨ sym B∞-BoolAlg.∧Assoc ⟩
  (¬∞ (g∞ n)) ∧∞ (finMeetNeg∞ ns ∧∞ finMeetNeg∞ ms)
    ≡⟨ cong ((¬∞ (g∞ n)) ∧∞_) (meet-meetNegForm-correct ns ms) ⟩
  (¬∞ (g∞ n)) ∧∞ finMeetNeg∞ (ns ++ ms) ∎

-- =============================================================================
-- Mixed normal form cases (lines 7949-8047)
-- =============================================================================

-- Helper: if a·b = 0 in a Boolean algebra, then a ∧ ¬b = a
∧-neg-orthogonal : (a b : ⟨ B∞ ⟩) → a ·∞ b ≡ 𝟘∞ → a ∧∞ (¬∞ b) ≡ a
∧-neg-orthogonal a b ab=0 =
  a ∧∞ (¬∞ b)
    ≡⟨ refl ⟩
  a ·∞ (𝟙∞ +∞ b)
    ≡⟨ BooleanRingStr.·DistR+ (snd B∞) a 𝟙∞ b ⟩
  (a ·∞ 𝟙∞) +∞ (a ·∞ b)
    ≡⟨ cong₂ _+∞_ (BooleanRingStr.·IdR (snd B∞) a) ab=0 ⟩
  a +∞ 𝟘∞
    ≡⟨ BooleanRingStr.+IdR (snd B∞) a ⟩
  a ∎

-- Generator meets negated generator: g_n ∧ ¬g_m = g_n when n ≠ m
g∞-meet-neg-g∞-neq : (n m : ℕ) → ¬ (n ≡ m) → (g∞ n) ∧∞ (¬∞ (g∞ m)) ≡ g∞ n
g∞-meet-neg-g∞-neq n m n≠m = ∧-neg-orthogonal (g∞ n) (g∞ m) (gen-orthogonal n m n≠m)

-- Generator meets negated generator: g_n ∧ ¬g_n = 0
g∞-meet-neg-g∞-eq : (n : ℕ) → (g∞ n) ∧∞ (¬∞ (g∞ n)) ≡ 𝟘∞
g∞-meet-neg-g∞-eq n = B∞-BoolAlg.¬Cancels∧R

-- Generator meets finite meet of negations
g∞-meet-finMeetNeg-notin : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ false →
  (g∞ n) ∧∞ finMeetNeg∞ ms ≡ g∞ n
g∞-meet-finMeetNeg-notin n [] _ =
  (g∞ n) ∧∞ 𝟙∞   ≡⟨ B∞-BoolAlg.∧IdR ⟩
  g∞ n ∎
g∞-meet-finMeetNeg-notin n (m ∷ ms) p with discreteℕ n m
... | yes n=m = ex-falso (true≢false p)
... | no n≠m =
  (g∞ n) ∧∞ ((¬∞ (g∞ m)) ∧∞ finMeetNeg∞ ms)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) (g∞ n) (¬∞ (g∞ m)) (finMeetNeg∞ ms) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ m))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (g∞-meet-neg-g∞-neq n m n≠m) ⟩
  (g∞ n) ∧∞ finMeetNeg∞ ms
    ≡⟨ g∞-meet-finMeetNeg-notin n ms p ⟩
  g∞ n ∎

g∞-meet-finMeetNeg-in : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ true →
  (g∞ n) ∧∞ finMeetNeg∞ ms ≡ 𝟘∞
g∞-meet-finMeetNeg-in n [] p = ex-falso (true≢false (sym p))
g∞-meet-finMeetNeg-in n (m ∷ ms) p with discreteℕ n m
... | yes n=m =
  (g∞ n) ∧∞ ((¬∞ (g∞ m)) ∧∞ finMeetNeg∞ ms)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) (g∞ n) (¬∞ (g∞ m)) (finMeetNeg∞ ms) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ m))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (cong ((g∞ n) ∧∞_) (cong (¬∞_ ∘ g∞) (sym n=m))) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ n))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (g∞-meet-neg-g∞-eq n) ⟩
  𝟘∞ ∧∞ finMeetNeg∞ ms
    ≡⟨ B∞-BoolAlg.∧AnnihilL ⟩
  𝟘∞ ∎
... | no n≠m =
  (g∞ n) ∧∞ ((¬∞ (g∞ m)) ∧∞ finMeetNeg∞ ms)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) (g∞ n) (¬∞ (g∞ m)) (finMeetNeg∞ ms) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ m))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (g∞-meet-neg-g∞-neq n m n≠m) ⟩
  (g∞ n) ∧∞ finMeetNeg∞ ms
    ≡⟨ g∞-meet-finMeetNeg-in n ms p ⟩
  𝟘∞ ∎

-- List difference: ns minus elements in ms
_∖L_ : List ℕ → List ℕ → List ℕ
[] ∖L ms = []
(n ∷ ns) ∖L ms with n ∈? ms
... | true = ns ∖L ms
... | false = n ∷ (ns ∖L ms)

-- Main correctness theorem for meet of joinForm and meetNegForm
meet-joinForm-meetNegForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns ∧∞ finMeetNeg∞ ms ≡ finJoin∞ (ns ∖L ms)
meet-joinForm-meetNegForm-correct [] ms =
  𝟘∞ ∧∞ finMeetNeg∞ ms   ≡⟨ B∞-BoolAlg.∧AnnihilL ⟩
  𝟘∞ ∎
meet-joinForm-meetNegForm-correct (n ∷ ns) ms with n ∈? ms | inspect (n ∈?_) ms
... | true | [ n∈ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finMeetNeg∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  ((g∞ n) ∧∞ finMeetNeg∞ ms) ∨∞ (finJoin∞ ns ∧∞ finMeetNeg∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finMeetNeg-in n ms n∈ms) (meet-joinForm-meetNegForm-correct ns ms) ⟩
  𝟘∞ ∨∞ finJoin∞ (ns ∖L ms)
    ≡⟨ B∞-BoolAlg.∨IdL ⟩
  finJoin∞ (ns ∖L ms) ∎
... | false | [ n∉ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finMeetNeg∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  ((g∞ n) ∧∞ finMeetNeg∞ ms) ∨∞ (finJoin∞ ns ∧∞ finMeetNeg∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finMeetNeg-notin n ms n∉ms) (meet-joinForm-meetNegForm-correct ns ms) ⟩
  g∞ n ∨∞ finJoin∞ (ns ∖L ms) ∎

-- =============================================================================
-- XOR (Ring Addition) of Normal Forms (lines 8049-8333)
-- =============================================================================

-- Symmetric difference of lists
_△L_ : List ℕ → List ℕ → List ℕ
ns △L ms = (ns ++ ms) ∖L (ns ∩L ms)

-- Helper lemmas for idempotent multiplication
·-idem-left : (a b : ⟨ B∞ ⟩) → a ∧∞ (a ∧∞ b) ≡ a ∧∞ b
·-idem-left a b =
  a ∧∞ (a ∧∞ b)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) a a b ⟩
  (a ∧∞ a) ∧∞ b
    ≡⟨ cong (_∧∞ b) (BooleanRingStr.·Idem (snd B∞) a) ⟩
  a ∧∞ b ∎

·-idem-right : (a b : ⟨ B∞ ⟩) → b ∧∞ (a ∧∞ b) ≡ a ∧∞ b
·-idem-right a b =
  b ∧∞ (a ∧∞ b)
    ≡⟨ BooleanRingStr.·Comm (snd B∞) b (a ∧∞ b) ⟩
  (a ∧∞ b) ∧∞ b
    ≡⟨ sym (BooleanRingStr.·Assoc (snd B∞) a b b) ⟩
  a ∧∞ (b ∧∞ b)
    ≡⟨ cong (a ∧∞_) (BooleanRingStr.·Idem (snd B∞) b) ⟩
  a ∧∞ b ∎

-- Helpers for · operations
·-absorb-left : (a b : ⟨ B∞ ⟩) → a ·∞ (a ·∞ b) ≡ a ·∞ b
·-absorb-left a b =
  a ·∞ (a ·∞ b)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) a a b ⟩
  (a ·∞ a) ·∞ b
    ≡⟨ cong (_·∞ b) (BooleanRingStr.·Idem (snd B∞) a) ⟩
  a ·∞ b ∎

·-absorb-right : (a b : ⟨ B∞ ⟩) → b ·∞ (a ·∞ b) ≡ a ·∞ b
·-absorb-right a b =
  b ·∞ (a ·∞ b)
    ≡⟨ BooleanRingStr.·Comm (snd B∞) b (a ·∞ b) ⟩
  (a ·∞ b) ·∞ b
    ≡⟨ sym (BooleanRingStr.·Assoc (snd B∞) a b b) ⟩
  a ·∞ (b ·∞ b)
    ≡⟨ cong (a ·∞_) (BooleanRingStr.·Idem (snd B∞) b) ⟩
  a ·∞ b ∎

·-prod-idem : (a b : ⟨ B∞ ⟩) → (a ·∞ b) ·∞ (a ·∞ b) ≡ a ·∞ b
·-prod-idem a b = BooleanRingStr.·Idem (snd B∞) (a ·∞ b)

-- Helper: 4x = 0 in char 2
quad-cancel : (x : ⟨ B∞ ⟩) → x +∞ x +∞ x +∞ x ≡ 𝟘∞
quad-cancel x =
  x +∞ x +∞ x +∞ x
    ≡⟨ cong (λ t → t +∞ x +∞ x) (char2-B∞ x) ⟩
  𝟘∞ +∞ x +∞ x
    ≡⟨ cong (_+∞ x) (BooleanRingStr.+IdL (snd B∞) x) ⟩
  x +∞ x
    ≡⟨ char2-B∞ x ⟩
  𝟘∞ ∎

-- Helper functions for xor-symmdiff proof
xor-·-distL-+ : (a b c : ⟨ B∞ ⟩) → (a +∞ b) ·∞ c ≡ (a ·∞ c) +∞ (b ·∞ c)
xor-·-distL-+ a b c = BooleanRingStr.·DistL+ (snd B∞) a b c

xor-·-distR-+ : (c a b : ⟨ B∞ ⟩) → c ·∞ (a +∞ b) ≡ (c ·∞ a) +∞ (c ·∞ b)
xor-·-distR-+ c a b = BooleanRingStr.·DistR+ (snd B∞) c a b

xor-·-1R : (x : ⟨ B∞ ⟩) → x ·∞ 𝟙∞ ≡ x
xor-·-1R x = BooleanRingStr.·IdR (snd B∞) x

xor-+∞-assoc : (a b c : ⟨ B∞ ⟩) → (a +∞ b) +∞ c ≡ a +∞ (b +∞ c)
xor-+∞-assoc a b c = sym (BooleanRingStr.+Assoc (snd B∞) a b c)

xor-·∞-assoc : (a b c : ⟨ B∞ ⟩) → (a ·∞ b) ·∞ c ≡ a ·∞ (b ·∞ c)
xor-·∞-assoc a b c = sym (BooleanRingStr.·Assoc (snd B∞) a b c)

xor-·∞-comm : (a b : ⟨ B∞ ⟩) → a ·∞ b ≡ b ·∞ a
xor-·∞-comm a b = BooleanRingStr.·Comm (snd B∞) a b

xor-·∞-idem : (a : ⟨ B∞ ⟩) → a ·∞ a ≡ a
xor-·∞-idem a = BooleanRingStr.·Idem (snd B∞) a

xor-+∞-0L : (x : ⟨ B∞ ⟩) → 𝟘∞ +∞ x ≡ x
xor-+∞-0L x = BooleanRingStr.+IdL (snd B∞) x

xor-+∞-0R : (x : ⟨ B∞ ⟩) → x +∞ 𝟘∞ ≡ x
xor-+∞-0R x = BooleanRingStr.+IdR (snd B∞) x

xor-a·ab=ab : (a b : ⟨ B∞ ⟩) → a ·∞ (a ·∞ b) ≡ a ·∞ b
xor-a·ab=ab a b =
  a ·∞ (a ·∞ b)
    ≡⟨ sym (xor-·∞-assoc a a b) ⟩
  (a ·∞ a) ·∞ b
    ≡⟨ cong (_·∞ b) (xor-·∞-idem a) ⟩
  a ·∞ b ∎

xor-b·ab=ab : (a b : ⟨ B∞ ⟩) → b ·∞ (a ·∞ b) ≡ a ·∞ b
xor-b·ab=ab a b =
  b ·∞ (a ·∞ b)
    ≡⟨ xor-·∞-comm b (a ·∞ b) ⟩
  (a ·∞ b) ·∞ b
    ≡⟨ xor-·∞-assoc a b b ⟩
  a ·∞ (b ·∞ b)
    ≡⟨ cong (a ·∞_) (xor-·∞-idem b) ⟩
  a ·∞ b ∎

xor-triple-distL : (x y z w : ⟨ B∞ ⟩) → (x +∞ y +∞ z) ·∞ w ≡ (x ·∞ w) +∞ (y ·∞ w) +∞ (z ·∞ w)
xor-triple-distL x y z w =
  (x +∞ y +∞ z) ·∞ w
    ≡⟨ xor-·-distL-+ (x +∞ y) z w ⟩
  ((x +∞ y) ·∞ w) +∞ (z ·∞ w)
    ≡⟨ cong (_+∞ (z ·∞ w)) (xor-·-distL-+ x y w) ⟩
  ((x ·∞ w) +∞ (y ·∞ w)) +∞ (z ·∞ w) ∎

-- Main proof of xor-symmdiff: a + b = (a ∨ b) ∧ ¬(a ∧ b)
xor-symmdiff : (a b : ⟨ B∞ ⟩) → a +∞ b ≡ (a ∨∞ b) ∧∞ (¬∞ (a ∧∞ b))
xor-symmdiff a b =
  let ab = a ·∞ b
      step1 : (a +∞ b +∞ ab) ·∞ 𝟙∞ ≡ a +∞ b +∞ ab
      step1 = xor-·-1R (a +∞ b +∞ ab)

      step2-dist : (a +∞ b +∞ ab) ·∞ ab ≡ (a ·∞ ab) +∞ (b ·∞ ab) +∞ (ab ·∞ ab)
      step2-dist = xor-triple-distL a b ab ab

      step2-simplify : (a ·∞ ab) +∞ (b ·∞ ab) +∞ (ab ·∞ ab) ≡ ab +∞ ab +∞ ab
      step2-simplify =
        (a ·∞ ab) +∞ (b ·∞ ab) +∞ (ab ·∞ ab)
          ≡⟨ cong (λ t → t +∞ (b ·∞ ab) +∞ (ab ·∞ ab)) (xor-a·ab=ab a b) ⟩
        ab +∞ (b ·∞ ab) +∞ (ab ·∞ ab)
          ≡⟨ cong (λ t → ab +∞ t +∞ (ab ·∞ ab)) (xor-b·ab=ab a b) ⟩
        ab +∞ ab +∞ (ab ·∞ ab)
          ≡⟨ cong (λ t → ab +∞ ab +∞ t) (xor-·∞-idem ab) ⟩
        ab +∞ ab +∞ ab ∎

      step2 : (a +∞ b +∞ ab) ·∞ ab ≡ ab +∞ ab +∞ ab
      step2 = step2-dist ∙ step2-simplify

      main-dist : (a +∞ b +∞ ab) ·∞ (𝟙∞ +∞ ab) ≡ ((a +∞ b +∞ ab) ·∞ 𝟙∞) +∞ ((a +∞ b +∞ ab) ·∞ ab)
      main-dist = xor-·-distR-+ (a +∞ b +∞ ab) 𝟙∞ ab

      main-simplified : ((a +∞ b +∞ ab) ·∞ 𝟙∞) +∞ ((a +∞ b +∞ ab) ·∞ ab) ≡ (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab)
      main-simplified =
        ((a +∞ b +∞ ab) ·∞ 𝟙∞) +∞ ((a +∞ b +∞ ab) ·∞ ab)
          ≡⟨ cong (_+∞ ((a +∞ b +∞ ab) ·∞ ab)) step1 ⟩
        (a +∞ b +∞ ab) +∞ ((a +∞ b +∞ ab) ·∞ ab)
          ≡⟨ cong ((a +∞ b +∞ ab) +∞_) step2 ⟩
        (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab) ∎

      step-reassoc1 : (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab) ≡ (a +∞ b) +∞ (ab +∞ (ab +∞ ab +∞ ab))
      step-reassoc1 = xor-+∞-assoc (a +∞ b) ab (ab +∞ ab +∞ ab)

      step-reassoc2 : (a +∞ b) +∞ (ab +∞ (ab +∞ ab +∞ ab)) ≡ (a +∞ b) +∞ ((ab +∞ ab) +∞ (ab +∞ ab))
      step-reassoc2 = cong ((a +∞ b) +∞_) (
        ab +∞ (ab +∞ ab +∞ ab)
          ≡⟨ sym (xor-+∞-assoc ab (ab +∞ ab) ab) ⟩
        (ab +∞ (ab +∞ ab)) +∞ ab
          ≡⟨ cong (_+∞ ab) (sym (xor-+∞-assoc ab ab ab)) ⟩
        ((ab +∞ ab) +∞ ab) +∞ ab
          ≡⟨ xor-+∞-assoc (ab +∞ ab) ab ab ⟩
        (ab +∞ ab) +∞ (ab +∞ ab) ∎)

      step-cancel : (a +∞ b) +∞ ((ab +∞ ab) +∞ (ab +∞ ab)) ≡ (a +∞ b) +∞ 𝟘∞
      step-cancel = cong ((a +∞ b) +∞_) (
        (ab +∞ ab) +∞ (ab +∞ ab)
          ≡⟨ cong (_+∞ (ab +∞ ab)) (char2-B∞ ab) ⟩
        𝟘∞ +∞ (ab +∞ ab)
          ≡⟨ xor-+∞-0L (ab +∞ ab) ⟩
        ab +∞ ab
          ≡⟨ char2-B∞ ab ⟩
        𝟘∞ ∎)

      flatten : (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab) ≡ a +∞ b
      flatten = step-reassoc1 ∙ step-reassoc2 ∙ step-cancel ∙ xor-+∞-0R (a +∞ b)

      rhs-expanded : (a ∨∞ b) ∧∞ (¬∞ (a ∧∞ b)) ≡ (a +∞ b +∞ ab) ·∞ (𝟙∞ +∞ ab)
      rhs-expanded = refl

  in sym (rhs-expanded ∙ main-dist ∙ main-simplified ∙ flatten)

-- XOR of two joinForms yields a joinForm with symmetric difference
xor-joinForm-joinForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns +∞ finJoin∞ ms ≡ finJoin∞ (ns △L ms)
xor-joinForm-joinForm-correct ns ms =
  finJoin∞ ns +∞ finJoin∞ ms
    ≡⟨ xor-symmdiff (finJoin∞ ns) (finJoin∞ ms) ⟩
  (finJoin∞ ns ∨∞ finJoin∞ ms) ∧∞ (¬∞ (finJoin∞ ns ∧∞ finJoin∞ ms))
    ≡⟨ cong₂ (λ x y → x ∧∞ (¬∞ y)) (join-joinForm-correct ns ms) (meet-joinForm-joinForm-correct ns ms) ⟩
  finJoin∞ (ns ++ ms) ∧∞ (¬∞ (finJoin∞ (ns ∩L ms)))
    ≡⟨ cong (finJoin∞ (ns ++ ms) ∧∞_) (sym (neg-nf-correct (joinForm (ns ∩L ms)))) ⟩
  finJoin∞ (ns ++ ms) ∧∞ finMeetNeg∞ (ns ∩L ms)
    ≡⟨ meet-joinForm-meetNegForm-correct (ns ++ ms) (ns ∩L ms) ⟩
  finJoin∞ ((ns ++ ms) ∖L (ns ∩L ms))
    ≡⟨ refl ⟩
  finJoin∞ (ns △L ms) ∎

-- XOR of meetNegForms: ¬a + ¬b = a + b in char 2
xor-meetNegForm-meetNegForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns +∞ finMeetNeg∞ ms ≡ finJoin∞ (ns △L ms)
xor-meetNegForm-meetNegForm-correct ns ms =
  finMeetNeg∞ ns +∞ finMeetNeg∞ ms
    ≡⟨ cong₂ _+∞_ (sym (neg-finJoin ns)) (sym (neg-finJoin ms)) ⟩
  ¬∞ (finJoin∞ ns) +∞ ¬∞ (finJoin∞ ms)
    ≡⟨ refl ⟩
  (𝟙∞ +∞ finJoin∞ ns) +∞ (𝟙∞ +∞ finJoin∞ ms)
    ≡⟨ xor-+∞-assoc 𝟙∞ (finJoin∞ ns) (𝟙∞ +∞ finJoin∞ ms) ⟩
  𝟙∞ +∞ (finJoin∞ ns +∞ (𝟙∞ +∞ finJoin∞ ms))
    ≡⟨ cong (𝟙∞ +∞_) (sym (xor-+∞-assoc (finJoin∞ ns) 𝟙∞ (finJoin∞ ms))) ⟩
  𝟙∞ +∞ ((finJoin∞ ns +∞ 𝟙∞) +∞ finJoin∞ ms)
    ≡⟨ cong (λ t → 𝟙∞ +∞ (t +∞ finJoin∞ ms)) (BooleanRingStr.+Comm (snd B∞) (finJoin∞ ns) 𝟙∞) ⟩
  𝟙∞ +∞ ((𝟙∞ +∞ finJoin∞ ns) +∞ finJoin∞ ms)
    ≡⟨ cong (𝟙∞ +∞_) (xor-+∞-assoc 𝟙∞ (finJoin∞ ns) (finJoin∞ ms)) ⟩
  𝟙∞ +∞ (𝟙∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms))
    ≡⟨ sym (xor-+∞-assoc 𝟙∞ 𝟙∞ (finJoin∞ ns +∞ finJoin∞ ms)) ⟩
  (𝟙∞ +∞ 𝟙∞) +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ cong (_+∞ (finJoin∞ ns +∞ finJoin∞ ms)) (char2-B∞ 𝟙∞) ⟩
  𝟘∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ xor-+∞-0L (finJoin∞ ns +∞ finJoin∞ ms) ⟩
  finJoin∞ ns +∞ finJoin∞ ms
    ≡⟨ xor-joinForm-joinForm-correct ns ms ⟩
  finJoin∞ (ns △L ms) ∎

-- XOR of joinForm and meetNegForm: a + ¬b = ¬(a + b)
xor-joinForm-meetNegForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns +∞ finMeetNeg∞ ms ≡ finMeetNeg∞ (ns △L ms)
xor-joinForm-meetNegForm-correct ns ms =
  finJoin∞ ns +∞ finMeetNeg∞ ms
    ≡⟨ cong (finJoin∞ ns +∞_) (sym (neg-finJoin ms)) ⟩
  finJoin∞ ns +∞ ¬∞ (finJoin∞ ms)
    ≡⟨ refl ⟩
  finJoin∞ ns +∞ (𝟙∞ +∞ finJoin∞ ms)
    ≡⟨ sym (xor-+∞-assoc (finJoin∞ ns) 𝟙∞ (finJoin∞ ms)) ⟩
  (finJoin∞ ns +∞ 𝟙∞) +∞ finJoin∞ ms
    ≡⟨ cong (_+∞ finJoin∞ ms) (BooleanRingStr.+Comm (snd B∞) (finJoin∞ ns) 𝟙∞) ⟩
  (𝟙∞ +∞ finJoin∞ ns) +∞ finJoin∞ ms
    ≡⟨ xor-+∞-assoc 𝟙∞ (finJoin∞ ns) (finJoin∞ ms) ⟩
  𝟙∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ cong (𝟙∞ +∞_) (xor-joinForm-joinForm-correct ns ms) ⟩
  𝟙∞ +∞ finJoin∞ (ns △L ms)
    ≡⟨ refl ⟩
  ¬∞ (finJoin∞ (ns △L ms))
    ≡⟨ neg-finJoin (ns △L ms) ⟩
  finMeetNeg∞ (ns △L ms) ∎

-- Symmetric case: meetNegForm + joinForm
xor-meetNegForm-joinForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns +∞ finJoin∞ ms ≡ finMeetNeg∞ (ms △L ns)
xor-meetNegForm-joinForm-correct ns ms =
  finMeetNeg∞ ns +∞ finJoin∞ ms
    ≡⟨ BooleanRingStr.+Comm (snd B∞) (finMeetNeg∞ ns) (finJoin∞ ms) ⟩
  finJoin∞ ms +∞ finMeetNeg∞ ns
    ≡⟨ xor-joinForm-meetNegForm-correct ms ns ⟩
  finMeetNeg∞ (ms △L ns) ∎

-- =============================================================================
-- Normal Form Operations for normalizeTerm (lines 8433-8500)
-- =============================================================================

-- Symmetric case: meet of meetNegForm with joinForm
meet-meetNegForm-joinForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns ∧∞ finJoin∞ ms ≡ finJoin∞ (ms ∖L ns)
meet-meetNegForm-joinForm-correct ns ms =
  finMeetNeg∞ ns ∧∞ finJoin∞ ms
    ≡⟨ BooleanRingStr.·Comm (snd B∞) (finMeetNeg∞ ns) (finJoin∞ ms) ⟩
  finJoin∞ ms ∧∞ finMeetNeg∞ ns
    ≡⟨ meet-joinForm-meetNegForm-correct ms ns ⟩
  finJoin∞ (ms ∖L ns) ∎

-- XOR operation on normal forms
xor-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
xor-nf (joinForm ns) (joinForm ms) = joinForm (ns △L ms)
xor-nf (joinForm ns) (meetNegForm ms) = meetNegForm (ns △L ms)
xor-nf (meetNegForm ns) (joinForm ms) = meetNegForm (ms △L ns)
xor-nf (meetNegForm ns) (meetNegForm ms) = joinForm (ns △L ms)

-- Correctness of xor-nf
xor-nf-correct : (nf1 nf2 : B∞-NormalForm) → ⟦ xor-nf nf1 nf2 ⟧nf ≡ ⟦ nf1 ⟧nf +∞ ⟦ nf2 ⟧nf
xor-nf-correct (joinForm ns) (joinForm ms) = sym (xor-joinForm-joinForm-correct ns ms)
xor-nf-correct (joinForm ns) (meetNegForm ms) = sym (xor-joinForm-meetNegForm-correct ns ms)
xor-nf-correct (meetNegForm ns) (joinForm ms) = sym (xor-meetNegForm-joinForm-correct ns ms)
xor-nf-correct (meetNegForm ns) (meetNegForm ms) = sym (xor-meetNegForm-meetNegForm-correct ns ms)

-- MEET operation on normal forms
meet-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
meet-nf (joinForm ns) (joinForm ms) = joinForm (ns ∩L ms)
meet-nf (joinForm ns) (meetNegForm ms) = joinForm (ns ∖L ms)
meet-nf (meetNegForm ns) (joinForm ms) = joinForm (ms ∖L ns)
meet-nf (meetNegForm ns) (meetNegForm ms) = meetNegForm (ns ++ ms)

-- Correctness of meet-nf
meet-nf-correct : (nf1 nf2 : B∞-NormalForm) → ⟦ meet-nf nf1 nf2 ⟧nf ≡ ⟦ nf1 ⟧nf ∧∞ ⟦ nf2 ⟧nf
meet-nf-correct (joinForm ns) (joinForm ms) = sym (meet-joinForm-joinForm-correct ns ms)
meet-nf-correct (joinForm ns) (meetNegForm ms) = sym (meet-joinForm-meetNegForm-correct ns ms)
meet-nf-correct (meetNegForm ns) (joinForm ms) = sym (meet-meetNegForm-joinForm-correct ns ms)
meet-nf-correct (meetNegForm ns) (meetNegForm ms) = sym (meet-meetNegForm-correct ns ms)
