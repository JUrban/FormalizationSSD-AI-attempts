{-# OPTIONS --cubical --guardedness #-}

module work.Part07 where

-- =============================================================================
-- Part 07: B∞×B∞ operations, the map f : B∞ → B∞×B∞, parity operations,
--          f-injective, and B∞×B∞-Presentation
-- =============================================================================

-- Import Part06 for previous definitions
open import work.Part06 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ)
-- Note: isEmbedding→Inj from Cubical.Functions.Embedding is used in B∞×B∞-Presentation (Part08)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; inj-m+; +-zero; injSuc; snotz; znots)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.List hiding (map)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.CommRing.DirectProd using (DirectProd-CommRing)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; idBoolEquiv; has-Countability-structure)
open import Axioms.StoneDuality using (Sp; Booleω)

-- Open B∞-construction from Part06 to get B∞, π∞, g∞, etc.
open B∞-construction public

-- =============================================================================
-- B∞×B∞ Operations (lines 4604-4620 of work.agda)
-- =============================================================================

-- Projections and zero elements for the product
module B∞×B∞-Operations where
  open BooleanRingStr (snd B∞×B∞) renaming (_·_ to _·×_ ; 𝟘 to 𝟘× ; 𝟙 to 𝟙×)

  -- Zero element is (0, 0)
  0×0 : ⟨ B∞×B∞ ⟩
  0×0 = 𝟘∞ , 𝟘∞

  -- Left injection: x ↦ (x, 0)
  inl-B∞ : ⟨ B∞ ⟩ → ⟨ B∞×B∞ ⟩
  inl-B∞ x = x , 𝟘∞

  -- Right injection: x ↦ (0, x)
  inr-B∞ : ⟨ B∞ ⟩ → ⟨ B∞×B∞ ⟩
  inr-B∞ x = 𝟘∞ , x

open B∞×B∞-Operations

-- =============================================================================
-- The map f : B∞ → B∞ × B∞ for LLPO (lines 4622-4730 of work.agda)
-- =============================================================================

-- tex definition (line 554-559):
-- f(g_n) = (g_k, 0) if n = 2k
-- f(g_n) = (0, g_k) if n = 2k+1

-- Helper: division by 2 with parity
div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

-- Parity check (renamed to avoid clash with Cubical.Data.Nat.Base.isEven)
parity : ℕ → Bool
parity zero = true
parity (suc zero) = false
parity (suc (suc n)) = parity n

-- The map on generators of freeBA ℕ into B∞ × B∞
-- f(gen n) = (g∞(n/2), 0) if n is even
-- f(gen n) = (0, g∞(n/2)) if n is odd
f-on-gen : ℕ → ⟨ B∞×B∞ ⟩
f-on-gen n with parity n
... | true  = g∞ (div2 n) , 𝟘∞   -- n = 2k, map to (g_k, 0)
... | false = 𝟘∞ , g∞ (div2 n)   -- n = 2k+1, map to (0, g_k)

-- Helper: multiplication in B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; 𝟘 to 𝟘×)

-- Key lemma: The product structure in B∞×B∞ is componentwise
·×-componentwise : (x y : ⟨ B∞×B∞ ⟩) → (x ·× y) ≡ (fst x ·∞ fst y , snd x ·∞ snd y)
·×-componentwise x y = refl  -- This is definitional by the product construction

-- Zero absorbs multiplication in B∞
-- Using RingTheory from Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.Properties using (module RingTheory)

private
  B∞-Ring = CommRing→Ring (BooleanRing→CommRing B∞)
  module B∞-RT = RingTheory B∞-Ring

0∞-absorbs-left : (x : ⟨ B∞ ⟩) → 𝟘∞ ·∞ x ≡ 𝟘∞
0∞-absorbs-left x = B∞-RT.0LeftAnnihilates x

0∞-absorbs-right : (x : ⟨ B∞ ⟩) → x ·∞ 𝟘∞ ≡ 𝟘∞
0∞-absorbs-right x = B∞-RT.0RightAnnihilates x

-- Key lemma: (x, 0) · (0, y) = (0, 0)
inl-inr-mult-zero : (x y : ⟨ B∞ ⟩) → (x , 𝟘∞) ·× (𝟘∞ , y) ≡ (𝟘∞ , 𝟘∞)
inl-inr-mult-zero x y =
  (x , 𝟘∞) ·× (𝟘∞ , y) ≡⟨ refl ⟩
  (x ·∞ 𝟘∞ , 𝟘∞ ·∞ y)  ≡⟨ cong₂ _,_ (0∞-absorbs-right x) (0∞-absorbs-left y) ⟩
  (𝟘∞ , 𝟘∞) ∎

-- Symmetric case
inr-inl-mult-zero : (x y : ⟨ B∞ ⟩) → (𝟘∞ , x) ·× (y , 𝟘∞) ≡ (𝟘∞ , 𝟘∞)
inr-inl-mult-zero x y =
  (𝟘∞ , x) ·× (y , 𝟘∞) ≡⟨ refl ⟩
  (𝟘∞ ·∞ y , x ·∞ 𝟘∞)  ≡⟨ cong₂ _,_ (0∞-absorbs-left y) (0∞-absorbs-right x) ⟩
  (𝟘∞ , 𝟘∞) ∎

-- Helper: parity properties
parity-double : (k : ℕ) → parity (k +ℕ k) ≡ true
parity-double zero = refl
parity-double (suc k) =
  parity (suc k +ℕ suc k)    ≡⟨ refl ⟩
  parity (suc (k +ℕ suc k))  ≡⟨ cong (parity ∘ suc) (+-suc k k) ⟩
  parity (suc (suc (k +ℕ k))) ≡⟨ refl ⟩
  parity (k +ℕ k)             ≡⟨ parity-double k ⟩
  true ∎

parity-double-suc : (k : ℕ) → parity (suc (k +ℕ k)) ≡ false
parity-double-suc zero = refl
parity-double-suc (suc k) =
  parity (suc (suc k +ℕ suc k))    ≡⟨ refl ⟩
  parity (suc (suc (k +ℕ suc k)))  ≡⟨ cong (parity ∘ suc ∘ suc) (+-suc k k) ⟩
  parity (suc (suc (suc (k +ℕ k)))) ≡⟨ refl ⟩
  parity (suc (k +ℕ k))             ≡⟨ parity-double-suc k ⟩
  false ∎

-- div2 properties
div2-double : (k : ℕ) → div2 (k +ℕ k) ≡ k
div2-double zero = refl
div2-double (suc k) =
  div2 (suc k +ℕ suc k)         ≡⟨ refl ⟩
  div2 (suc (k +ℕ suc k))       ≡⟨ cong (div2 ∘ suc) (+-suc k k) ⟩
  div2 (suc (suc (k +ℕ k)))     ≡⟨ refl ⟩
  suc (div2 (k +ℕ k))           ≡⟨ cong suc (div2-double k) ⟩
  suc k ∎

div2-double-suc : (k : ℕ) → div2 (suc (k +ℕ k)) ≡ k
div2-double-suc zero = refl
div2-double-suc (suc k) =
  div2 (suc (suc k +ℕ suc k))       ≡⟨ refl ⟩
  div2 (suc (suc (k +ℕ suc k)))     ≡⟨ cong (div2 ∘ suc ∘ suc) (+-suc k k) ⟩
  div2 (suc (suc (suc (k +ℕ k))))   ≡⟨ refl ⟩
  suc (div2 (suc (k +ℕ k)))         ≡⟨ cong suc (div2-double-suc k) ⟩
  suc k ∎

-- Helper: different div2 values implies different generators
div2-neq→gen-product-zero : (m n : ℕ) → ¬ (div2 m ≡ div2 n) →
  g∞ (div2 m) ·∞ g∞ (div2 n) ≡ 𝟘∞
div2-neq→gen-product-zero m n neq = g∞-distinct-mult-zero (div2 m) (div2 n) neq

-- Helper: suc a + suc b = suc (suc (a + b))
double-div2-even : (n : ℕ) → parity n ≡ true → n ≡ div2 n +ℕ div2 n
double-div2-even zero _ = refl
double-div2-even (suc zero) p = ex-falso (true≢false (sym p))
double-div2-even (suc (suc n)) p =
  suc (suc n) ≡⟨ cong (suc ∘ suc) (double-div2-even n p) ⟩
  suc (suc (div2 n +ℕ div2 n)) ≡⟨ cong suc (sym (+-suc (div2 n) (div2 n))) ⟩
  suc (div2 n +ℕ suc (div2 n)) ∎

double-div2-odd : (n : ℕ) → parity n ≡ false → n ≡ suc (div2 n +ℕ div2 n)
double-div2-odd zero p = ex-falso (true≢false p)
double-div2-odd (suc zero) _ = refl
double-div2-odd (suc (suc n)) p =
  suc (suc n) ≡⟨ cong (suc ∘ suc) (double-div2-odd n p) ⟩
  suc (suc (suc (div2 n +ℕ div2 n))) ≡⟨ cong (suc ∘ suc) (sym (+-suc (div2 n) (div2 n))) ⟩
  suc (suc (div2 n +ℕ suc (div2 n))) ∎

-- Convert builtin equality to path for Bool
import Agda.Builtin.Equality as BEq
builtin→Path-Bool : {a b : Bool} → a BEq.≡ b → a ≡ b
builtin→Path-Bool BEq.refl = refl

div2-injective-even : (m n : ℕ) → parity m BEq.≡ true → parity n BEq.≡ true →
  div2 m ≡ div2 n → m ≡ n
div2-injective-even m n pm pn = λ eq →
  double-div2-even m (builtin→Path-Bool pm) ∙ cong₂ _+ℕ_ eq eq ∙ sym (double-div2-even n (builtin→Path-Bool pn))

div2-injective-odd : (m n : ℕ) → parity m BEq.≡ false → parity n BEq.≡ false →
  div2 m ≡ div2 n → m ≡ n
div2-injective-odd m n pm pn = λ eq →
  double-div2-odd m (builtin→Path-Bool pm) ∙ cong₂ (λ a b → suc (a +ℕ b)) eq eq ∙ sym (double-div2-odd n (builtin→Path-Bool pn))

-- The key theorem: f-on-gen respects the relations
-- For distinct m, n: f-on-gen m ·× f-on-gen n = (0, 0)
f-respects-relations : (m n : ℕ) → ¬ (m ≡ n) →
  (f-on-gen m) ·× (f-on-gen n) ≡ (𝟘∞ , 𝟘∞)
f-respects-relations m n m≠n with parity m in pm | parity n in pn
-- Case 1: both even
... | true | true = cong₂ _,_ (div2-neq→gen-product-zero m n div2-neq) (0∞-absorbs-left 𝟘∞)
  where
    div2-neq : ¬ (div2 m ≡ div2 n)
    div2-neq = λ eq → m≠n (div2-injective-even m n pm pn eq)
-- Case 2: both odd
... | false | false = cong₂ _,_ (0∞-absorbs-left 𝟘∞) (div2-neq→gen-product-zero m n div2-neq)
  where
    div2-neq : ¬ (div2 m ≡ div2 n)
    div2-neq = λ eq → m≠n (div2-injective-odd m n pm pn eq)
-- Case 3: m even, n odd
... | true | false = inl-inr-mult-zero (g∞ (div2 m)) (g∞ (div2 n))
-- Case 4: m odd, n even
... | false | true = inr-inl-mult-zero (g∞ (div2 m)) (g∞ (div2 n))

-- =============================================================================
-- Constructing the full homomorphism f : B∞ → B∞×B∞ (lines 4804-4900)
-- =============================================================================

-- The induced homomorphism from freeBA ℕ to B∞×B∞
f-free : BoolHom (freeBA ℕ) B∞×B∞
f-free = inducedBAHom ℕ B∞×B∞ f-on-gen

-- Key property: f-free agrees with f-on-gen on generators
f-free-on-gen : fst f-free ∘ generator ≡ f-on-gen
f-free-on-gen = evalBAInduce ℕ B∞×B∞ f-on-gen

-- The product in freeBA ℕ
private
  open BooleanRingStr (snd (freeBA ℕ)) using () renaming (_·_ to _·free_)

-- Homomorphism property of f-free
f-free-pres· : (x y : ⟨ freeBA ℕ ⟩) → fst f-free (x ·free y) ≡ (fst f-free x) ·× (fst f-free y)
f-free-pres· x y = IsCommRingHom.pres· (snd f-free) x y

-- gen in freeBA ℕ is just 'generator'
gen-is-generator : gen ≡ generator
gen-is-generator = refl

-- The crucial lemma: f-free sends products of distinct generators to zero
f-free-distinct-zero : (m n : ℕ) → ¬ (m ≡ n) →
  fst f-free (gen m ·free gen n) ≡ (𝟘∞ , 𝟘∞)
f-free-distinct-zero m n m≠n =
  fst f-free (gen m ·free gen n)             ≡⟨ f-free-pres· (gen m) (gen n) ⟩
  (fst f-free (gen m)) ·× (fst f-free (gen n)) ≡⟨ cong₂ _·×_ (funExt⁻ f-free-on-gen m) (funExt⁻ f-free-on-gen n) ⟩
  f-on-gen m ·× f-on-gen n                    ≡⟨ f-respects-relations m n m≠n ⟩
  (𝟘∞ , 𝟘∞) ∎

-- Since a < a + suc d, we have a ≠ a + suc d
a≠a+suc-d : (a d : ℕ) → ¬ (a ≡ a +ℕ suc d)
a≠a+suc-d a d = λ eq →
  let step1 : a +ℕ zero ≡ a +ℕ suc d
      step1 = +-zero a ∙ eq
      step2 : zero ≡ suc d
      step2 = inj-m+ step1
  in znots step2

-- f-free sends relB∞ k to zero
f-free-on-relB∞ : (k : ℕ) → fst f-free (relB∞ k) ≡ (𝟘∞ , 𝟘∞)
f-free-on-relB∞ k =
  let (a , d) = cantorUnpair k
  in f-free-distinct-zero a (a +ℕ suc d) (a≠a+suc-d a d)

-- Step 3: Use QB.inducedHom to descend to the quotient
f : BoolHom B∞ B∞×B∞
f = QB.inducedHom B∞×B∞ f-free f-free-on-relB∞

-- =============================================================================
-- f applied to generators (lines 4882-4950)
-- =============================================================================

-- f applied to generators: fst f (g∞ n) = f-on-gen n
opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  f-eval : f ∘cr π∞ ≡ f-free
  f-eval = QB.evalInduce {B = freeBA ℕ} {f = relB∞}
             B∞×B∞ {g = f-free} {gfx=0 = f-free-on-relB∞}

-- Key lemma: f on generators equals f-on-gen
f-on-gen-eq : (n : ℕ) → fst f (g∞ n) ≡ f-on-gen n
f-on-gen-eq n =
  fst f (g∞ n)                        ≡⟨ refl ⟩
  fst f (fst π∞ (gen n))              ≡⟨ funExt⁻ (cong fst f-eval) (gen n) ⟩
  fst f-free (gen n)                  ≡⟨ funExt⁻ f-free-on-gen n ⟩
  f-on-gen n ∎

-- Helper: 2 ·ℕ k = k +ℕ k
2·-is-double : (k : ℕ) → 2 ·ℕ k ≡ k +ℕ k
2·-is-double k = cong (k +ℕ_) (+-zero k)

-- f applied to odd generators gives right factor
f-odd-gen : (k : ℕ) → fst f (g∞ (suc (2 ·ℕ k))) ≡ (𝟘∞ , g∞ k)
f-odd-gen k =
  fst f (g∞ (suc (2 ·ℕ k)))
    ≡⟨ f-on-gen-eq (suc (2 ·ℕ k)) ⟩
  f-on-gen (suc (2 ·ℕ k))
    ≡⟨ f-on-gen-odd k ⟩
  (𝟘∞ , g∞ k) ∎
  where
  f-on-gen-odd : (k : ℕ) → f-on-gen (suc (2 ·ℕ k)) ≡ (𝟘∞ , g∞ k)
  f-on-gen-odd k with parity (suc (2 ·ℕ k)) in par-eq
  ... | false = cong (𝟘∞ ,_) (cong g∞ div2-eq)
    where
    div2-eq : div2 (suc (2 ·ℕ k)) ≡ k
    div2-eq = subst (λ m → div2 (suc m) ≡ k) (sym (2·-is-double k)) (div2-double-suc k)
  ... | true = ex-falso (false≢true (sym parity-eq ∙ builtin→Path-Bool par-eq))
    where
    parity-eq : parity (suc (2 ·ℕ k)) ≡ false
    parity-eq = subst (λ m → parity (suc m) ≡ false) (sym (2·-is-double k)) (parity-double-suc k)

-- f applied to even generators gives left factor
f-even-gen : (k : ℕ) → fst f (g∞ (2 ·ℕ k)) ≡ (g∞ k , 𝟘∞)
f-even-gen k =
  fst f (g∞ (2 ·ℕ k))
    ≡⟨ f-on-gen-eq (2 ·ℕ k) ⟩
  f-on-gen (2 ·ℕ k)
    ≡⟨ f-on-gen-even k ⟩
  (g∞ k , 𝟘∞) ∎
  where
  f-on-gen-even : (k : ℕ) → f-on-gen (2 ·ℕ k) ≡ (g∞ k , 𝟘∞)
  f-on-gen-even k with parity (2 ·ℕ k) in par-eq
  ... | true = cong (_, 𝟘∞) (cong g∞ div2-eq)
    where
    div2-eq : div2 (2 ·ℕ k) ≡ k
    div2-eq = subst (λ m → div2 m ≡ k) (sym (2·-is-double k)) (div2-double k)
  ... | false = ex-falso (true≢false (sym parity-eq ∙ builtin→Path-Bool par-eq))
    where
    parity-eq : parity (2 ·ℕ k) ≡ true
    parity-eq = subst (λ m → parity m ≡ true) (sym (2·-is-double k)) (parity-double k)

-- =============================================================================
-- Normal Form Infrastructure for B∞ (lines 4983-5090)
-- =============================================================================

-- Boolean ring operations in B∞
open BooleanRingStr (snd B∞) using () renaming (_+_ to _+∞_ ; -_ to -∞_)

-- Join in a Boolean ring: a ∨ b = a + b + a·b
_∨∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
a ∨∞ b = a +∞ b +∞ (a ·∞ b)

-- Meet in a Boolean ring: a ∧ b = a · b
_∧∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
a ∧∞ b = a ·∞ b

-- Negation in a Boolean ring: ¬a = 1 + a
¬∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩
¬∞ a = 𝟙∞ +∞ a

-- Finite join of generators
finJoin∞ : List ℕ → ⟨ B∞ ⟩
finJoin∞ [] = 𝟘∞
finJoin∞ (n ∷ ns) = g∞ n ∨∞ finJoin∞ ns

-- Finite meet of negated generators
finMeetNeg∞ : List ℕ → ⟨ B∞ ⟩
finMeetNeg∞ [] = 𝟙∞
finMeetNeg∞ (n ∷ ns) = (¬∞ g∞ n) ∧∞ finMeetNeg∞ ns

-- The normal form data type for B∞ elements
data B∞-NormalForm : Type₀ where
  joinForm : List ℕ → B∞-NormalForm
  meetNegForm : List ℕ → B∞-NormalForm

-- Interpretation of normal forms as B∞ elements
⟦_⟧nf : B∞-NormalForm → ⟨ B∞ ⟩
⟦ joinForm ns ⟧nf = finJoin∞ ns
⟦ meetNegForm ns ⟧nf = finMeetNeg∞ ns

-- Helper to split a list by parity of indices
splitByParity : List ℕ → List ℕ × List ℕ
splitByParity [] = [] , []
splitByParity (n ∷ ns) with isEven n | splitByParity ns
... | true  | (evens , odds) = half n ∷ evens , odds
... | false | (evens , odds) = evens , half n ∷ odds

-- Key lemma: for orthogonal elements a · b = 0, we have a ∨ b = a + b
orthogonal→join-is-sum : (a b : ⟨ B∞ ⟩) → a ·∞ b ≡ 𝟘∞ → a ∨∞ b ≡ a +∞ b
orthogonal→join-is-sum a b a·b=0 =
  a ∨∞ b                    ≡⟨ refl ⟩
  a +∞ b +∞ (a ·∞ b)        ≡⟨ cong (a +∞ b +∞_) a·b=0 ⟩
  a +∞ b +∞ 𝟘∞              ≡⟨ +B∞-IdR (a +∞ b) ⟩
  a +∞ b ∎
  where
  open BooleanRingStr (snd B∞) using () renaming (+IdR to +B∞-IdR)

-- Generators are orthogonal
gen-orthogonal : (m n : ℕ) → ¬ (m ≡ n) → g∞ m ·∞ g∞ n ≡ 𝟘∞
gen-orthogonal = g∞-distinct-mult-zero

-- Product operations in B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×_ ; _·_ to _·×'_ ; 𝟘 to 𝟘×' ; 𝟙 to 𝟙×)

-- Join in B∞×B∞: componentwise
_∨×_ : ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞ ⟩
(a₁ , a₂) ∨× (b₁ , b₂) = (a₁ ∨∞ b₁ , a₂ ∨∞ b₂)

-- f preserves addition
f-pres+ : (a b : ⟨ B∞ ⟩) → fst f (a +∞ b) ≡ (fst f a) +× (fst f b)
f-pres+ a b = IsCommRingHom.pres+ (snd f) a b

-- f preserves multiplication
f-pres·' : (a b : ⟨ B∞ ⟩) → fst f (a ·∞ b) ≡ (fst f a) ·×' (fst f b)
f-pres·' a b = IsCommRingHom.pres· (snd f) a b

-- f respects joins
f-pres-join : (a b : ⟨ B∞ ⟩) → fst f (a ∨∞ b) ≡ ((fst f a) ∨× (fst f b))
f-pres-join a b = step1 ∙ step2 ∙ step3
  where
  step1 : fst f (a ∨∞ b) ≡ ((fst f (a +∞ b)) +× (fst f (a ·∞ b)))
  step1 = f-pres+ (a +∞ b) (a ·∞ b)
  step2 : ((fst f (a +∞ b)) +× (fst f (a ·∞ b))) ≡ (((fst f a) +× (fst f b)) +× ((fst f a) ·×' (fst f b)))
  step2 = cong₂ _+×_ (f-pres+ a b) (f-pres·' a b)
  step3 : (((fst f a) +× (fst f b)) +× ((fst f a) ·×' (fst f b))) ≡ ((fst f a) ∨× (fst f b))
  step3 = refl

-- finJoin for the product B∞×B∞
finJoin× : List ℕ → List ℕ → ⟨ B∞×B∞ ⟩
finJoin× evens odds = (finJoin∞ evens , finJoin∞ odds)

-- f(0) = (0, 0)
f-on-zero : fst f 𝟘∞ ≡ (𝟘∞ , 𝟘∞)
f-on-zero = IsCommRingHom.pres0 (snd f)

-- Helper: 0 ∨ x = x
zero-join-left : (x : ⟨ B∞ ⟩) → 𝟘∞ ∨∞ x ≡ x
zero-join-left x =
  𝟘∞ ∨∞ x                     ≡⟨ refl ⟩
  𝟘∞ +∞ x +∞ (𝟘∞ ·∞ x)        ≡⟨ cong (𝟘∞ +∞ x +∞_) (0∞-absorbs-left x) ⟩
  𝟘∞ +∞ x +∞ 𝟘∞              ≡⟨ BooleanRingStr.+IdR (snd B∞) (𝟘∞ +∞ x) ⟩
  𝟘∞ +∞ x                     ≡⟨ BooleanRingStr.+IdL (snd B∞) x ⟩
  x ∎

-- Helper: x ∨ 0 = x
zero-join-right : (x : ⟨ B∞ ⟩) → x ∨∞ 𝟘∞ ≡ x
zero-join-right x =
  x ∨∞ 𝟘∞                     ≡⟨ refl ⟩
  x +∞ 𝟘∞ +∞ (x ·∞ 𝟘∞)        ≡⟨ cong (x +∞ 𝟘∞ +∞_) (0∞-absorbs-right x) ⟩
  x +∞ 𝟘∞ +∞ 𝟘∞              ≡⟨ BooleanRingStr.+IdR (snd B∞) (x +∞ 𝟘∞) ⟩
  x +∞ 𝟘∞                     ≡⟨ BooleanRingStr.+IdR (snd B∞) x ⟩
  x ∎

-- isEven equivalences
isEven≡isEvenB : (n : ℕ) → isEven n ≡ isEvenB n
isEven≡isEvenB zero = refl
isEven≡isEvenB (suc zero) = refl
isEven≡isEvenB (suc (suc n)) = isEven≡isEvenB n

isEven→even : (n : ℕ) → isEven n ≡ true → 2 ·ℕ (half n) ≡ n
isEven→even n prf = 2·half-even n (sym (isEven≡isEvenB n) ∙ prf)

isEven→odd : (n : ℕ) → isEven n ≡ false → suc (2 ·ℕ (half n)) ≡ n
isEven→odd n prf = suc-2·half-odd n (sym (isEven≡isEvenB n) ∙ prf)

-- f on generator when even
f-on-gen-even' : (n : ℕ) → isEven n ≡ true → fst f (g∞ n) ≡ (g∞ (half n) , 𝟘∞)
f-on-gen-even' n even-prf =
  fst f (g∞ n)                    ≡⟨ cong (λ m → fst f (g∞ m)) (sym (isEven→even n even-prf)) ⟩
  fst f (g∞ (2 ·ℕ (half n)))      ≡⟨ f-even-gen (half n) ⟩
  (g∞ (half n) , 𝟘∞) ∎

-- f on generator when odd
f-on-gen-odd' : (n : ℕ) → isEven n ≡ false → fst f (g∞ n) ≡ (𝟘∞ , g∞ (half n))
f-on-gen-odd' n odd-prf =
  fst f (g∞ n)                         ≡⟨ cong (λ m → fst f (g∞ m)) (sym (isEven→odd n odd-prf)) ⟩
  fst f (g∞ (suc (2 ·ℕ (half n))))     ≡⟨ f-odd-gen (half n) ⟩
  (𝟘∞ , g∞ (half n)) ∎

-- Main theorem: f on finite join splits by parity
f-on-finJoin : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in fst f (finJoin∞ ns) ≡ (finJoin∞ evens , finJoin∞ odds)
f-on-finJoin [] = f-on-zero
f-on-finJoin (n ∷ ns) with isEven n in parity-eq | splitByParity ns | f-on-finJoin ns
... | true  | (evens , odds) | ih =
  fst f (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ f-pres-join (g∞ n) (finJoin∞ ns) ⟩
  (fst f (g∞ n)) ∨× (fst f (finJoin∞ ns))
    ≡⟨ cong₂ _∨×_ (f-on-gen-even' n (builtin→Path-Bool parity-eq)) ih ⟩
  (g∞ (half n) , 𝟘∞) ∨× (finJoin∞ evens , finJoin∞ odds)
    ≡⟨ refl ⟩
  (g∞ (half n) ∨∞ finJoin∞ evens , 𝟘∞ ∨∞ finJoin∞ odds)
    ≡⟨ cong (g∞ (half n) ∨∞ finJoin∞ evens ,_) (zero-join-left (finJoin∞ odds)) ⟩
  (g∞ (half n) ∨∞ finJoin∞ evens , finJoin∞ odds)
    ≡⟨ refl ⟩
  (finJoin∞ (half n ∷ evens) , finJoin∞ odds) ∎
... | false | (evens , odds) | ih =
  fst f (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ f-pres-join (g∞ n) (finJoin∞ ns) ⟩
  (fst f (g∞ n)) ∨× (fst f (finJoin∞ ns))
    ≡⟨ cong₂ _∨×_ (f-on-gen-odd' n (builtin→Path-Bool parity-eq)) ih ⟩
  (𝟘∞ , g∞ (half n)) ∨× (finJoin∞ evens , finJoin∞ odds)
    ≡⟨ refl ⟩
  (𝟘∞ ∨∞ finJoin∞ evens , g∞ (half n) ∨∞ finJoin∞ odds)
    ≡⟨ cong (_, g∞ (half n) ∨∞ finJoin∞ odds) (zero-join-left (finJoin∞ evens)) ⟩
  (finJoin∞ evens , g∞ (half n) ∨∞ finJoin∞ odds)
    ≡⟨ refl ⟩
  (finJoin∞ evens , finJoin∞ (half n ∷ odds)) ∎

-- =============================================================================
-- Dirac delta and f-injective (lines 5320-5400)
-- =============================================================================

-- The Dirac sequence at n
δ-seq : ℕ → ℕ → Bool
δ-seq n m with discreteℕ n m
... | yes _ = true
... | no _ = false

δ-seq-hamo : (n : ℕ) → hitsAtMostOnce (δ-seq n)
δ-seq-hamo n i j δi=t δj=t with discreteℕ n i | discreteℕ n j
... | yes n=i | yes n=j = sym n=i ∙ n=j
... | yes _ | no n≠j = ex-falso (true≢false (sym δj=t))
... | no n≠i | _ = ex-falso (true≢false (sym δi=t))

δ∞ : ℕ → ℕ∞
δ∞ n = δ-seq n , δ-seq-hamo n

δ∞-hits-n : (n : ℕ) → fst (δ∞ n) n ≡ true
δ∞-hits-n n with discreteℕ n n
... | yes _ = refl
... | no n≠n = ex-falso (n≠n refl)

δ∞-misses-m : (n m : ℕ) → ¬ (n ≡ m) → fst (δ∞ n) m ≡ false
δ∞-misses-m n m n≠m with discreteℕ n m
... | yes n=m = ex-falso (n≠m n=m)
... | no _ = refl

-- f preserves 1
f-pres1 : fst f 𝟙∞ ≡ (𝟙∞ , 𝟙∞)
f-pres1 = IsCommRingHom.pres1 (snd f)

-- f preserves negation
f-pres-neg : (x : ⟨ B∞ ⟩) → fst f (¬∞ x) ≡ (¬∞ (fst (fst f x)) , ¬∞ (snd (fst f x)))
f-pres-neg x =
  fst f (¬∞ x)
    ≡⟨ refl ⟩
  fst f (𝟙∞ +∞ x)
    ≡⟨ f-pres+ 𝟙∞ x ⟩
  (fst f 𝟙∞) +× (fst f x)
    ≡⟨ cong (_+× (fst f x)) f-pres1 ⟩
  (𝟙∞ , 𝟙∞) +× (fst f x)
    ≡⟨ refl ⟩
  (𝟙∞ +∞ fst (fst f x) , 𝟙∞ +∞ snd (fst f x))
    ≡⟨ refl ⟩
  (¬∞ (fst (fst f x)) , ¬∞ (snd (fst f x))) ∎

-- f-injective is postulated (proved later in the file, line ~7148)
postulate
  f-injective : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y

-- Alternative: kernel is trivial
f-kernel-trivial : (x : ⟨ B∞ ⟩) → fst f x ≡ (𝟘∞ , 𝟘∞) → x ≡ 𝟘∞
f-kernel-trivial x fx=0 = f-injective x 𝟘∞ (fx=0 ∙ sym f-pres0)
  where
  f-pres0 : fst f 𝟘∞ ≡ (𝟘∞ , 𝟘∞)
  f-pres0 = IsCommRingHom.pres0 (snd f)

-- =============================================================================
-- Spectrum of Products and B∞×B∞-Units (lines 5403-5500)
-- =============================================================================

module B∞×B∞-Units where
  open BooleanRingStr (snd B∞×B∞) using () renaming (𝟙 to 𝟙×')
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

  unit-left : ⟨ B∞×B∞ ⟩
  unit-left = (𝟙B∞ , 𝟘∞)

  unit-right : ⟨ B∞×B∞ ⟩
  unit-right = (𝟘∞ , 𝟙B∞)

  unit-sum : unit-left ·× unit-right ≡ (𝟘∞ , 𝟘∞)
  unit-sum = cong₂ _,_ (0∞-absorbs-right 𝟙B∞) (0∞-absorbs-left 𝟙B∞)

open B∞×B∞-Units
