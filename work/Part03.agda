{-# OPTIONS --cubical --guardedness #-}

module work.Part03 where

open import work.Part02 public

-- Additional imports needed for this part
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.DirectProd using (DirectProd-CommRing)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Bool using (Bool; true; false; _and_; true≢false; false≢true; isSetBool)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; idBoolEquiv; has-Countability-structure)
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

-- =============================================================================
-- Part 03: work.agda lines 3744-4118 (B∞-construction, DirectProd)
-- =============================================================================

module B∞-construction where
  open import BooleanRing.FreeBooleanRing.FreeBool using (generator)
  open BooleanRingStr (snd (freeBA ℕ)) using (_·_ ; 𝟘)

  -- The generator function embeds ℕ into freeBA ℕ
  gen : ℕ → ⟨ freeBA ℕ ⟩
  gen = generator

  -- The relation generator: for k : ℕ, decode to (m, n) and produce g_m · g_n
  -- We need m ≠ n, so we interpret k as indexing pairs with m < n
  -- Using cantorUnpair k = (m, n), we use (m, m + suc n) to ensure distinct indices

  -- Given a pair (m, d) where d > 0, produce g_m · g_{m + d}
  -- This ensures the two generators are always distinct
  relB∞-from-pair : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  relB∞-from-pair (m , n) = gen m · gen (m +ℕ suc n)

  -- The relation function: k ↦ g_m · g_{m + n + 1} where cantorUnpair k = (m, n)
  relB∞ : ℕ → ⟨ freeBA ℕ ⟩
  relB∞ k = relB∞-from-pair (cantorUnpair k)

  -- B_∞ is the quotient of freeBA ℕ by these relations
  B∞ : BooleanRing ℓ-zero
  B∞ = freeBA ℕ QB./Im relB∞

  -- The quotient map π_∞ : freeBA ℕ → B_∞
  π∞ : BoolHom (freeBA ℕ) B∞
  π∞ = QB.quotientImageHom

  -- The generators g_n in B_∞
  g∞ : ℕ → ⟨ B∞ ⟩
  g∞ n = fst π∞ (gen n)

  -- Key property: g∞ m · g∞ n = 0 when m ≠ n
  -- This is what the relations enforce. We need to show this holds.

  -- First, we show that the relation relB∞ k = 0 in B∞ (by construction)
  relB∞-is-zero : (k : ℕ) → fst π∞ (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞)
  relB∞-is-zero k = QB.zeroOnImage {B = freeBA ℕ} {f = relB∞} k

  -- The key property: for any two distinct generators, their product is 0 in B∞
  -- We need: for any m < n, there exists k such that cantorUnpair k codes a pair giving g_m · g_n

  -- Actually, it's easier to show: for m and offset d, (m, m + suc d) is a relation
  -- We need to show that given m and n with m < n, we can find a k encoding this.

  -- Helper: given m and d, find k such that cantorUnpair k = (m, d)
  -- This requires cantorPair, the inverse of cantorUnpair

  -- For now, we'll work with the weaker statement that g_m · g_{m+suc d} = 0
  -- This covers all pairs (m, n) with m < n by taking d = n - m - 1

  -- The product in B∞ comes from the quotient ring structure
  open BooleanRingStr (snd B∞) renaming (_·_ to _·∞_ ; 𝟘 to 𝟘∞ ; 𝟙 to 𝟙∞)

-- B∞ is in Booleω (it's a quotient of freeBA ℕ)
-- has-Boole-ω' B∞ holds because relB∞ : ℕ → ⟨ freeBA ℕ ⟩ is the presentation

open B∞-construction public

-- Re-open BooleanRingStr for freeBA ℕ to get _·_ in scope
open BooleanRingStr (snd (freeBA ℕ)) using (_·_ ; 𝟘) public

-- Re-open BooleanRingStr for B∞ to get _·∞_ and 𝟘∞ in scope
open BooleanRingStr (snd B∞) renaming (_·_ to _·∞_ ; 𝟘 to 𝟘∞ ; 𝟙 to 𝟙∞) public

-- The presentation witness for B∞
B∞-has-Boole-ω' : has-Boole-ω' B∞
B∞-has-Boole-ω' = relB∞ , idBoolEquiv B∞

B∞-Booleω : Booleω
B∞-Booleω = B∞ , ∣ B∞-has-Boole-ω' ∣₁

-- =============================================================================
-- Section 20: Spectrum of B∞ and LLPO proof structure
-- =============================================================================

-- Sp(B∞) = BoolHom B∞ BoolBR
-- A homomorphism h : B∞ → 2 is determined by h(g∞ n) for each n
-- The relations g∞ m ·∞ g∞ n = 0∞ for m ≠ n mean:
--   h(g∞ m) · h(g∞ n) = 0, i.e., both can't be 1 simultaneously
-- So h corresponds to a sequence hitting 1 at most once, i.e., an element of ℕ∞

-- The key insight: Sp(B∞) ≅ ℕ∞ is a fundamental property of B∞

-- Forward direction: BoolHom B∞ BoolBR → ℕ∞
-- Given h : B∞ → 2, the sequence (h(g∞ n))_n hits 1 at most once
SpB∞-to-ℕ∞-seq : Sp B∞-Booleω → binarySequence
SpB∞-to-ℕ∞-seq h n = h $cr (g∞ n)

-- We need to show this sequence hits at most once
-- This follows from h preserving multiplication and the relations in B∞

-- The proof that h(g∞ m) and h(g∞ n) can't both be true for m ≠ n
-- requires showing that g∞ m ·∞ g∞ n = 0∞ in B∞
-- which comes from the quotient structure

-- Key lemma: The product of distinct generators in B∞ is zero
-- g∞ m ·∞ g∞ n = 0∞ when m ≠ n
--
-- Proof outline:
-- The quotient map π∞ is a ring homomorphism, so:
--   g∞ m ·∞ g∞ n = π∞(gen m) ·∞ π∞(gen n) = π∞(gen m · gen n)
-- We need to show gen m · gen n is in the ideal, i.e., equals relB∞ k for some k
-- By construction, relB∞ maps k to gen a · gen (a + suc d) where (a, d) = cantorUnpair k
-- For m < n, take a = m and d = n - m - 1, then gen m · gen n is in the ideal

-- To prove the homomorphism property, we need:
-- 1. g∞ m ·∞ g∞ n = 0∞ for distinct m, n (follows from quotient structure)
-- 2. h preserves multiplication (h is a BoolHom)
-- 3. Derive contradiction from h(g∞ m) = h(g∞ n) = true

-- The key property: distinct generators multiply to zero in B∞
-- Proof: for a < b, we have gen a · gen b = relB∞ k for k = cantorPair a (b - a - 1)
-- π∞ preserves multiplication, so g∞ a ·∞ g∞ b = π∞(gen a · gen b)
-- Since gen a · gen b is in the ideal, this equals 0

-- Helper: a + (suc d) with d = b - a - 1 gives b when a < b
-- We need: a + suc (b - suc a) = b
-- Proof: a + suc d = suc (a + d) = suc (d + a) = d + suc a = (b - suc a) + suc a = b
a+suc-d≡b : (a b : ℕ) → a < b → a +ℕ suc (b ∸ suc a) ≡ b
a+suc-d≡b a b a<b =
  let d = b ∸ suc a in
  a +ℕ suc d             ≡⟨ +-suc a d ⟩
  suc (a +ℕ d)           ≡⟨ cong suc (+-comm a d) ⟩
  suc (d +ℕ a)           ≡⟨ sym (+-suc d a) ⟩
  d +ℕ suc a             ≡⟨ ∸+-cancel b (suc a) a<b ⟩
  b ∎

-- relB∞ encodes products of distinct generators
-- relB∞ (cantorPair a d) = gen a · gen (a + suc d)
relB∞-encodes : (a d : ℕ) → relB∞ (cantorPair a d) ≡ gen a · gen (a +ℕ suc d)
relB∞-encodes a d =
  relB∞ (cantorPair a d)                          ≡⟨ refl ⟩
  relB∞-from-pair (cantorUnpair (cantorPair a d)) ≡⟨ cong relB∞-from-pair (cantorUnpair-pair a d) ⟩
  relB∞-from-pair (a , d)                         ≡⟨ refl ⟩
  gen a · gen (a +ℕ suc d)                        ∎

-- π∞ preserves multiplication (it's a ring hom)
open IsCommRingHom (snd π∞) renaming (pres· to π∞-pres·)

-- Commutativity in freeBA ℕ
open BooleanRingStr (snd (freeBA ℕ)) using () renaming (·Comm to free-·Comm)

-- For a < b, show gen a · gen b maps to 0 in B∞
g∞-lt-mult-zero : (a b : ℕ) → a < b → g∞ a ·∞ g∞ b ≡ 𝟘∞
g∞-lt-mult-zero a b a<b =
  let d = b ∸ suc a
      k = cantorPair a d
      eq1 : gen a · gen b ≡ gen a · gen (a +ℕ suc d)
      eq1 = cong (λ x → gen a · gen x) (sym (a+suc-d≡b a b a<b))
      eq2 : relB∞ k ≡ gen a · gen (a +ℕ suc d)
      eq2 = relB∞-encodes a d
      eq3 : gen a · gen b ≡ relB∞ k
      eq3 = eq1 ∙ sym eq2
  in
  g∞ a ·∞ g∞ b                        ≡⟨ refl ⟩
  fst π∞ (gen a) ·∞ fst π∞ (gen b)    ≡⟨ sym (π∞-pres· (gen a) (gen b)) ⟩
  fst π∞ (gen a · gen b)              ≡⟨ cong (fst π∞) eq3 ⟩
  fst π∞ (relB∞ k)                    ≡⟨ relB∞-is-zero k ⟩
  𝟘∞ ∎

-- Main theorem: distinct generators multiply to zero
g∞-distinct-mult-zero : (m n : ℕ) → ¬ (m ≡ n) →
  BooleanRingStr._·_ (snd B∞) (g∞ m) (g∞ n) ≡ BooleanRingStr.𝟘 (snd B∞)
g∞-distinct-mult-zero m n m≠n with Cubical.Data.Nat.Order.<Dec m n
... | yes m<n = g∞-lt-mult-zero m n m<n
... | no ¬m<n with Cubical.Data.Nat.Order.<Dec n m
...   | yes n<m =
        -- g∞ m ·∞ g∞ n = g∞ n ·∞ g∞ m (commutativity in B∞)
        let comm : g∞ m ·∞ g∞ n ≡ g∞ n ·∞ g∞ m
            comm = BooleanRingStr.·Comm (snd B∞) (g∞ m) (g∞ n)
        in comm ∙ g∞-lt-mult-zero n m n<m
...   | no ¬n<m =
        -- If ¬(m < n) and ¬(n < m), then m = n, contradicting m ≠ n
        -- ≮→≥ ¬m<n : n ≤ m (from ¬(m < n))
        -- ≮→≥ ¬n<m : m ≤ n (from ¬(n < m))
        -- ≤-antisym (n ≤ m) (m ≤ n) : n ≡ m
        let n≤m : n ≤ m
            n≤m = ≮→≥ ¬m<n
            m≤n : m ≤ n
            m≤n = ≮→≥ ¬n<m
            n≡m : n ≡ m
            n≡m = ≤-antisym n≤m m≤n
            m≡n : m ≡ n
            m≡n = sym n≡m
        in ex-falso (m≠n m≡n)
  where
  -- ¬(a < b) implies b ≤ a
  ≮→≥ : {a b : ℕ} → ¬ (a < b) → b ≤ a
  ≮→≥ {zero} {zero} _ = ≤-refl
  ≮→≥ {zero} {suc b} ¬0<sb = ex-falso (¬0<sb (suc-≤-suc zero-≤))
  ≮→≥ {suc a} {zero} _ = zero-≤
  ≮→≥ {suc a} {suc b} ¬sa<sb = suc-≤-suc (≮→≥ (λ a<b → ¬sa<sb (suc-≤-suc a<b)))

-- The homomorphism property shows the sequence hits at most once
SpB∞-seq-atMostOnce : (h : Sp B∞-Booleω) → hitsAtMostOnce (SpB∞-to-ℕ∞-seq h)
SpB∞-seq-atMostOnce h m n hm=true hn=true = m=n
  where
  -- Note: _·∞_ and 𝟘∞ are already in scope from the public open at line 3548
  open IsCommRingHom (snd h)

  -- h preserves multiplication
  h-pres· : (a b : ⟨ B∞ ⟩) → h $cr (a ·∞ b) ≡ (h $cr a) and (h $cr b)
  h-pres· = pres·

  -- If m ≠ n, then g∞ m ·∞ g∞ n = 0∞
  -- So h(g∞ m ·∞ g∞ n) = h(0∞) = false
  -- But h preserves multiplication, so h(g∞ m) and h(g∞ n) = false
  -- This contradicts hm=true and hn=true (since true and true = true ≠ false)

  m=n : m ≡ n
  m=n with discreteℕ m n
  ... | yes p = p
  ... | no m≠n =
    let
      -- g∞ m ·∞ g∞ n = 0∞ (by g∞-distinct-mult-zero)
      mult-zero : g∞ m ·∞ g∞ n ≡ 𝟘∞
      mult-zero = g∞-distinct-mult-zero m n m≠n

      -- h(g∞ m ·∞ g∞ n) = h(0∞) = false (h preserves 0)
      h-mult : h $cr (g∞ m ·∞ g∞ n) ≡ false
      h-mult = cong (h $cr_) mult-zero ∙ IsCommRingHom.pres0 (snd h)

      -- h(g∞ m) and h(g∞ n) = h(g∞ m ·∞ g∞ n) (h preserves ·)
      h-and-eq : (h $cr (g∞ m)) and (h $cr (g∞ n)) ≡ h $cr (g∞ m ·∞ g∞ n)
      h-and-eq = sym (h-pres· (g∞ m) (g∞ n))

      -- Combined: (h $cr g∞ m) and (h $cr g∞ n) = false
      and-is-false : (h $cr (g∞ m)) and (h $cr (g∞ n)) ≡ false
      and-is-false = h-and-eq ∙ h-mult

      -- But hm=true and hn=true, so true and true should be true
      -- Build: true = true and true = (h $cr g∞ m) and (h $cr g∞ n) = false
      step1 : true and true ≡ (h $cr (g∞ m)) and (h $cr (g∞ n))
      step1 = cong₂ _and_ (sym hm=true) (sym hn=true)

      contradiction : true ≡ false
      contradiction = step1 ∙ and-is-false
    in ex-falso (true≢false contradiction)

-- Note: g∞-distinct-mult-zero is now fully proven (lines 3657-3680 above)

-- Now we can define the full conversion from Sp(B∞) to ℕ∞
SpB∞-to-ℕ∞ : Sp B∞-Booleω → ℕ∞
SpB∞-to-ℕ∞ h = SpB∞-to-ℕ∞-seq h , SpB∞-seq-atMostOnce h

-- This gives us the forward direction of Sp(B∞) ≅ ℕ∞
-- The backward direction would construct a BoolHom B∞ BoolBR from α : ℕ∞
-- This uses the universal property of quotients

-- =============================================================================
-- Direct Product of Boolean Rings
-- =============================================================================

-- A direct product of commutative rings is a Boolean ring if both factors are
module DirectProd-BooleanRing
  (A : BooleanRing ℓ-zero)
  (B : BooleanRing ℓ-zero)
  where

  -- The underlying commutative ring product
  private
    A-CR = BooleanRing→CommRing A
    B-CR = BooleanRing→CommRing B
    AB-CR = DirectProd-CommRing A-CR B-CR

  -- The key property: idempotence is preserved componentwise
  ·Idem-prod : (x : ⟨ A ⟩ × ⟨ B ⟩) →
    CommRingStr._·_ (snd AB-CR) x x ≡ x
  ·Idem-prod (a , b) =
    let open BooleanRingStr
        open CommRingStr (snd AB-CR)
    in cong₂ _,_ (BooleanRingStr.·Idem (snd A) a) (BooleanRingStr.·Idem (snd B) b)

  -- Convert commutative ring with idempotence to Boolean ring
  DirectProd-BooleanRing : BooleanRing ℓ-zero
  DirectProd-BooleanRing = idemCommRing→BR AB-CR ·Idem-prod

-- Convenient notation
_×BR_ : BooleanRing ℓ-zero → BooleanRing ℓ-zero → BooleanRing ℓ-zero
A ×BR B = DirectProd-BooleanRing.DirectProd-BooleanRing A B

-- B∞ × B∞ as a Boolean ring
B∞×B∞ : BooleanRing ℓ-zero
B∞×B∞ = B∞ ×BR B∞

-- =============================================================================
-- BoolBR × BoolBR: Product of the 2-element Boolean ring with itself
-- =============================================================================
-- This is a 4-element Boolean ring: {(0,0), (0,1), (1,0), (1,1)}
-- Its spectrum Sp(BoolBR × BoolBR) has exactly 2 elements: the projections π₁ and π₂
-- Therefore Sp(BoolBR × BoolBR) ≃ Bool

-- The product Boolean ring BoolBR × BoolBR
Bool² : BooleanRing ℓ-zero
Bool² = BoolBR ×BR BoolBR

-- Unit elements for the product (idempotents that sum to 1)
Bool²-unit-left : ⟨ Bool² ⟩
Bool²-unit-left = true , false

Bool²-unit-right : ⟨ Bool² ⟩
Bool²-unit-right = false , true

-- =============================================================================
-- Proof that Bool² = BoolBR × BoolBR is Booleω
-- =============================================================================
-- Strategy: Bool² ≅ freeBA Bool (free Boolean ring on 2 generators)
-- Since Bool is countable, freeBA Bool is Booleω by replacementFreeOnCountable
-- Therefore Bool² is Booleω

-- Step 1: Bool has a countability structure (Bool ≅ Fin 2)
countBool : has-Countability-structure Bool
countBool = α , iso fun' inv' sec' ret'
  where
  -- α n = true iff n = 0 or n = 1 (encodes {0,1} ⊆ ℕ)
  α : binarySequence
  α 0 = true
  α 1 = true
  α (suc (suc _)) = false

  fun' : Bool → Σ[ n ∈ ℕ ] α n ≡ true
  fun' false = 0 , refl
  fun' true = 1 , refl

  inv' : Σ[ n ∈ ℕ ] α n ≡ true → Bool
  inv' (0 , _) = false
  inv' (1 , _) = true
  inv' (suc (suc n) , p) = ex-falso (false≢true p)

  sec' : (x : Σ[ n ∈ ℕ ] α n ≡ true) → fun' (inv' x) ≡ x
  sec' (0 , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
  sec' (1 , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
  sec' (suc (suc n) , p) = ex-falso (false≢true p)

  ret' : (b : Bool) → inv' (fun' b) ≡ b
  ret' false = refl
  ret' true = refl

-- Step 2: freeBA Bool has a countable presentation
open import CountablyPresentedBooleanRings.Examples.FreeCase using (replacementFreeOnCountable)

is-cp-freeBool : has-Boole-ω' (freeBA Bool)
is-cp-freeBool = replacementFreeOnCountable Bool countBool

-- Step 3: Construct the equivalence freeBA Bool ≅ Bool²
-- The free Boolean ring on 2 generators is the 4-element Boolean ring
-- with atoms e₁ = generator true and e₂ = generator false

open import BooleanRing.FreeBooleanRing.FreeBool using (generator; freeBA-universal-property; inducedBAHom; evalBAInduce; inducedBAHomUnique)

-- The map freeBA Bool → Bool² sends generators to atoms
-- Note: inducedBAHom extends A → ⟨B⟩ to BoolHom (freeBA A) B (not the reverse!)
freeBool→Bool²-on-gens : Bool → ⟨ Bool² ⟩
freeBool→Bool²-on-gens true = (true , false)  -- e₁ = Bool²-unit-left
freeBool→Bool²-on-gens false = (false , true) -- e₂ = Bool²-unit-right

-- By universal property, this extends to a homomorphism freeBA Bool → Bool²
freeBool→Bool²-hom : BoolHom (freeBA Bool) Bool²
freeBool→Bool²-hom = inducedBAHom Bool Bool² freeBool→Bool²-on-gens

-- Note: The map Bool² → freeBA Bool cannot use inducedBAHom (wrong direction).
-- A full proof of Bool² ≅ freeBA Bool would require explicit HIT reasoning.

-- Direct presentation of Bool² as a countably presented Boolean ring
-- ===================================================================
-- Bool² has 4 elements with 2 complementary atoms: e₀ = (true,false), e₁ = (false,true)
-- Note: freeBA Bool has 16 elements (2^(2^2)), so Bool² ≠ freeBA Bool.
-- Instead: Bool² ≃ freeBA ℕ /Im relBool² where:
--   relBool² 0 = generator 0 · generator 1         (atoms have trivial meet)
--   relBool² 1 = 1 + generator 0 + generator 1     (atoms sum to 1)
--   relBool² (n+2) = generator (n+2)               (kill extra generators)

-- Local module for Bool² presentation
