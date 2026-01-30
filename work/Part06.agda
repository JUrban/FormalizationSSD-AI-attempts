{-# OPTIONS --cubical --guardedness #-}

module work.Part06 where

-- =============================================================================
-- Part 06: B∞ construction, Sp(B∞) ≅ ℕ∞, Direct Products, Bool²
-- =============================================================================

-- Import Part05 for previous definitions
open import work.Part05 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; isoToIsEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; inj-m+; +-zero)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.CommRing.DirectProd using (DirectProd-CommRing)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; idBoolEquiv; has-Countability-structure)
open import Axioms.StoneDuality using (Sp; Booleω)

-- =============================================================================
-- B∞-construction module (lines 3744-3802 of work.agda)
-- =============================================================================

module B∞-construction where
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
  -- This is what the relations enforce.

  -- First, we show that the relation relB∞ k = 0 in B∞ (by construction)
  relB∞-is-zero : (k : ℕ) → fst π∞ (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞)
  relB∞-is-zero k = QB.zeroOnImage {B = freeBA ℕ} {f = relB∞} k

  -- The product in B∞ comes from the quotient ring structure
  open BooleanRingStr (snd B∞) renaming (_·_ to _·∞_ ; 𝟘 to 𝟘∞ ; 𝟙 to 𝟙∞)

-- B∞ is in Booleω (it's a quotient of freeBA ℕ)
-- has-Boole-ω' B∞ holds because relB∞ : ℕ → ⟨ freeBA ℕ ⟩ is the presentation

open B∞-construction

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

-- Forward direction: BoolHom B∞ BoolBR → ℕ∞
-- Given h : B∞ → 2, the sequence (h(g∞ n))_n hits 1 at most once
SpB∞-to-ℕ∞-seq : Sp B∞-Booleω → binarySequence
SpB∞-to-ℕ∞-seq h n = h $cr (g∞ n)

-- Helper: a + (suc d) with d = b - a - 1 gives b when a < b
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
  open IsCommRingHom (snd h)

  -- h preserves multiplication
  h-pres· : (a b : ⟨ B∞ ⟩) → h $cr (a ·∞ b) ≡ (h $cr a) and (h $cr b)
  h-pres· = pres·

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
      step1 : true and true ≡ (h $cr (g∞ m)) and (h $cr (g∞ n))
      step1 = cong₂ _and_ (sym hm=true) (sym hn=true)

      contradiction : true ≡ false
      contradiction = step1 ∙ and-is-false
    in ex-falso (true≢false contradiction)

-- Now we can define the full conversion from Sp(B∞) to ℕ∞
SpB∞-to-ℕ∞ : Sp B∞-Booleω → ℕ∞
SpB∞-to-ℕ∞ h = SpB∞-to-ℕ∞-seq h , SpB∞-seq-atMostOnce h

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
open import BooleanRing.FreeBooleanRing.FreeBool using (inducedBAHom; evalBAInduce; inducedBAHomUnique)

-- The map freeBA Bool → Bool² sends generators to atoms
freeBool→Bool²-on-gens : Bool → ⟨ Bool² ⟩
freeBool→Bool²-on-gens true = (true , false)  -- e₁ = Bool²-unit-left
freeBool→Bool²-on-gens false = (false , true) -- e₂ = Bool²-unit-right

-- By universal property, this extends to a homomorphism freeBA Bool → Bool²
freeBool→Bool²-hom : BoolHom (freeBA Bool) Bool²
freeBool→Bool²-hom = inducedBAHom Bool Bool² freeBool→Bool²-on-gens

-- =============================================================================
-- Local module for Bool² presentation
-- =============================================================================

module Bool²-presentation where
  open BooleanRingStr (snd (freeBA ℕ)) using (𝟙) renaming (_+_ to _+free_ ; _·_ to _·free_)

  -- The generators in freeBA ℕ
  g₀ : ⟨ freeBA ℕ ⟩
  g₀ = generator 0

  g₁ : ⟨ freeBA ℕ ⟩
  g₁ = generator 1

  -- The relations for Bool²
  relBool² : ℕ → ⟨ freeBA ℕ ⟩
  relBool² 0 = g₀ ·free g₁
  relBool² 1 = 𝟙 +free g₀ +free g₁
  relBool² (suc (suc n)) = generator (suc (suc n))

  -- The quotient ring: Bool²-quotient = freeBA ℕ /Im relBool²
  Bool²-quotient : BooleanRing ℓ-zero
  Bool²-quotient = freeBA ℕ QB./Im relBool²

  -- The quotient map
  π : BoolHom (freeBA ℕ) Bool²-quotient
  π = QB.quotientImageHom

  -- The backward map: generator 0 ↦ (true, false), generator 1 ↦ (false, true)
  gens→Bool² : ℕ → ⟨ Bool² ⟩
  gens→Bool² 0 = (true , false)   -- e₀
  gens→Bool² 1 = (false , true)   -- e₁
  gens→Bool² (suc (suc n)) = (false , false)  -- killed generators map to 0

  -- The induced homomorphism freeBA ℕ → Bool² via universal property
  freeBool→Bool² : BoolHom (freeBA ℕ) Bool²
  freeBool→Bool² = inducedBAHom ℕ Bool² gens→Bool²

  -- Need to show that relBool² n maps to 0 in Bool² for all n
  private
    open BooleanRingStr (snd Bool²) using () renaming (_+_ to _+²_ ; _·_ to _·²_ ; 𝟘 to 𝟘² ; 𝟙 to 𝟙²)
    open IsCommRingHom (snd freeBool→Bool²) renaming (pres1 to presB1 ; pres+ to presB+ ; pres· to presB·)

  freeBool→Bool²-on-rels : (n : ℕ) → fst freeBool→Bool² (relBool² n) ≡ 𝟘²
  freeBool→Bool²-on-rels 0 =
    -- g₀ · g₁ ↦ (true,false) · (false,true) = (false,false) = 0
    fst freeBool→Bool² (g₀ ·free g₁)
      ≡⟨ presB· g₀ g₁ ⟩
    fst freeBool→Bool² g₀ ·² fst freeBool→Bool² g₁
      ≡⟨ cong₂ _·²_ (evalBAInduce ℕ Bool² gens→Bool² ≡$ 0) (evalBAInduce ℕ Bool² gens→Bool² ≡$ 1) ⟩
    (true , false) ·² (false , true)
      ≡⟨ refl ⟩
    𝟘² ∎
  freeBool→Bool²-on-rels 1 =
    fst freeBool→Bool² (𝟙 +free g₀ +free g₁)
      ≡⟨ presB+ (𝟙 +free g₀) g₁ ⟩
    fst freeBool→Bool² (𝟙 +free g₀) +² fst freeBool→Bool² g₁
      ≡⟨ cong₂ _+²_ (presB+ 𝟙 g₀) (evalBAInduce ℕ Bool² gens→Bool² ≡$ 1) ⟩
    (fst freeBool→Bool² 𝟙 +² fst freeBool→Bool² g₀) +² (false , true)
      ≡⟨ cong₂ _+²_ (cong₂ _+²_ presB1 (evalBAInduce ℕ Bool² gens→Bool² ≡$ 0)) refl ⟩
    ((true , true) +² (true , false)) +² (false , true)
      ≡⟨ refl ⟩
    𝟘² ∎
  freeBool→Bool²-on-rels (suc (suc n)) =
    fst freeBool→Bool² (generator (suc (suc n)))
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ (suc (suc n)) ⟩
    (false , false)
      ≡⟨ refl ⟩
    𝟘² ∎

  -- The induced homomorphism from the quotient to Bool²
  quotient→Bool² : BoolHom Bool²-quotient Bool²
  quotient→Bool² = QB.inducedHom Bool² freeBool→Bool² freeBool→Bool²-on-rels

  -- The forward map: Bool² → quotient
  Bool²→quotient-fun : ⟨ Bool² ⟩ → ⟨ Bool²-quotient ⟩
  Bool²→quotient-fun (false , false) = BooleanRingStr.𝟘 (snd Bool²-quotient)
  Bool²→quotient-fun (false , true)  = fst π g₁
  Bool²→quotient-fun (true , false)  = fst π g₀
  Bool²→quotient-fun (true , true)   = BooleanRingStr.𝟙 (snd Bool²-quotient)

  private
    open BooleanRingStr (snd Bool²-quotient) using () renaming (_+_ to _+Q_ ; _·_ to _·Q_ ; 𝟘 to 𝟘Q ; 𝟙 to 𝟙Q)
    open BooleanAlgebraStr Bool²-quotient using () renaming (characteristic2 to char2Q-raw ; ∧AnnihilL to annihilLQ ; ∧AnnihilR to annihilRQ)
    open BooleanAlgebraStr Bool² using () renaming (characteristic2 to char2²-raw)
    open import Cubical.Tactics.CommRingSolver
    open import Cubical.HITs.SetQuotients as SQ

    -- Characteristic 2 property: x + x = 0 in any Boolean ring
    char2Q : (x : ⟨ Bool²-quotient ⟩) → x +Q x ≡ 𝟘Q
    char2Q x = char2Q-raw {x}

    -- Characteristic 2 for Bool²
    char2² : (x : ⟨ Bool² ⟩) → x +² x ≡ 𝟘²
    char2² x = char2²-raw {x}

    -- Helper lemma: g₀ + g₁ = 1 in the quotient
    g₀+g₁≡𝟙Q : fst π g₀ +Q fst π g₁ ≡ 𝟙Q
    g₀+g₁≡𝟙Q = step6 ∙ step7 ∙ step8 ∙ step9
      where
        -- From the relation: fst π (relBool² 1) = 𝟘Q
        rel1-eq : fst π (𝟙 +free g₀ +free g₁) ≡ 𝟘Q
        rel1-eq = QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} 1
        step2 : fst π (𝟙 +free g₀) ≡ fst π 𝟙 +Q fst π g₀
        step2 = IsCommRingHom.pres+ (snd π) 𝟙 g₀
        step3 : fst π 𝟙 ≡ 𝟙Q
        step3 = IsCommRingHom.pres1 (snd π)
        pathAB : 𝟙Q +Q fst π g₀ +Q fst π g₁ ≡ fst π (𝟙 +free g₀) +Q fst π g₁
        pathAB = cong (λ z → z +Q fst π g₀ +Q fst π g₁) (sym step3) ∙
                 cong (_+Q fst π g₁) (sym step2)
        pathC : fst π (𝟙 +free g₀) +Q fst π g₁ ≡ fst π (𝟙 +free g₀ +free g₁)
        pathC = sym (IsCommRingHom.pres+ (snd π) (𝟙 +free g₀) g₁)
        combined : 𝟙Q +Q fst π g₀ +Q fst π g₁ ≡ 𝟘Q
        combined = pathAB ∙ pathC ∙ rel1-eq
        step4 : 𝟙Q +Q (𝟙Q +Q fst π g₀ +Q fst π g₁) ≡ 𝟙Q +Q 𝟘Q
        step4 = cong (𝟙Q +Q_) combined
        step5 : 𝟙Q +Q 𝟘Q ≡ 𝟙Q
        step5 = BooleanRingStr.+IdR (snd Bool²-quotient) 𝟙Q
        step6 : fst π g₀ +Q fst π g₁ ≡ 𝟘Q +Q fst π g₀ +Q fst π g₁
        step6 = cong (_+Q fst π g₁) (sym (BooleanRingStr.+IdL (snd Bool²-quotient) (fst π g₀)))
        step7 : 𝟘Q +Q fst π g₀ +Q fst π g₁ ≡ (𝟙Q +Q 𝟙Q) +Q fst π g₀ +Q fst π g₁
        step7 = cong (λ z → z +Q fst π g₀ +Q fst π g₁) (sym (char2Q 𝟙Q))
        step8 : (𝟙Q +Q 𝟙Q) +Q fst π g₀ +Q fst π g₁ ≡ 𝟙Q +Q (𝟙Q +Q fst π g₀ +Q fst π g₁)
        step8 = solve! (BooleanRing→CommRing Bool²-quotient)
        step9 : 𝟙Q +Q (𝟙Q +Q fst π g₀ +Q fst π g₁) ≡ 𝟙Q
        step9 = step4 ∙ step5

    -- Helper for the symmetric case: g₁ + g₀ = 1
    g₁+g₀≡𝟙Q : fst π g₁ +Q fst π g₀ ≡ 𝟙Q
    g₁+g₀≡𝟙Q = BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀) ∙ g₀+g₁≡𝟙Q

    -- Derived helper: g₀ = g₁ + 1
    g₀≡g₁+𝟙Q : fst π g₀ ≡ fst π g₁ +Q 𝟙Q
    g₀≡g₁+𝟙Q =
      fst π g₀
        ≡⟨ sym (BooleanRingStr.+IdL (snd Bool²-quotient) (fst π g₀)) ⟩
      𝟘Q +Q fst π g₀
        ≡⟨ cong (_+Q fst π g₀) (sym (char2Q (fst π g₁))) ⟩
      (fst π g₁ +Q fst π g₁) +Q fst π g₀
        ≡⟨ solve! (BooleanRing→CommRing Bool²-quotient) ⟩
      fst π g₁ +Q (fst π g₁ +Q fst π g₀)
        ≡⟨ cong (fst π g₁ +Q_) g₁+g₀≡𝟙Q ⟩
      fst π g₁ +Q 𝟙Q ∎

    -- Symmetric derived helper: g₁ = g₀ + 1
    g₁≡g₀+𝟙Q : fst π g₁ ≡ fst π g₀ +Q 𝟙Q
    g₁≡g₀+𝟙Q =
      fst π g₁
        ≡⟨ sym (BooleanRingStr.+IdL (snd Bool²-quotient) (fst π g₁)) ⟩
      𝟘Q +Q fst π g₁
        ≡⟨ cong (_+Q fst π g₁) (sym (char2Q (fst π g₀))) ⟩
      (fst π g₀ +Q fst π g₀) +Q fst π g₁
        ≡⟨ solve! (BooleanRing→CommRing Bool²-quotient) ⟩
      fst π g₀ +Q (fst π g₀ +Q fst π g₁)
        ≡⟨ cong (fst π g₀ +Q_) g₀+g₁≡𝟙Q ⟩
      fst π g₀ +Q 𝟙Q ∎

    -- Multiplication helper: g₀ · g₁ = 0 (from relation 0)
    g₀·g₁≡𝟘Q : fst π g₀ ·Q fst π g₁ ≡ 𝟘Q
    g₀·g₁≡𝟘Q =
      fst π g₀ ·Q fst π g₁
        ≡⟨ sym (IsCommRingHom.pres· (snd π) g₀ g₁) ⟩
      fst π (g₀ ·free g₁)
        ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} 0 ⟩
      𝟘Q ∎

    -- Symmetric multiplication helper: g₁ · g₀ = 0
    g₁·g₀≡𝟘Q : fst π g₁ ·Q fst π g₀ ≡ 𝟘Q
    g₁·g₀≡𝟘Q = BooleanRingStr.·Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀) ∙ g₀·g₁≡𝟘Q

    -- In Boolean rings, -x = x (since x + x = 0)
    neg≡self² : (x : ⟨ Bool² ⟩) → BooleanRingStr.-_ (snd Bool²) x ≡ x
    neg≡self² (false , false) = refl
    neg≡self² (false , true) = refl
    neg≡self² (true , false) = refl
    neg≡self² (true , true) = refl

    -- Same property for the quotient ring: -x = x
    neg≡selfQ : (y : ⟨ Bool²-quotient ⟩) → BooleanRingStr.-_ (snd Bool²-quotient) y ≡ y
    neg≡selfQ y = sym (BooleanAlgebraStr.-IsId Bool²-quotient)

  -- The forward map is a homomorphism
  Bool²→quotient-pres1 : Bool²→quotient-fun 𝟙² ≡ 𝟙Q
  Bool²→quotient-pres1 = refl

  Bool²→quotient-pres+ : (x y : ⟨ Bool² ⟩) → Bool²→quotient-fun (x +² y) ≡ Bool²→quotient-fun x +Q Bool²→quotient-fun y
  Bool²→quotient-pres+ (false , false) (false , false) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , false) (false , true) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , false) (true , false) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , false) (true , true) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , true) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , true) (false , true) = sym (char2Q (fst π g₁))
  Bool²→quotient-pres+ (false , true) (true , false) = sym g₁+g₀≡𝟙Q
  Bool²→quotient-pres+ (false , true) (true , true) = g₀≡g₁+𝟙Q
  Bool²→quotient-pres+ (true , false) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (true , false) (false , true) =
    cong Bool²→quotient-fun (cong₂ _,_ (⊕-comm true false) (⊕-comm false true)) ∙
    Bool²→quotient-pres+ (false , true) (true , false) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀)
  Bool²→quotient-pres+ (true , false) (true , false) = sym (char2Q (fst π g₀))
  Bool²→quotient-pres+ (true , false) (true , true) = g₁≡g₀+𝟙Q
  Bool²→quotient-pres+ (true , true) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (true , true) (false , true) =
    cong Bool²→quotient-fun (cong₂ _,_ (⊕-comm true false) (⊕-comm true true)) ∙
    Bool²→quotient-pres+ (false , true) (true , true) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) 𝟙Q
  Bool²→quotient-pres+ (true , true) (true , false) =
    cong Bool²→quotient-fun (cong₂ _,_ (⊕-comm true true) (⊕-comm true false)) ∙
    Bool²→quotient-pres+ (true , false) (true , true) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₀) 𝟙Q
  Bool²→quotient-pres+ (true , true) (true , true) = sym (char2Q 𝟙Q)

  Bool²→quotient-pres· : (x y : ⟨ Bool² ⟩) → Bool²→quotient-fun (x ·² y) ≡ Bool²→quotient-fun x ·Q Bool²→quotient-fun y
  Bool²→quotient-pres· (false , false) y = sym annihilLQ
  Bool²→quotient-pres· (false , true) (false , false) = sym annihilRQ
  Bool²→quotient-pres· (false , true) (false , true) = sym (BooleanRingStr.·Idem (snd Bool²-quotient) (fst π g₁))
  Bool²→quotient-pres· (false , true) (true , false) = sym g₁·g₀≡𝟘Q
  Bool²→quotient-pres· (false , true) (true , true) = sym (BooleanRingStr.·IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres· (true , false) (false , false) = sym annihilRQ
  Bool²→quotient-pres· (true , false) (false , true) =
    Bool²→quotient-pres· (false , true) (true , false) ∙
    BooleanRingStr.·Comm (snd Bool²-quotient) _ _
  Bool²→quotient-pres· (true , false) (true , false) = sym (BooleanRingStr.·Idem (snd Bool²-quotient) (fst π g₀))
  Bool²→quotient-pres· (true , false) (true , true) = sym (BooleanRingStr.·IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres· (true , true) y = sym (BooleanRingStr.·IdL (snd Bool²-quotient) _)

  Bool²→quotient : BoolHom Bool² Bool²-quotient
  Bool²→quotient = Bool²→quotient-fun , record
    { pres0 = refl
    ; pres1 = refl
    ; pres+ = Bool²→quotient-pres+
    ; pres· = Bool²→quotient-pres·
    ; pres- = Bool²→quotient-pres-
    }
    where
      Bool²→quotient-pres- : (x : ⟨ Bool² ⟩) → Bool²→quotient-fun (BooleanRingStr.-_ (snd Bool²) x) ≡ BooleanRingStr.-_ (snd Bool²-quotient) (Bool²→quotient-fun x)
      Bool²→quotient-pres- x = cong Bool²→quotient-fun (neg≡self² x) ∙ sym (neg≡selfQ (Bool²→quotient-fun x))

  -- Now we prove the two maps are inverses

  -- quotient→Bool² ∘ Bool²→quotient = id
  roundtrip-Bool² : (x : ⟨ Bool² ⟩) → fst quotient→Bool² (Bool²→quotient-fun x) ≡ x
  roundtrip-Bool² (false , false) = IsCommRingHom.pres0 (snd quotient→Bool²)
  roundtrip-Bool² (false , true) =
    fst quotient→Bool² (fst π g₁)
      ≡⟨ cong (fst quotient→Bool²) refl ⟩
    fst (quotient→Bool² ∘cr π) g₁
      ≡⟨ cong (λ h → fst h g₁) (QB.evalInduce Bool² {freeBool→Bool²} {freeBool→Bool²-on-rels}) ⟩
    fst freeBool→Bool² g₁
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ 1 ⟩
    (false , true) ∎
  roundtrip-Bool² (true , false) =
    fst quotient→Bool² (fst π g₀)
      ≡⟨ cong (fst quotient→Bool²) refl ⟩
    fst (quotient→Bool² ∘cr π) g₀
      ≡⟨ cong (λ h → fst h g₀) (QB.evalInduce Bool² {freeBool→Bool²} {freeBool→Bool²-on-rels}) ⟩
    fst freeBool→Bool² g₀
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ 0 ⟩
    (true , false) ∎
  roundtrip-Bool² (true , true) = IsCommRingHom.pres1 (snd quotient→Bool²)

  -- Bool²→quotient ∘ quotient→Bool² = id (on the quotient)
  composite-on-gens : (n : ℕ) → fst Bool²→quotient (fst quotient→Bool² (fst π (generator n))) ≡ fst π (generator n)
  composite-on-gens 0 =
    fst Bool²→quotient (fst quotient→Bool² (fst π g₀))
      ≡⟨ cong (fst Bool²→quotient) (roundtrip-Bool² (true , false)) ⟩
    fst Bool²→quotient (true , false)
      ≡⟨ refl ⟩
    fst π g₀ ∎
  composite-on-gens 1 =
    fst Bool²→quotient (fst quotient→Bool² (fst π g₁))
      ≡⟨ cong (fst Bool²→quotient) (roundtrip-Bool² (false , true)) ⟩
    fst Bool²→quotient (false , true)
      ≡⟨ refl ⟩
    fst π g₁ ∎
  composite-on-gens (suc (suc n)) =
    fst Bool²→quotient (fst quotient→Bool² (fst π (generator (suc (suc n)))))
      ≡⟨ cong (fst Bool²→quotient ∘ fst quotient→Bool²) (QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} (suc (suc n))) ⟩
    fst Bool²→quotient (fst quotient→Bool² 𝟘Q)
      ≡⟨ cong (fst Bool²→quotient) (IsCommRingHom.pres0 (snd quotient→Bool²)) ⟩
    fst Bool²→quotient 𝟘²
      ≡⟨ IsCommRingHom.pres0 (snd Bool²→quotient) ⟩
    𝟘Q
      ≡⟨ sym (QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} (suc (suc n))) ⟩
    fst π (generator (suc (suc n))) ∎

  composite-hom-on-gens : (n : ℕ) → fst (Bool²→quotient ∘cr quotient→Bool² ∘cr π) (generator n) ≡ fst π (generator n)
  composite-hom-on-gens = composite-on-gens

  -- By universal property, composite-hom = π
  composite-eq-π : Bool²→quotient ∘cr quotient→Bool² ∘cr π ≡ π
  composite-eq-π = sym (inducedBAHomUnique ℕ Bool²-quotient (fst π ∘ generator)
                                      (Bool²→quotient ∘cr quotient→Bool² ∘cr π)
                                      (funExt composite-on-gens)) ∙
                   inducedBAHomUnique ℕ Bool²-quotient (fst π ∘ generator) π refl

  opaque
    unfolding QB._/Im_
    unfolding QB.quotientImageHom
    roundtrip-quotient : (x : ⟨ Bool²-quotient ⟩) → fst Bool²→quotient (fst quotient→Bool² x) ≡ x
    roundtrip-quotient = SQ.elimProp (λ _ → BooleanRingStr.is-set (snd Bool²-quotient) _ _)
                         (λ a → funExt⁻ (cong fst composite-eq-π) a)

  -- The equivalence
  Bool²≃quotient : BooleanRingEquiv Bool² Bool²-quotient
  Bool²≃quotient = (fst Bool²→quotient , isoToIsEquiv (iso (fst Bool²→quotient) (fst quotient→Bool²) roundtrip-quotient roundtrip-Bool²)) ,
                   snd Bool²→quotient

open Bool²-presentation hiding (π)

-- The proof that Bool² has a countable presentation
Bool²-has-Boole-ω' : has-Boole-ω' Bool²
Bool²-has-Boole-ω' = relBool² , Bool²≃quotient

Bool²-Booleω : Booleω
Bool²-Booleω = Bool² , ∣ Bool²-has-Boole-ω' ∣₁

-- =============================================================================
-- Sp(Bool²) ≃ Bool (the projections)
-- =============================================================================

-- The two homomorphisms BoolBR × BoolBR → BoolBR are the projections
proj₁-Bool² : ⟨ Bool² ⟩ → Bool
proj₁-Bool² = fst

proj₂-Bool² : ⟨ Bool² ⟩ → Bool
proj₂-Bool² = snd

-- π₁ is a Boolean ring homomorphism
proj₁-Bool²-hom : BoolHom Bool² BoolBR
proj₁-Bool²-hom = proj₁-Bool² , record
  { pres0 = refl
  ; pres1 = refl
  ; pres+ = λ _ _ → refl
  ; pres· = λ _ _ → refl
  ; pres- = λ _ → refl
  }

-- π₂ is a Boolean ring homomorphism
proj₂-Bool²-hom : BoolHom Bool² BoolBR
proj₂-Bool²-hom = proj₂-Bool² , record
  { pres0 = refl
  ; pres1 = refl
  ; pres+ = λ _ _ → refl
  ; pres· = λ _ _ → refl
  ; pres- = λ _ → refl
  }

-- Classification of homomorphisms: any h equals proj₁ or proj₂
classify-Bool²-hom : (h : Sp Bool²-Booleω) → (h ≡ proj₁-Bool²-hom) ⊎ (h ≡ proj₂-Bool²-hom)
classify-Bool²-hom h = helper (fst h Bool²-unit-left) refl
  where
  h≡proj₁ : fst h Bool²-unit-left ≡ true → h ≡ proj₁-Bool²-hom
  h≡proj₁ h-ul-true = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing Bool²)) f (snd (BooleanRing→CommRing BoolBR))) (sym funEq)
    where
    h-ur : fst h Bool²-unit-right ≡ false
    h-ur =
      fst h (false , true)
        ≡⟨ cong (fst h) (cong₂ _,_ refl (sym (⊕-comm false true))) ⟩
      fst h (false , true ⊕ false)
        ≡⟨ cong (fst h) (cong₂ _,_ (sym (⊕-comm true true)) refl) ⟩
      fst h ((true ⊕ true) , (true ⊕ false))
        ≡⟨ IsCommRingHom.pres+ (snd h) (true , true) (true , false) ⟩
      (fst h (true , true)) ⊕ (fst h (true , false))
        ≡⟨ cong₂ _⊕_ (IsCommRingHom.pres1 (snd h)) h-ul-true ⟩
      true ⊕ true
        ≡⟨ ⊕-comm true true ⟩
      false ∎
    funEq : proj₁-Bool² ≡ fst h
    funEq = funExt λ { (false , false) → sym (IsCommRingHom.pres0 (snd h))
                     ; (false , true) → sym h-ur
                     ; (true , false) → sym h-ul-true
                     ; (true , true) → sym (IsCommRingHom.pres1 (snd h)) }

  h≡proj₂ : fst h Bool²-unit-left ≡ false → h ≡ proj₂-Bool²-hom
  h≡proj₂ h-ul-false = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing Bool²)) f (snd (BooleanRing→CommRing BoolBR))) (sym funEq)
    where
    h-ur : fst h Bool²-unit-right ≡ true
    h-ur =
      fst h (false , true)
        ≡⟨ cong (fst h) (cong₂ _,_ refl (sym (⊕-comm false true))) ⟩
      fst h (false , true ⊕ false)
        ≡⟨ cong (fst h) (cong₂ _,_ (sym (⊕-comm true true)) refl) ⟩
      fst h ((true ⊕ true) , (true ⊕ false))
        ≡⟨ IsCommRingHom.pres+ (snd h) (true , true) (true , false) ⟩
      (fst h (true , true)) ⊕ (fst h (true , false))
        ≡⟨ cong₂ _⊕_ (IsCommRingHom.pres1 (snd h)) h-ul-false ⟩
      true ⊕ false
        ≡⟨ ⊕-comm true false ⟩
      true ∎
    funEq : proj₂-Bool² ≡ fst h
    funEq = funExt λ { (false , false) → sym (IsCommRingHom.pres0 (snd h))
                     ; (false , true) → sym h-ur
                     ; (true , false) → sym h-ul-false
                     ; (true , true) → sym (IsCommRingHom.pres1 (snd h)) }

  helper : (b : Bool) → fst h Bool²-unit-left ≡ b → (h ≡ proj₁-Bool²-hom) ⊎ (h ≡ proj₂-Bool²-hom)
  helper true = λ eq → inl (h≡proj₁ eq)
  helper false = λ eq → inr (h≡proj₂ eq)

-- Forward direction: Sp(Bool²) → Bool
Sp-Bool²→Bool : Sp Bool²-Booleω → Bool
Sp-Bool²→Bool h = fst h Bool²-unit-left

-- Backward direction: Bool → Sp(Bool²)
Bool→Sp-Bool² : Bool → Sp Bool²-Booleω
Bool→Sp-Bool² true = proj₁-Bool²-hom
Bool→Sp-Bool² false = proj₂-Bool²-hom

-- Roundtrip 1: Bool→Sp-Bool² ∘ Sp-Bool²→Bool = id
Sp-Bool²→Bool→Sp-Bool² : (h : Sp Bool²-Booleω) → Bool→Sp-Bool² (Sp-Bool²→Bool h) ≡ h
Sp-Bool²→Bool→Sp-Bool² h with classify-Bool²-hom h
... | inl h≡proj₁ = cong Bool→Sp-Bool² (cong (λ g → fst g Bool²-unit-left) h≡proj₁) ∙ sym h≡proj₁
... | inr h≡proj₂ = cong Bool→Sp-Bool² (cong (λ g → fst g Bool²-unit-left) h≡proj₂) ∙ sym h≡proj₂

-- Roundtrip 2: Sp-Bool²→Bool ∘ Bool→Sp-Bool² = id
Bool→Sp-Bool²→Bool : (b : Bool) → Sp-Bool²→Bool (Bool→Sp-Bool² b) ≡ b
Bool→Sp-Bool²→Bool true = refl
Bool→Sp-Bool²→Bool false = refl

-- The equivalence Sp(BoolBR × BoolBR) ≃ Bool
Sp-Bool²≃Bool : Sp Bool²-Booleω ≃ Bool
Sp-Bool²≃Bool = isoToEquiv (iso Sp-Bool²→Bool Bool→Sp-Bool² Bool→Sp-Bool²→Bool Sp-Bool²→Bool→Sp-Bool²)
