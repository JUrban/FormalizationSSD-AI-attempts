{-# OPTIONS --cubical --guardedness #-}

module work.Part09 where

-- =============================================================================
-- Part 09: ℕ∞ ↔ Sp B∞ correspondence, LLPO derivation, and normal form
--          infrastructure (lines 6500-7500 of work.agda)
-- =============================================================================

-- Import Part08 for previous definitions
open import work.Part08 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open Iso
open import Cubical.Foundations.Equiv using (_≃_)
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
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
import QuotientBool as QB
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; idBoolEquiv; has-Countability-structure)
open import Axioms.StoneDuality using (Sp; Booleω)

-- Open BooleanRingStr for B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; _+_ to _+×_)

-- Note: _·∞_, 𝟘∞, 𝟙∞ are already exported from Part06 publicly
-- _+∞_ is needed locally and is not exported from Part07
open BooleanRingStr (snd B∞) using () renaming (_+_ to _+∞_)

-- =============================================================================
-- ℕ∞ to Sp B∞ correspondence (lines 6500-6600 of work.agda)
-- =============================================================================

-- Evaluate ℕ∞ on generators
ℕ∞-on-gen : ℕ∞ → ℕ → Bool
ℕ∞-on-gen α n = fst α n

-- This map sends distinct generators to values that multiply to 0 in BoolBR
-- (since α hits at most once, we can't have both α_m = α_n = true for m ≠ n)
ℕ∞-gen-respects-relations : (α : ℕ∞) → (m n : ℕ) → ¬ (m ≡ n) →
  (ℕ∞-on-gen α m) and (ℕ∞-on-gen α n) ≡ false
ℕ∞-gen-respects-relations α m n m≠n = lemma (fst α m) (fst α n) refl refl
  where
  lemma : (am an : Bool) → fst α m ≡ am → fst α n ≡ an → am and an ≡ false
  lemma false _ _ _ = refl
  lemma true false _ _ = refl
  lemma true true αm≡true αn≡true = ex-falso (m≠n (snd α m n αm≡true αn≡true))

-- The map on freeBA ℕ induced by α
ℕ∞-to-SpB∞-free : ℕ∞ → BoolHom (freeBA ℕ) BoolBR
ℕ∞-to-SpB∞-free α = inducedBAHom ℕ BoolBR (ℕ∞-on-gen α)

-- Key property: ℕ∞-to-SpB∞-free agrees with ℕ∞-on-gen on generators
ℕ∞-to-SpB∞-free-on-gen : (α : ℕ∞) → fst (ℕ∞-to-SpB∞-free α) ∘ generator ≡ ℕ∞-on-gen α
ℕ∞-to-SpB∞-free-on-gen α = evalBAInduce ℕ BoolBR (ℕ∞-on-gen α)

-- Helper: distinct generators map to and-zero under ℕ∞-to-SpB∞-free
ℕ∞-to-SpB∞-free-distinct-zero : (α : ℕ∞) (a b : ℕ) → ¬ (a ≡ b) →
  fst (ℕ∞-to-SpB∞-free α) (gen a · gen b) ≡ false
ℕ∞-to-SpB∞-free-distinct-zero α a b a≠b =
  fst (ℕ∞-to-SpB∞-free α) (gen a · gen b)
    ≡⟨ IsCommRingHom.pres· (snd (ℕ∞-to-SpB∞-free α)) (gen a) (gen b) ⟩
  (fst (ℕ∞-to-SpB∞-free α) (gen a)) and (fst (ℕ∞-to-SpB∞-free α) (gen b))
    ≡⟨ cong₂ _and_ (funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) a) (funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) b) ⟩
  (ℕ∞-on-gen α a) and (ℕ∞-on-gen α b)
    ≡⟨ ℕ∞-gen-respects-relations α a b a≠b ⟩
  false ∎

ℕ∞-to-SpB∞-respects-rel : (α : ℕ∞) (k : ℕ) →
  fst (ℕ∞-to-SpB∞-free α) (relB∞ k) ≡ false
ℕ∞-to-SpB∞-respects-rel α k =
  let (a , d) = cantorUnpair k
  in ℕ∞-to-SpB∞-free-distinct-zero α a (a +ℕ suc d) (a≠a+suc-d a d)

-- Descend to the quotient using QB.inducedHom
ℕ∞-to-SpB∞ : ℕ∞ → Sp B∞-Booleω
ℕ∞-to-SpB∞ α = QB.inducedHom {B = freeBA ℕ} {f = relB∞} BoolBR (ℕ∞-to-SpB∞-free α) (ℕ∞-to-SpB∞-respects-rel α)

-- First, establish that inducedHom ∘cr quotientImageHom = the original map
opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  ℕ∞-to-SpB∞-eval : (α : ℕ∞) →
    (ℕ∞-to-SpB∞ α) ∘cr π∞ ≡ ℕ∞-to-SpB∞-free α
  ℕ∞-to-SpB∞-eval α = QB.evalInduce {B = freeBA ℕ} {f = relB∞}
                        BoolBR {g = ℕ∞-to-SpB∞-free α} {gfx=0 = ℕ∞-to-SpB∞-respects-rel α}

-- The sequence equality
SpB∞-roundtrip-seq : (α : ℕ∞) (n : ℕ) →
  SpB∞-to-ℕ∞-seq (ℕ∞-to-SpB∞ α) n ≡ fst α n
SpB∞-roundtrip-seq α n =
  SpB∞-to-ℕ∞-seq (ℕ∞-to-SpB∞ α) n
    ≡⟨ refl ⟩  -- SpB∞-to-ℕ∞-seq h n = h $cr (g∞ n)
  (ℕ∞-to-SpB∞ α) $cr (g∞ n)
    ≡⟨ refl ⟩  -- g∞ n = fst π∞ (gen n)
  (ℕ∞-to-SpB∞ α) $cr (fst π∞ (gen n))
    ≡⟨ funExt⁻ (cong fst (ℕ∞-to-SpB∞-eval α)) (gen n) ⟩  -- by evalInduce
  fst (ℕ∞-to-SpB∞-free α) (gen n)
    ≡⟨ funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) n ⟩  -- by evalBAInduce
  ℕ∞-on-gen α n
    ≡⟨ refl ⟩  -- by definition of ℕ∞-on-gen
  fst α n ∎

-- The full roundtrip: equality of ℕ∞ is equality of the sequence
SpB∞-roundtrip : (α : ℕ∞) → SpB∞-to-ℕ∞ (ℕ∞-to-SpB∞ α) ≡ α
SpB∞-roundtrip α = Σ≡Prop
  (λ s → isPropHitsAtMostOnce s)
  (funExt (SpB∞-roundtrip-seq α))

-- =============================================================================
-- Generators are non-zero (using ℕ∞-to-SpB∞) (lines 6593-6616)
-- =============================================================================

-- h_n evaluates g_n to true
g∞-has-witness : (n : ℕ) → (ℕ∞-to-SpB∞ (δ∞ n)) $cr (g∞ n) ≡ true
g∞-has-witness n = SpB∞-roundtrip-seq (δ∞ n) n ∙ δ∞-hits-n n

-- Consequence: g∞ n ≠ 0
g∞-nonzero : (n : ℕ) → ¬ (g∞ n ≡ 𝟘∞)
g∞-nonzero n gn=0 =
  let h = ℕ∞-to-SpB∞ (δ∞ n)
      h-gn=t : h $cr (g∞ n) ≡ true
      h-gn=t = g∞-has-witness n
      h-0=f : h $cr 𝟘∞ ≡ false
      h-0=f = IsCommRingHom.pres0 (snd h)
      h-gn=f : h $cr (g∞ n) ≡ false
      h-gn=f = cong (h $cr_) gn=0 ∙ h-0=f
  in true≢false (sym h-gn=t ∙ h-gn=f)

-- =============================================================================
-- Join-zero lemma: finJoin∞ ns = 0 implies ns = [] (lines 6618-6691)
-- =============================================================================

-- Boolean OR in terms of XOR and AND
_orBool_ : Bool → Bool → Bool
false orBool b = b
true orBool _ = true

-- Key: a ⊕ b ⊕ (a and b) = a orBool b
xor-and-is-or : (a b : Bool) → (a ⊕ b) ⊕ (a and b) ≡ a orBool b
xor-and-is-or false false = refl
xor-and-is-or false true = refl
xor-and-is-or true false = refl
xor-and-is-or true true = refl

-- Homomorphism preserves join: h(a ∨ b) = h(a) orBool h(b)
h-pres-join-Bool : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr (a ∨∞ b) ≡ (h $cr a) orBool (h $cr b)
h-pres-join-Bool h a b =
  let open IsCommRingHom (snd h) renaming (pres+ to h-pres+ ; pres· to h-pres·)
  in h $cr (a ∨∞ b)
       ≡⟨ refl ⟩  -- ∨∞ = + + ·
     h $cr (a +∞ b +∞ (a ·∞ b))
       ≡⟨ h-pres+ (a +∞ b) (a ·∞ b) ⟩
     (h $cr (a +∞ b)) ⊕ (h $cr (a ·∞ b))
       ≡⟨ cong₂ _⊕_ (h-pres+ a b) (h-pres· a b) ⟩
     ((h $cr a) ⊕ (h $cr b)) ⊕ ((h $cr a) and (h $cr b))
       ≡⟨ xor-and-is-or (h $cr a) (h $cr b) ⟩
     (h $cr a) orBool (h $cr b) ∎

-- Key lemma: if h(a) = true, then h(a ∨ b) = true
h-join-monotone : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr a ≡ true → h $cr (a ∨∞ b) ≡ true
h-join-monotone h a b ha=t =
  h $cr (a ∨∞ b)
    ≡⟨ h-pres-join-Bool h a b ⟩
  (h $cr a) orBool (h $cr b)
    ≡⟨ cong (_orBool (h $cr b)) ha=t ⟩
  true orBool (h $cr b)
    ≡⟨ refl ⟩
  true ∎

-- Main lemma: if finJoin∞ ns = 0, then ns = []
finJoin∞-zero→empty : (ns : List ℕ) → finJoin∞ ns ≡ 𝟘∞ → ns ≡ []
finJoin∞-zero→empty [] _ = refl
finJoin∞-zero→empty (n ∷ rest) join=0 = ex-falso contradiction
  where
  -- Witness homomorphism: h_n(g_n) = true
  h : Sp B∞-Booleω
  h = ℕ∞-to-SpB∞ (δ∞ n)

  -- h evaluates g∞ n to true
  h-gn=true : h $cr (g∞ n) ≡ true
  h-gn=true = g∞-has-witness n

  -- h evaluates the join to true (by monotonicity)
  h-join=true : h $cr (finJoin∞ (n ∷ rest)) ≡ true
  h-join=true = h-join-monotone h (g∞ n) (finJoin∞ rest) h-gn=true

  -- But h(0) = false
  h-0=false : h $cr 𝟘∞ ≡ false
  h-0=false = IsCommRingHom.pres0 (snd h)

  -- h(finJoin∞ (n ∷ rest)) = h(0) = false
  h-join=false : h $cr (finJoin∞ (n ∷ rest)) ≡ false
  h-join=false = cong (h $cr_) join=0 ∙ h-0=false

  contradiction : ⊥
  contradiction = true≢false (sym h-join=true ∙ h-join=false)

-- =============================================================================
-- Meet of negations is non-zero: finMeetNeg∞ ns ≠ 0 (lines 6693-6798)
-- =============================================================================

-- The "infinity" element of ℕ∞: the constant-false sequence
∞-seq : ℕ → Bool
∞-seq _ = false

∞-hamo : hitsAtMostOnce ∞-seq
∞-hamo m n ∞m=t _ = ex-falso (false≢true ∞m=t)

ℕ∞-∞ : ℕ∞
ℕ∞-∞ = ∞-seq , ∞-hamo

-- The zero homomorphism: sends all generators to false
h₀ : Sp B∞-Booleω
h₀ = ℕ∞-to-SpB∞ ℕ∞-∞

-- h₀ sends all generators to false
h₀-on-gen : (n : ℕ) → h₀ $cr (g∞ n) ≡ false
h₀-on-gen n = SpB∞-roundtrip-seq ℕ∞-∞ n

-- Negation in Bool: ¬b = true ⊕ b
notBool : Bool → Bool
notBool false = true
notBool true = false

-- Key: in Boolean rings sent to Bool, h(¬x) = not(h(x))
h-pres-neg-Bool : (h : Sp B∞-Booleω) (x : ⟨ B∞ ⟩) →
  h $cr (¬∞ x) ≡ notBool (h $cr x)
h-pres-neg-Bool h x =
  let open IsCommRingHom (snd h) renaming (pres+ to h-pres+ ; pres1 to h-pres1)
  in h $cr (¬∞ x)
       ≡⟨ refl ⟩  -- ¬∞ x = 𝟙∞ +∞ x
     h $cr (𝟙∞ +∞ x)
       ≡⟨ h-pres+ 𝟙∞ x ⟩
     (h $cr 𝟙∞) ⊕ (h $cr x)
       ≡⟨ cong (_⊕ (h $cr x)) h-pres1 ⟩
     true ⊕ (h $cr x)
       ≡⟨ ⊕-comm true (h $cr x) ⟩
     (h $cr x) ⊕ true
       ≡⟨ helper (h $cr x) ⟩
     notBool (h $cr x) ∎
  where
  helper : (b : Bool) → b ⊕ true ≡ notBool b
  helper false = refl
  helper true = refl

-- h₀ sends negated generators to true
h₀-on-neg-gen : (n : ℕ) → h₀ $cr (¬∞ (g∞ n)) ≡ true
h₀-on-neg-gen n =
  h₀ $cr (¬∞ (g∞ n))
    ≡⟨ h-pres-neg-Bool h₀ (g∞ n) ⟩
  notBool (h₀ $cr (g∞ n))
    ≡⟨ cong notBool (h₀-on-gen n) ⟩
  notBool false
    ≡⟨ refl ⟩
  true ∎

-- Meet in Bool: a ∧ b = a and b
h-pres-meet-Bool : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr (a ∧∞ b) ≡ (h $cr a) and (h $cr b)
h-pres-meet-Bool h a b = IsCommRingHom.pres· (snd h) a b

-- Key lemma: if h(a) = true and h(b) = true, then h(a ∧ b) = true
h-meet-preserves-true : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr a ≡ true → h $cr b ≡ true → h $cr (a ∧∞ b) ≡ true
h-meet-preserves-true h a b ha=t hb=t =
  h $cr (a ∧∞ b)
    ≡⟨ h-pres-meet-Bool h a b ⟩
  (h $cr a) and (h $cr b)
    ≡⟨ cong₂ _and_ ha=t hb=t ⟩
  true and true
    ≡⟨ refl ⟩
  true ∎

-- h₀ evaluates finMeetNeg∞ to true for any list
h₀-on-finMeetNeg : (ns : List ℕ) → h₀ $cr (finMeetNeg∞ ns) ≡ true
h₀-on-finMeetNeg [] = IsCommRingHom.pres1 (snd h₀)
h₀-on-finMeetNeg (n ∷ ns) =
  h-meet-preserves-true h₀ (¬∞ (g∞ n)) (finMeetNeg∞ ns)
    (h₀-on-neg-gen n)
    (h₀-on-finMeetNeg ns)

-- Main theorem: finMeetNeg∞ ns ≠ 0 for any list
finMeetNeg∞-nonzero : (ns : List ℕ) → ¬ (finMeetNeg∞ ns ≡ 𝟘∞)
finMeetNeg∞-nonzero ns meet=0 = contradiction
  where
  h₀-meet=true : h₀ $cr (finMeetNeg∞ ns) ≡ true
  h₀-meet=true = h₀-on-finMeetNeg ns

  h₀-0=false : h₀ $cr 𝟘∞ ≡ false
  h₀-0=false = IsCommRingHom.pres0 (snd h₀)

  h₀-meet=false : h₀ $cr (finMeetNeg∞ ns) ≡ false
  h₀-meet=false = cong (h₀ $cr_) meet=0 ∙ h₀-0=false

  contradiction : ⊥
  contradiction = true≢false (sym h₀-meet=true ∙ h₀-meet=false)

-- =============================================================================
-- Characteristic 2 helpers (lines 6800-6812)
-- =============================================================================

private
  module BA∞ = BooleanAlgebraStr B∞

-- Export char2-B∞ for use in later parts
char2-B∞ : (x : ⟨ B∞ ⟩) → x +∞ x ≡ 𝟘∞
char2-B∞ x = BA∞.characteristic2 {x}

char2-B∞×B∞ : (z : ⟨ B∞×B∞ ⟩) → z +× z ≡ (𝟘∞ , 𝟘∞)
char2-B∞×B∞ (a , b) = cong₂ _,_ (char2-B∞ a) (char2-B∞ b)

-- =============================================================================
-- splitByParity helpers (lines 6814-6862)
-- =============================================================================

splitByParity-evens : List ℕ → List ℕ
splitByParity-evens ns = fst (splitByParity ns)

splitByParity-odds : List ℕ → List ℕ
splitByParity-odds ns = snd (splitByParity ns)

-- When isEven n = true, the evens list gets half n prepended
splitByParity-cons-even : (n : ℕ) (ns : List ℕ) → isEven n ≡ true →
  splitByParity-evens (n ∷ ns) ≡ half n ∷ splitByParity-evens ns
splitByParity-cons-even n ns even-n with isEven n | splitByParity ns
... | true  | (evens , odds) = refl
... | false | (evens , odds) = ex-falso (false≢true even-n)

-- When isEven n = false, the odds list gets half n prepended
splitByParity-cons-odd : (n : ℕ) (ns : List ℕ) → isEven n ≡ false →
  splitByParity-odds (n ∷ ns) ≡ half n ∷ splitByParity-odds ns
splitByParity-cons-odd n ns odd-n with isEven n | splitByParity ns
... | false | (evens , odds) = refl
... | true  | (evens , odds) = ex-falso (true≢false odd-n)

-- Key lemma: if both parity components are empty after splitByParity, then ns = []
splitByParity-nonempty : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in evens ≡ [] → odds ≡ [] → ns ≡ []
splitByParity-nonempty [] _ _ = refl
splitByParity-nonempty (n ∷ ns) evens=[] odds=[] = splitByParity-nonempty-aux (isEven n) refl
  where
  splitByParity-nonempty-aux : (b : Bool) → isEven n ≡ b → (n ∷ ns) ≡ []
  splitByParity-nonempty-aux true parity =
    let evens-eq = splitByParity-cons-even n ns parity
        contradiction : half n ∷ splitByParity-evens ns ≡ []
        contradiction = sym evens-eq ∙ evens=[]
    in ex-falso (¬cons≡nil contradiction)
  splitByParity-nonempty-aux false parity =
    let odds-eq = splitByParity-cons-odd n ns parity
        contradiction : half n ∷ splitByParity-odds ns ≡ []
        contradiction = sym odds-eq ∙ odds=[]
    in ex-falso (¬cons≡nil contradiction)

-- Contrapositive: non-empty ns gives non-empty evens or odds
splitByParity-ns-nonempty : (ns : List ℕ) → ¬ (ns ≡ []) →
  let (evens , odds) = splitByParity ns
  in ¬ ((evens ≡ []) × (odds ≡ []))
splitByParity-ns-nonempty ns ns≠[] (evens=[] , odds=[]) =
  ns≠[] (splitByParity-nonempty ns evens=[] odds=[])

-- =============================================================================
-- f-kernel on joinForm (lines 6864-6893)
-- =============================================================================

f-kernel-joinForm : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in fst f (finJoin∞ ns) ≡ (𝟘∞ , 𝟘∞) → ns ≡ []
f-kernel-joinForm ns fx=0 =
  let evens = splitByParity-evens ns
      odds = splitByParity-odds ns

      -- f(finJoin∞ ns) = (finJoin∞ evens, finJoin∞ odds)
      f-eq : fst f (finJoin∞ ns) ≡ (finJoin∞ evens , finJoin∞ odds)
      f-eq = f-on-finJoin ns

      f-split : (finJoin∞ evens , finJoin∞ odds) ≡ (𝟘∞ , 𝟘∞)
      f-split = sym f-eq ∙ fx=0

      evens-join=0 : finJoin∞ evens ≡ 𝟘∞
      evens-join=0 = cong fst f-split

      odds-join=0 : finJoin∞ odds ≡ 𝟘∞
      odds-join=0 = cong snd f-split

      evens=[] : evens ≡ []
      evens=[] = finJoin∞-zero→empty evens evens-join=0

      odds=[] : odds ≡ []
      odds=[] = finJoin∞-zero→empty odds odds-join=0

  in splitByParity-nonempty ns evens=[] odds=[]

-- =============================================================================
-- f-kernel on normal forms (lines 6895-7005)
-- =============================================================================

-- f-kernel on normal forms: proves kernel is trivial for normal form elements
f-kernel-normalForm : (nf : B∞-NormalForm) → fst f ⟦ nf ⟧nf ≡ (𝟘∞ , 𝟘∞) → ⟦ nf ⟧nf ≡ 𝟘∞
f-kernel-normalForm (joinForm ns) fx=0 =
  let ns=[] : ns ≡ []
      ns=[] = f-kernel-joinForm ns fx=0
  in cong finJoin∞ ns=[]
f-kernel-normalForm (meetNegForm ns) fx=0 =
  ex-falso (f-meetNeg-nonzero fx=0)
  where
  h' : ⟨ B∞×B∞ ⟩ → Bool
  h' (a , b) = h₀ $cr a

  h'-on-f-neg-gen-even : (k : ℕ) → h' (fst f (¬∞ (g∞ (2 ·ℕ k)))) ≡ true
  h'-on-f-neg-gen-even k =
    h' (fst f (¬∞ (g∞ (2 ·ℕ k))))
      ≡⟨ cong h' (f-pres-neg (g∞ (2 ·ℕ k))) ⟩
    h' (¬∞ (fst (fst f (g∞ (2 ·ℕ k)))) , ¬∞ (snd (fst f (g∞ (2 ·ℕ k)))))
      ≡⟨ cong (λ x → h' (¬∞ (fst x) , ¬∞ (snd x))) (f-even-gen k) ⟩
    h' (¬∞ (g∞ k) , ¬∞ 𝟘∞)
      ≡⟨ refl ⟩
    h₀ $cr (¬∞ (g∞ k))
      ≡⟨ h₀-on-neg-gen k ⟩
    true ∎

  h'-on-f-neg-gen-odd : (k : ℕ) → h' (fst f (¬∞ (g∞ (suc (2 ·ℕ k))))) ≡ true
  h'-on-f-neg-gen-odd k =
    h' (fst f (¬∞ (g∞ (suc (2 ·ℕ k)))))
      ≡⟨ cong h' (f-pres-neg (g∞ (suc (2 ·ℕ k)))) ⟩
    h' (¬∞ (fst (fst f (g∞ (suc (2 ·ℕ k))))) , ¬∞ (snd (fst f (g∞ (suc (2 ·ℕ k))))))
      ≡⟨ cong (λ x → h' (¬∞ (fst x) , ¬∞ (snd x))) (f-odd-gen k) ⟩
    h' (¬∞ 𝟘∞ , ¬∞ (g∞ k))
      ≡⟨ refl ⟩
    h₀ $cr (¬∞ 𝟘∞)
      ≡⟨ h-pres-neg-Bool h₀ 𝟘∞ ⟩
    notBool (h₀ $cr 𝟘∞)
      ≡⟨ cong notBool (IsCommRingHom.pres0 (snd h₀)) ⟩
    notBool false
      ≡⟨ refl ⟩
    true ∎

  h'-on-f-neg-gen : (n : ℕ) → h' (fst f (¬∞ (g∞ n))) ≡ true
  h'-on-f-neg-gen n = h'-on-f-neg-gen-aux (isEven n) refl
    where
    h'-on-f-neg-gen-aux : (b : Bool) → isEven n ≡ b → h' (fst f (¬∞ (g∞ n))) ≡ true
    h'-on-f-neg-gen-aux true even-n =
      let k = half n
          n=2k : n ≡ 2 ·ℕ k
          n=2k = sym (isEven→even n even-n)
      in subst (λ m → h' (fst f (¬∞ (g∞ m))) ≡ true) (sym n=2k) (h'-on-f-neg-gen-even k)
    h'-on-f-neg-gen-aux false odd-n =
      let k = half n
          n=2k+1 : n ≡ suc (2 ·ℕ k)
          n=2k+1 = sym (isEven→odd n odd-n)
      in subst (λ m → h' (fst f (¬∞ (g∞ m))) ≡ true) (sym n=2k+1) (h'-on-f-neg-gen-odd k)

  h'-pres-· : (x y : ⟨ B∞×B∞ ⟩) → h' (x ·× y) ≡ (h' x) and (h' y)
  h'-pres-· (a₁ , b₁) (a₂ , b₂) = IsCommRingHom.pres· (snd h₀) a₁ a₂

  h'-on-f-finMeetNeg : (ms : List ℕ) → h' (fst f (finMeetNeg∞ ms)) ≡ true
  h'-on-f-finMeetNeg [] =
    h' (fst f 𝟙∞)
      ≡⟨ cong h' f-pres1 ⟩
    h' (𝟙∞ , 𝟙∞)
      ≡⟨ refl ⟩
    h₀ $cr 𝟙∞
      ≡⟨ IsCommRingHom.pres1 (snd h₀) ⟩
    true ∎
  h'-on-f-finMeetNeg (m ∷ ms) =
    h' (fst f (finMeetNeg∞ (m ∷ ms)))
      ≡⟨ refl ⟩
    h' (fst f ((¬∞ (g∞ m)) ∧∞ (finMeetNeg∞ ms)))
      ≡⟨ cong h' (IsCommRingHom.pres· (snd f) (¬∞ (g∞ m)) (finMeetNeg∞ ms)) ⟩
    h' ((fst f (¬∞ (g∞ m))) ·× (fst f (finMeetNeg∞ ms)))
      ≡⟨ h'-pres-· (fst f (¬∞ (g∞ m))) (fst f (finMeetNeg∞ ms)) ⟩
    (h' (fst f (¬∞ (g∞ m)))) and (h' (fst f (finMeetNeg∞ ms)))
      ≡⟨ cong₂ _and_ (h'-on-f-neg-gen m) (h'-on-f-finMeetNeg ms) ⟩
    true and true
      ≡⟨ refl ⟩
    true ∎

  f-meetNeg-nonzero : fst f (finMeetNeg∞ ns) ≡ (𝟘∞ , 𝟘∞) → ⊥
  f-meetNeg-nonzero f-meetNeg=0 = false≢true (sym h'-on-0 ∙ h'-on-f-meetNeg-eq-0)
    where
    h'-on-0 : h' (𝟘∞ , 𝟘∞) ≡ false
    h'-on-0 = IsCommRingHom.pres0 (snd h₀)

    h'-on-f-meetNeg : h' (fst f (finMeetNeg∞ ns)) ≡ true
    h'-on-f-meetNeg = h'-on-f-finMeetNeg ns

    h'-on-f-meetNeg-eq-0 : h' (𝟘∞ , 𝟘∞) ≡ true
    h'-on-f-meetNeg-eq-0 = subst (λ z → h' z ≡ true) f-meetNeg=0 h'-on-f-meetNeg

-- =============================================================================
-- LLPO derivation from Stone Duality (lines 7073-7239)
-- =============================================================================

llpo-from-SD-aux : (h : Sp B∞-Booleω) →
  ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎ ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
llpo-from-SD-aux h = PT.rec llpo-is-prop go (Sp-f-surjective h)
  where
  evens-is-prop : isProp ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false)
  evens-is-prop = isPropΠ (λ k → isSetBool _ _)

  odds-is-prop : isProp ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
  odds-is-prop = isPropΠ (λ k → isSetBool _ _)

  postulate
    evens-odds-disjoint : ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) →
                          ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) → ⊥

  llpo-is-prop : isProp (((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
                         ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false))
  llpo-is-prop = isProp⊎ evens-is-prop odds-is-prop evens-odds-disjoint

  go : Σ[ h' ∈ Sp B∞×B∞-Booleω ] Sp-f h' ≡ h →
       ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
       ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
  go (h' , Sp-f-h'≡h) = go' (h' $cr B∞×B∞-Units.unit-left) refl
    where
    go' : (b : Bool) → h' $cr B∞×B∞-Units.unit-left ≡ b →
          ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
          ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
    go' true h'-left-true = ⊎.inr odds-zero-case
      where
      odds-zero-case : (k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false
      odds-zero-case k =
        h $cr (g∞ (suc (2 ·ℕ k)))
          ≡⟨ sym (funExt⁻ (cong fst Sp-f-h'≡h) (g∞ (suc (2 ·ℕ k)))) ⟩
        h' $cr (fst f (g∞ (suc (2 ·ℕ k))))
          ≡⟨ cong (h' $cr_) (f-odd-gen k) ⟩
        h' $cr (𝟘∞ , g∞ k)
          ≡⟨ h'-left-true→right-false h' h'-left-true (g∞ k) ⟩
        false ∎
    go' false h'-left-false = ⊎.inl evens-zero-case
      where
      open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞ ; _+_ to _+B∞_)
      open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×local_)
      open BooleanRingStr (snd BoolBR) using () renaming (_+_ to _⊕Bool_)

      h'-pres1 : h' $cr (𝟙B∞ , 𝟙B∞) ≡ true
      h'-pres1 = IsCommRingHom.pres1 (snd h')

      open CommRingStr (snd (BooleanRing→CommRing B∞)) using () renaming (+IdL to +left-unit ; +IdR to +right-unit)

      unit-sum' : (𝟙B∞ , 𝟘∞) +×local (𝟘∞ , 𝟙B∞) ≡ (𝟙B∞ , 𝟙B∞)
      unit-sum' = cong₂ _,_ (+right-unit 𝟙B∞) (+left-unit 𝟙B∞)

      h'-pres+ : (a b : ⟨ B∞×B∞ ⟩) → h' $cr (a +×local b) ≡ (h' $cr a) ⊕Bool (h' $cr b)
      h'-pres+ = IsCommRingHom.pres+ (snd h')

      false-⊕-id : (b : Bool) → false ⊕Bool b ≡ b
      false-⊕-id = CommRingStr.+IdL (snd (BooleanRing→CommRing BoolBR))

      h'-right-true : h' $cr B∞×B∞-Units.unit-right ≡ true
      h'-right-true =
        h' $cr B∞×B∞-Units.unit-right
          ≡⟨ sym (false-⊕-id (h' $cr B∞×B∞-Units.unit-right)) ⟩
        false ⊕Bool (h' $cr B∞×B∞-Units.unit-right)
          ≡⟨ cong (λ b → b ⊕Bool (h' $cr B∞×B∞-Units.unit-right)) (sym h'-left-false) ⟩
        (h' $cr B∞×B∞-Units.unit-left) ⊕Bool (h' $cr B∞×B∞-Units.unit-right)
          ≡⟨ sym (h'-pres+ B∞×B∞-Units.unit-left B∞×B∞-Units.unit-right) ⟩
        h' $cr (B∞×B∞-Units.unit-left +× B∞×B∞-Units.unit-right)
          ≡⟨ cong (h' $cr_) unit-sum' ⟩
        h' $cr (𝟙B∞ , 𝟙B∞)
          ≡⟨ h'-pres1 ⟩
        true ∎

      evens-zero-case : (k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false
      evens-zero-case k =
        h $cr (g∞ (2 ·ℕ k))
          ≡⟨ sym (funExt⁻ (cong fst Sp-f-h'≡h) (g∞ (2 ·ℕ k))) ⟩
        h' $cr (fst f (g∞ (2 ·ℕ k)))
          ≡⟨ cong (h' $cr_) (f-even-gen k) ⟩
        h' $cr (g∞ k , 𝟘∞)
          ≡⟨ h'-right-true→left-false h' h'-right-true (g∞ k) ⟩
        false ∎

-- Main LLPO theorem from Stone Duality
llpo-from-SD : LLPO
llpo-from-SD α = transport-llpo (llpo-from-SD-aux h)
  where
  h : Sp B∞-Booleω
  h = ℕ∞-to-SpB∞ α

  roundtrip : SpB∞-to-ℕ∞ h ≡ α
  roundtrip = SpB∞-roundtrip α

  seq-eq : (n : ℕ) → h $cr (g∞ n) ≡ fst α n
  seq-eq n = funExt⁻ (cong fst roundtrip) n

  transport-llpo : ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
                   ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) →
                   ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎
                   ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false)
  transport-llpo (⊎.inl evens) = ⊎.inl (λ k → sym (seq-eq (2 ·ℕ k)) ∙ evens k)
  transport-llpo (⊎.inr odds) = ⊎.inr (λ k → sym (seq-eq (suc (2 ·ℕ k))) ∙ odds k)

-- =============================================================================
-- Normal form infrastructure (lines 7320-7500)
-- =============================================================================

-- Helper: generator as normal form
g∞-nf : ℕ → B∞-NormalForm
g∞-nf n = joinForm (n ∷ [])

-- Generator matches its normal form
g∞-nf-correct : (n : ℕ) → ⟦ g∞-nf n ⟧nf ≡ g∞ n
g∞-nf-correct n =
  ⟦ joinForm (n ∷ []) ⟧nf
    ≡⟨ refl ⟩
  finJoin∞ (n ∷ [])
    ≡⟨ refl ⟩
  g∞ n ∨∞ finJoin∞ []
    ≡⟨ refl ⟩
  g∞ n ∨∞ 𝟘∞
    ≡⟨ zero-join-right (g∞ n) ⟩
  g∞ n ∎

-- Unit (1) as normal form
𝟙∞-nf : B∞-NormalForm
𝟙∞-nf = meetNegForm []

-- Unit matches its normal form
𝟙∞-nf-correct : ⟦ 𝟙∞-nf ⟧nf ≡ 𝟙∞
𝟙∞-nf-correct = refl

-- Zero (0) as normal form
𝟘∞-nf : B∞-NormalForm
𝟘∞-nf = joinForm []

-- Zero matches its normal form
𝟘∞-nf-correct : ⟦ 𝟘∞-nf ⟧nf ≡ 𝟘∞
𝟘∞-nf-correct = refl

-- Negation of normal forms
neg-nf : B∞-NormalForm → B∞-NormalForm
neg-nf (joinForm ns) = meetNegForm ns
neg-nf (meetNegForm ns) = joinForm ns

-- De Morgan modules
module B∞-BoolAlg = BooleanAlgebraStr B∞

neg-distrib-join : (a b : ⟨ B∞ ⟩) → ¬∞ (a ∨∞ b) ≡ (¬∞ a) ∧∞ (¬∞ b)
neg-distrib-join a b = B∞-BoolAlg.DeMorgan¬∨ {x = a} {y = b}

-- De Morgan for finite joins: ¬(g_1 ∨ ... ∨ g_n) = ¬g_1 ∧ ... ∧ ¬g_n
neg-finJoin : (ns : List ℕ) → ¬∞ (finJoin∞ ns) ≡ finMeetNeg∞ ns
neg-finJoin [] = BooleanRingStr.+IdR (snd B∞) 𝟙∞
neg-finJoin (n ∷ ns) =
  ¬∞ (finJoin∞ (n ∷ ns))
    ≡⟨ refl ⟩
  ¬∞ (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ neg-distrib-join (g∞ n) (finJoin∞ ns) ⟩
  (¬∞ (g∞ n)) ∧∞ (¬∞ (finJoin∞ ns))
    ≡⟨ cong ((¬∞ (g∞ n)) ∧∞_) (neg-finJoin ns) ⟩
  (¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns
    ≡⟨ refl ⟩
  finMeetNeg∞ (n ∷ ns) ∎

neg-distrib-meet : (a b : ⟨ B∞ ⟩) → ¬∞ ((¬∞ a) ∧∞ (¬∞ b)) ≡ a ∨∞ b
neg-distrib-meet a b =
  ¬∞ ((¬∞ a) ∧∞ (¬∞ b))
    ≡⟨ B∞-BoolAlg.DeMorgan¬∧ {x = ¬∞ a} {y = ¬∞ b} ⟩
  (¬∞ (¬∞ a)) ∨∞ (¬∞ (¬∞ b))
    ≡⟨ cong₂ _∨∞_ (B∞-BoolAlg.¬Invol {x = a}) (B∞-BoolAlg.¬Invol {x = b}) ⟩
  a ∨∞ b ∎

-- De Morgan for finite meets of negations
neg-finMeetNeg : (ns : List ℕ) → ¬∞ (finMeetNeg∞ ns) ≡ finJoin∞ ns
neg-finMeetNeg [] = char2-B∞ 𝟙∞
neg-finMeetNeg (n ∷ ns) =
  ¬∞ (finMeetNeg∞ (n ∷ ns))
    ≡⟨ refl ⟩
  ¬∞ ((¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns)
    ≡⟨ cong (λ z → ¬∞ ((¬∞ (g∞ n)) ∧∞ z)) (sym (neg-finJoin ns)) ⟩
  ¬∞ ((¬∞ (g∞ n)) ∧∞ (¬∞ (finJoin∞ ns)))
    ≡⟨ neg-distrib-meet (g∞ n) (finJoin∞ ns) ⟩
  (g∞ n) ∨∞ finJoin∞ ns
    ≡⟨ refl ⟩
  finJoin∞ (n ∷ ns) ∎

-- Negation preserves normal form correctness
neg-nf-correct : (nf : B∞-NormalForm) → ⟦ neg-nf nf ⟧nf ≡ ¬∞ (⟦ nf ⟧nf)
neg-nf-correct (joinForm ns) = sym (neg-finJoin ns)
neg-nf-correct (meetNegForm ns) = sym (neg-finMeetNeg ns)

-- =============================================================================
-- Closure operations for normal forms (lines 7446-7488)
-- =============================================================================

-- Join of two joinForms: union of index lists
join-joinForm : List ℕ → List ℕ → B∞-NormalForm
join-joinForm ns ms = joinForm (ns ++ ms)

-- Meet of two meetNegForms: union of index lists
meet-meetNegForm : List ℕ → List ℕ → B∞-NormalForm
meet-meetNegForm ns ms = meetNegForm (ns ++ ms)

