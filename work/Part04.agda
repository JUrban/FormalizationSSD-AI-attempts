{-# OPTIONS --cubical --guardedness #-}

module work.Part04 where

open import work.Part03 public

-- Additional imports for Part04
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; isoToIsEquiv; Iso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; _⊕_)
open import Cubical.Data.Bool.Properties using (⊕-comm; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; freeBA-universal-property; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty renaming (rec to ex-falso)

-- =============================================================================
-- Part 04: work.agda lines 4119-5415 (Bool²-presentation, B∞×B∞-Operations)
-- =============================================================================

module Bool²-presentation where
  open BooleanRingStr (snd (freeBA ℕ)) using (𝟙) renaming (_+_ to _+free_ ; _·_ to _·free_)

  -- The generators in freeBA ℕ
  g₀ : ⟨ freeBA ℕ ⟩
  g₀ = generator 0

  g₁ : ⟨ freeBA ℕ ⟩
  g₁ = generator 1

  -- The relations for Bool²
  -- relBool² 0 = g₀ · g₁ (atoms are orthogonal)
  -- relBool² 1 = 𝟙 + g₀ + g₁ (atoms sum to 1 in Boolean ring means g₀ ⊕ g₁ = 1)
  -- relBool² (n+2) = generator (n+2) (kill extra generators)
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
  -- This allows us to factor through the quotient
  -- Note: private has no effect on open statements, so we omit it
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
    -- (𝟙 +free g₀) +free g₁ ↦ ((true,true) + (true,false)) + (false,true)
    --                       = (false,true) + (false,true) = (false,false) = 0
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
    -- generator (n+2) ↦ (false, false) = 0
    fst freeBool→Bool² (generator (suc (suc n)))
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ (suc (suc n)) ⟩
    (false , false)
      ≡⟨ refl ⟩
    𝟘² ∎

  -- The induced homomorphism from the quotient to Bool²
  quotient→Bool² : BoolHom Bool²-quotient Bool²
  quotient→Bool² = QB.inducedHom Bool² freeBool→Bool² freeBool→Bool²-on-rels

  -- The forward map: Bool² → quotient
  -- (true,false) ↦ [g₀], (false,true) ↦ [g₁], etc.
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
    -- From relation: 𝟙 + g₀ + g₁ = 0, so adding 𝟙 to both sides: g₀ + g₁ = 𝟙 (since 𝟙 + 𝟙 = 0)
    g₀+g₁≡𝟙Q : fst π g₀ +Q fst π g₁ ≡ 𝟙Q
    g₀+g₁≡𝟙Q = step6 ∙ step7 ∙ step8 ∙ step9
      where
        -- From the relation: fst π (relBool² 1) = 𝟘Q
        rel1-eq : fst π (𝟙 +free g₀ +free g₁) ≡ 𝟘Q
        rel1-eq = QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} 1
        -- Using pres+ and pres1 to relate expressions
        step2 : fst π (𝟙 +free g₀) ≡ fst π 𝟙 +Q fst π g₀
        step2 = IsCommRingHom.pres+ (snd π) 𝟙 g₀
        step3 : fst π 𝟙 ≡ 𝟙Q
        step3 = IsCommRingHom.pres1 (snd π)
        -- Combining: 𝟙Q + (fst π g₀) + (fst π g₁) = 𝟘Q
        -- First go from 𝟙Q to fst π (𝟙 +free g₀)
        pathAB : 𝟙Q +Q fst π g₀ +Q fst π g₁ ≡ fst π (𝟙 +free g₀) +Q fst π g₁
        pathAB = cong (λ z → z +Q fst π g₀ +Q fst π g₁) (sym step3) ∙
                 cong (_+Q fst π g₁) (sym step2)
        -- Then go from fst π (𝟙 +free g₀) +Q fst π g₁ to fst π (𝟙 +free g₀ +free g₁)
        pathC : fst π (𝟙 +free g₀) +Q fst π g₁ ≡ fst π (𝟙 +free g₀ +free g₁)
        pathC = sym (IsCommRingHom.pres+ (snd π) (𝟙 +free g₀) g₁)
        combined : 𝟙Q +Q fst π g₀ +Q fst π g₁ ≡ 𝟘Q
        combined = pathAB ∙ pathC ∙ rel1-eq
        -- Now: (𝟙Q + fst π g₀) + fst π g₁ = 𝟘Q
        -- Add 𝟙Q to both sides (using char2: 𝟙Q + 𝟙Q = 𝟘Q)
        step4 : 𝟙Q +Q (𝟙Q +Q fst π g₀ +Q fst π g₁) ≡ 𝟙Q +Q 𝟘Q
        step4 = cong (𝟙Q +Q_) combined
        step5 : 𝟙Q +Q 𝟘Q ≡ 𝟙Q
        step5 = BooleanRingStr.+IdR (snd Bool²-quotient) 𝟙Q
        -- Use 0 + x = x to prepend 𝟘Q
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

    -- Derived helper: g₀ = g₁ + 1 (from g₁ + g₀ = 1, using char2)
    -- Proof: g₁ + g₀ = 1, so g₁ + (g₁ + g₀) = g₁ + 1, so (g₁ + g₁) + g₀ = g₁ + 1, so 0 + g₀ = g₁ + 1, so g₀ = g₁ + 1
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
    -- For Bool², we can prove this by case analysis on the 4 elements
    neg≡self² : (x : ⟨ Bool² ⟩) → BooleanRingStr.-_ (snd Bool²) x ≡ x
    neg≡self² (false , false) = refl
    neg≡self² (false , true) = refl
    neg≡self² (true , false) = refl
    neg≡self² (true , true) = refl

    -- Same property for the quotient ring: -x = x
    -- Using the -IsId lemma from BooleanAlgebraStr which applies to any Boolean ring
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
  Bool²→quotient-pres+ (false , true) (false , true) =
    -- (false, true) + (false, true) = (false, false) = 0
    -- π(g₁) + π(g₁) = 0 (in Boolean ring, x + x = 0)
    sym (char2Q (fst π g₁))
  Bool²→quotient-pres+ (false , true) (true , false) =
    -- (false, true) + (true, false) = (true, true) = 1
    -- We need: 1 = π(g₁) + π(g₀), i.e., sym (g₁+g₀≡𝟙Q)
    sym g₁+g₀≡𝟙Q
  Bool²→quotient-pres+ (false , true) (true , true) =
    -- (false, true) + (true, true) = (true, false)
    -- We need: π(g₀) = π(g₁) + 1
    -- Using helper: g₀≡g₁+𝟙Q
    g₀≡g₁+𝟙Q
  Bool²→quotient-pres+ (true , false) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (true , false) (false , true) =
    -- Symmetric to (false, true) + (true, false)
    cong Bool²→quotient-fun (cong₂ _,_ (⊕-comm true false) (⊕-comm false true)) ∙
    Bool²→quotient-pres+ (false , true) (true , false) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀)
  Bool²→quotient-pres+ (true , false) (true , false) =
    sym (char2Q (fst π g₀))
  Bool²→quotient-pres+ (true , false) (true , true) =
    -- (true, false) + (true, true) = (false, true)
    -- Goal: π g₁ ≡ π g₀ +Q 𝟙Q
    -- Using helper: g₁≡g₀+𝟙Q (which proves fst π g₁ ≡ fst π g₀ +Q 𝟙Q)
    g₁≡g₀+𝟙Q
  Bool²→quotient-pres+ (true , true) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (true , true) (false , true) =
    -- Symmetric case
    cong Bool²→quotient-fun (cong₂ _,_ (⊕-comm true false) (⊕-comm true true)) ∙
    Bool²→quotient-pres+ (false , true) (true , true) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) 𝟙Q
  Bool²→quotient-pres+ (true , true) (true , false) =
    cong Bool²→quotient-fun (cong₂ _,_ (⊕-comm true true) (⊕-comm true false)) ∙
    Bool²→quotient-pres+ (true , false) (true , true) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₀) 𝟙Q
  Bool²→quotient-pres+ (true , true) (true , true) =
    sym (char2Q 𝟙Q)

  Bool²→quotient-pres· : (x y : ⟨ Bool² ⟩) → Bool²→quotient-fun (x ·² y) ≡ Bool²→quotient-fun x ·Q Bool²→quotient-fun y
  Bool²→quotient-pres· (false , false) y = sym annihilLQ
  Bool²→quotient-pres· (false , true) (false , false) = sym annihilRQ
  Bool²→quotient-pres· (false , true) (false , true) =
    sym (BooleanRingStr.·Idem (snd Bool²-quotient) (fst π g₁))
  Bool²→quotient-pres· (false , true) (true , false) =
    -- (false, true) · (true, false) = (false, false) = 0
    -- Goal: π(g₁) · π(g₀) = 0
    -- Using helper: g₁·g₀≡𝟘Q
    sym g₁·g₀≡𝟘Q
  Bool²→quotient-pres· (false , true) (true , true) =
    -- (false, true) · (true, true) = (false, true)
    -- π(g₁) · 1 = π(g₁)
    sym (BooleanRingStr.·IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres· (true , false) (false , false) = sym annihilRQ
  Bool²→quotient-pres· (true , false) (false , true) =
    -- (true, false) · (false, true) = (false, false) = 0
    -- π(g₀) · π(g₁) = 0 (same as the symmetric case)
    Bool²→quotient-pres· (false , true) (true , false) ∙
    BooleanRingStr.·Comm (snd Bool²-quotient) _ _
  Bool²→quotient-pres· (true , false) (true , false) =
    sym (BooleanRingStr.·Idem (snd Bool²-quotient) (fst π g₀))
  Bool²→quotient-pres· (true , false) (true , true) =
    sym (BooleanRingStr.·IdR (snd Bool²-quotient) _)
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
      -- In Boolean ring, -x = x, so f(-x) = f(x) = -f(x)
      -- We use: cong f (neg≡self² x) ∙ sym (neg≡selfQ (f x))
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
  -- This requires showing the composite is the identity on generators and using uniqueness

  -- The composite Bool²→quotient ∘ quotient→Bool² when applied to π(gen n)
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

  -- The composite as a homomorphism freeBA ℕ → Bool²-quotient
  composite-hom-on-gens : (n : ℕ) → fst (Bool²→quotient ∘cr quotient→Bool² ∘cr π) (generator n) ≡ fst π (generator n)
  composite-hom-on-gens = composite-on-gens

  -- By universal property, composite-hom = π (both extend gens ↦ π(gens))
  -- Path order: composite ≡ inducedBA ≡ π
  composite-eq-π : Bool²→quotient ∘cr quotient→Bool² ∘cr π ≡ π
  composite-eq-π = sym (inducedBAHomUnique ℕ Bool²-quotient (fst π ∘ generator)
                                      (Bool²→quotient ∘cr quotient→Bool² ∘cr π)
                                      (funExt composite-on-gens)) ∙
                   inducedBAHomUnique ℕ Bool²-quotient (fst π ∘ generator) π refl

  -- Since π is surjective, this means Bool²→quotient ∘ quotient→Bool² = id
  -- The quotient uses QB./Im which is built on IQ./Im (SetQuotient)
  -- We use the equality of homomorphisms composite-eq-π to get pointwise equality
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

-- The two homomorphisms BoolBR × BoolBR → BoolBR are the projections
-- π₁ : (a, b) ↦ a
-- π₂ : (a, b) ↦ b

proj₁-Bool² : ⟨ Bool² ⟩ → Bool
proj₁-Bool² = fst

proj₂-Bool² : ⟨ Bool² ⟩ → Bool
proj₂-Bool² = snd

-- π₁ is a Boolean ring homomorphism
proj₁-Bool²-hom : BoolHom Bool² BoolBR
fst proj₁-Bool²-hom = proj₁-Bool²
snd proj₁-Bool²-hom .IsCommRingHom.pres0 = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres1 = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres+ _ _ = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres· _ _ = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres- _ = refl

-- π₂ is a Boolean ring homomorphism
proj₂-Bool²-hom : BoolHom Bool² BoolBR
fst proj₂-Bool²-hom = proj₂-Bool²
snd proj₂-Bool²-hom .IsCommRingHom.pres0 = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres1 = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres+ _ _ = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres· _ _ = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres- _ = refl

-- Sp(BoolBR × BoolBR) has exactly 2 elements: proj₁ and proj₂
-- This is because any h : Bool² → BoolBR is determined by h(1,0) and h(0,1)
-- which must satisfy:
-- - h(1,0) + h(0,1) = h(1,1) = 1  (h preserves 1)
-- - h(1,0) · h(0,1) = h(0,0) = 0  (h preserves 0 and multiplication)
-- In Bool with ⊕ and ∧, the only solutions are (1,0) and (0,1)

-- Classification of homomorphisms: any h equals proj₁ or proj₂
-- Using helper function pattern instead of inspect (Cubical Agda compatible)
classify-Bool²-hom : (h : Sp Bool²-Booleω) → (h ≡ proj₁-Bool²-hom) ⊎.⊎ (h ≡ proj₂-Bool²-hom)
classify-Bool²-hom h = helper (fst h Bool²-unit-left) refl
  where
  h≡proj₁ : fst h Bool²-unit-left ≡ true → h ≡ proj₁-Bool²-hom
  h≡proj₁ h-ul-true = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing Bool²)) f (snd (BooleanRing→CommRing BoolBR))) (sym funEq)
    where
    -- h(0,1) = h((1,1) + (1,0)) = h(1,1) + h(1,0) = 1 + h(1,0) = 1 ⊕ true = false
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
    -- h(true,false) = true, h(false,true) = false means h = π₁
    funEq : proj₁-Bool² ≡ fst h
    funEq = funExt λ { (false , false) → sym (IsCommRingHom.pres0 (snd h))
                     ; (false , true) → sym h-ur
                     ; (true , false) → sym h-ul-true
                     ; (true , true) → sym (IsCommRingHom.pres1 (snd h)) }

  h≡proj₂ : fst h Bool²-unit-left ≡ false → h ≡ proj₂-Bool²-hom
  h≡proj₂ h-ul-false = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing Bool²)) f (snd (BooleanRing→CommRing BoolBR))) (sym funEq)
    where
    -- h(0,1) = 1 ⊕ h(1,0) = 1 ⊕ false = true
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

  helper : (b : Bool) → fst h Bool²-unit-left ≡ b → (h ≡ proj₁-Bool²-hom) ⊎.⊎ (h ≡ proj₂-Bool²-hom)
  helper true = λ eq → ⊎.inl (h≡proj₁ eq)
  helper false = λ eq → ⊎.inr (h≡proj₂ eq)

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
... | ⊎.inl h≡proj₁ = cong Bool→Sp-Bool² (cong (λ g → fst g Bool²-unit-left) h≡proj₁) ∙ sym h≡proj₁
... | ⊎.inr h≡proj₂ = cong Bool→Sp-Bool² (cong (λ g → fst g Bool²-unit-left) h≡proj₂) ∙ sym h≡proj₂

-- Roundtrip 2: Sp-Bool²→Bool ∘ Bool→Sp-Bool² = id
Bool→Sp-Bool²→Bool : (b : Bool) → Sp-Bool²→Bool (Bool→Sp-Bool² b) ≡ b
Bool→Sp-Bool²→Bool true = refl
Bool→Sp-Bool²→Bool false = refl

-- The equivalence Sp(BoolBR × BoolBR) ≃ Bool
Sp-Bool²≃Bool : Sp Bool²-Booleω ≃ Bool
Sp-Bool²≃Bool = isoToEquiv (iso Sp-Bool²→Bool Bool→Sp-Bool² Bool→Sp-Bool²→Bool Sp-Bool²→Bool→Sp-Bool²)

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
-- The map f : B∞ → B∞ × B∞ for LLPO
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
open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; 𝟘 to 𝟘×) public

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

-- When both indices have the same parity and div2 gives different values,
-- the product is zero because g∞ (div2 m) ·∞ g∞ (div2 n) = 0
-- (since div2 m ≠ div2 n means the generators are distinct)

-- Helper: different div2 values implies different generators
div2-neq→gen-product-zero : (m n : ℕ) → ¬ (div2 m ≡ div2 n) →
  g∞ (div2 m) ·∞ g∞ (div2 n) ≡ 𝟘∞
div2-neq→gen-product-zero m n neq = g∞-distinct-mult-zero (div2 m) (div2 n) neq

-- Injectivity of div2 on even/odd numbers
-- If parity m = parity n = true (both even) and div2 m = div2 n, then m = n
-- If parity m = parity n = false (both odd) and div2 m = div2 n, then m = n
-- We prove this by showing: m = 2 * div2 m when parity m = true
--                           m = 2 * div2 m + 1 when parity m = false

-- Helper: suc a + suc b = suc (suc (a + b))
-- suc a + b = suc (a + b) and a + suc b = suc (a + b)
-- so suc a + suc b = suc (a + suc b) = suc (suc (a + b))
double-div2-even : (n : ℕ) → parity n ≡ true → n ≡ div2 n +ℕ div2 n
double-div2-even zero _ = refl
double-div2-even (suc zero) p = ex-falso (true≢false (sym p))  -- parity 1 = false ≠ true
double-div2-even (suc (suc n)) p =
  -- div2 (suc (suc n)) = suc (div2 n), so we need:
  -- suc (suc n) = suc (div2 n) + suc (div2 n)
  -- suc (div2 n) + suc (div2 n) = suc (div2 n + suc (div2 n))    [by def of +]
  --                             = suc (suc (div2 n + div2 n))    [by +-suc]
  suc (suc n) ≡⟨ cong (suc ∘ suc) (double-div2-even n p) ⟩
  suc (suc (div2 n +ℕ div2 n)) ≡⟨ cong suc (sym (+-suc (div2 n) (div2 n))) ⟩
  suc (div2 n +ℕ suc (div2 n)) ∎
  -- Note: suc (div2 n) + suc (div2 n) ≡ suc (div2 n + suc (div2 n)) definitionally

double-div2-odd : (n : ℕ) → parity n ≡ false → n ≡ suc (div2 n +ℕ div2 n)
double-div2-odd zero p = ex-falso (true≢false p)  -- parity 0 = true ≠ false
double-div2-odd (suc zero) _ = refl
double-div2-odd (suc (suc n)) p =
  -- div2 (suc (suc n)) = suc (div2 n), so we need:
  -- suc (suc n) = suc (suc (div2 n) + suc (div2 n))
  -- suc (div2 n) + suc (div2 n) = suc (div2 n + suc (div2 n))    [by def of +]
  --                             = suc (suc (div2 n + div2 n))    [by +-suc]
  -- so suc (suc (div2 n) + suc (div2 n)) = suc (suc (suc (div2 n + div2 n)))
  suc (suc n) ≡⟨ cong (suc ∘ suc) (double-div2-odd n p) ⟩
  suc (suc (suc (div2 n +ℕ div2 n))) ≡⟨ cong (suc ∘ suc) (sym (+-suc (div2 n) (div2 n))) ⟩
  suc (suc (div2 n +ℕ suc (div2 n))) ∎
  -- Note: suc (suc (div2 n)) + suc (div2 n) ≡ suc (suc (div2 n) + suc (div2 n))
  --                                        ≡ suc (suc (div2 n + suc (div2 n))) definitionally

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
-- Constructing the full homomorphism f : B∞ → B∞×B∞
-- =============================================================================

-- Step 1: Use the universal property of freeBA ℕ to get a map freeBA ℕ → B∞×B∞
-- This uses inducedBAHom from FreeBool.agda
open import BooleanRing.FreeBooleanRing.FreeBool using (inducedBAHom; generator; evalBAInduce)

-- The induced homomorphism from freeBA ℕ to B∞×B∞
f-free : BoolHom (freeBA ℕ) B∞×B∞
f-free = inducedBAHom ℕ B∞×B∞ f-on-gen

-- Key property: f-free agrees with f-on-gen on generators
f-free-on-gen : fst f-free ∘ generator ≡ f-on-gen
f-free-on-gen = evalBAInduce ℕ B∞×B∞ f-on-gen

-- Step 2: Show that f-free sends relB∞ k to (0, 0) for all k
-- This follows from the fact that relB∞ k = gen a · gen (a + suc d)
-- for some a, d, and f-free preserves multiplication

-- First, recall that the generator in freeBA ℕ is 'generator' and
-- the generator in B∞ is g∞ = fst π∞ ∘ gen
-- The relation is: gen m · gen n = 0 in B∞ for m ≠ n

-- Key: f-free(gen m · gen n) = f-free(gen m) ·× f-free(gen n)
--                             = f-on-gen m ·× f-on-gen n  (by f-free-on-gen)
--                             = (0, 0) for m ≠ n         (by f-respects-relations)

-- The product in freeBA ℕ
-- Note: private has no effect on open statements
open BooleanRingStr (snd (freeBA ℕ)) using () renaming (_·_ to _·free_)

-- Homomorphism property of f-free
f-free-pres· : (x y : ⟨ freeBA ℕ ⟩) → fst f-free (x ·free y) ≡ (fst f-free x) ·× (fst f-free y)
f-free-pres· x y = IsCommRingHom.pres· (snd f-free) x y

-- The crucial lemma: f-free sends products of distinct generators to zero
f-free-distinct-zero : (m n : ℕ) → ¬ (m ≡ n) →
  fst f-free (gen m ·free gen n) ≡ (𝟘∞ , 𝟘∞)
f-free-distinct-zero m n m≠n =
  fst f-free (gen m ·free gen n)             ≡⟨ f-free-pres· (gen m) (gen n) ⟩
  (fst f-free (gen m)) ·× (fst f-free (gen n)) ≡⟨ cong₂ _·×_ (funExt⁻ f-free-on-gen m) (funExt⁻ f-free-on-gen n) ⟩
  f-on-gen m ·× f-on-gen n                    ≡⟨ f-respects-relations m n m≠n ⟩
  (𝟘∞ , 𝟘∞) ∎

-- Now we need to show that f-free sends relB∞ k to (0, 0)
-- Recall: relB∞ k = relB∞-from-pair (cantorUnpair k) = gen a · gen (a + suc d)
-- where (a, d) = cantorUnpair k

-- Since a < a + suc d, we have a ≠ a + suc d
-- Proof: if a = a + suc d, then 0 = suc d (contradiction)
-- We use: a + 0 = a = a + suc d → 0 = suc d
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
-- B∞ = freeBA ℕ /Im relB∞
-- We have f-free : freeBA ℕ → B∞×B∞ with f-free(relB∞ k) = 0 for all k
-- So we get f : B∞ → B∞×B∞

f : BoolHom B∞ B∞×B∞
f = QB.inducedHom B∞×B∞ f-free f-free-on-relB∞

-- =============================================================================
-- f applied to generators (needed for f-on-finJoin)
-- =============================================================================

-- f applied to generators: fst f (g∞ n) = f-on-gen n
-- This follows from f = QB.inducedHom which satisfies f ∘ π∞ = f-free
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

-- Helper: 2 ·ℕ k = k +ℕ k (multiplication computes this way)
2·-is-double : (k : ℕ) → 2 ·ℕ k ≡ k +ℕ k
2·-is-double k = cong (k +ℕ_) (+-zero k)

-- f applied to odd generators gives right factor
-- f(g_{2k+1}) = f-on-gen(2k+1) = (0, g_k) since parity(2k+1) = false
f-odd-gen : (k : ℕ) → fst f (g∞ (suc (2 ·ℕ k))) ≡ (𝟘∞ , g∞ k)
f-odd-gen k =
  fst f (g∞ (suc (2 ·ℕ k)))
    ≡⟨ f-on-gen-eq (suc (2 ·ℕ k)) ⟩
  f-on-gen (suc (2 ·ℕ k))
    ≡⟨ f-on-gen-odd k ⟩
  (𝟘∞ , g∞ k) ∎
  where
  -- Show f-on-gen (suc (2k)) computes to (0, g_k)
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
-- f(g_{2k}) = f-on-gen(2k) = (g_k, 0) since parity(2k) = true
f-even-gen : (k : ℕ) → fst f (g∞ (2 ·ℕ k)) ≡ (g∞ k , 𝟘∞)
f-even-gen k =
  fst f (g∞ (2 ·ℕ k))
    ≡⟨ f-on-gen-eq (2 ·ℕ k) ⟩
  f-on-gen (2 ·ℕ k)
    ≡⟨ f-on-gen-even k ⟩
  (g∞ k , 𝟘∞) ∎
  where
  -- Show f-on-gen (2k) computes to (g_k, 0)
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
-- Injectivity of f (tex line 567-583)
-- =============================================================================

-- The proof of injectivity uses the following argument:
-- If x ≠ 0 in B∞, then x can be written in a normal form involving generators
-- When we apply f, the generators get split into even and odd positions
-- Since x ≠ 0, at least one of the two factors in f(x) is nonzero

-- For now, we postulate this as the proof requires detailed analysis of
-- the structure of elements in B∞ as set quotients
--
-- PROOF OUTLINE (from tex lines 567-583):
-- 1. Any x ∈ B∞ can be written uniquely as:
--    - ⋁_{i∈I} g_i (join of generators) for finite I, OR
--    - ⋀_{i∈I} ¬g_i (meet of negated generators) for finite I
--    (This is the "normal form" or "conjunctive normal form" for B∞)
--
-- 2. For x = ⋁_{i∈I} g_i:
--    f(x) = (⋁_{k: 2k∈I} g_k, ⋁_{k: 2k+1∈I} g_k)
--    If f(x) = 0, then both I₀ = {k | 2k ∈ I} and I₁ = {k | 2k+1 ∈ I} are empty
--    Therefore I = ∅ and x = 0.
--
-- 3. For x = ⋀_{i∈I} ¬g_i:
--    f(x) = (⋀_{k: 2k∈I} ¬g_k, ⋀_{k: 2k+1∈I} ¬g_k)
--    Since each component is either 1 (if corresponding I_j = ∅) or a non-zero
--    meet of negated generators, f(x) ≠ 0.
--
-- 4. Conclusion: kernel of f is trivial, so f is injective.
--
-- TO FORMALIZE: Need normal form theorem for elements of B∞.

-- =============================================================================
-- Normal Form Infrastructure for B∞ (preparation for f-injective)
-- =============================================================================

-- In Boolean rings, the "join" of elements is: a ∨ b = a + b + a·b
-- This is the lattice join in the Boolean algebra structure
-- For B∞, elements are either:
--   - Finite joins of generators: ⋁_{i∈I} g_i
--   - Finite meets of negated generators: ⋀_{i∈I} ¬g_i

-- Boolean ring operations in B∞
open BooleanRingStr (snd B∞) using () renaming (_+_ to _+∞_ ; -_ to -∞_) public

-- Join in a Boolean ring: a ∨ b = a + b + a·b
_∨∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
a ∨∞ b = a +∞ b +∞ (a ·∞ b)

-- Meet in a Boolean ring: a ∧ b = a · b
_∧∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
a ∧∞ b = a ·∞ b

-- Negation in a Boolean ring: ¬a = 1 + a
¬∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩
¬∞ a = 𝟙∞ +∞ a

-- Finite join of generators: for a list of indices, compute ⋁_{i∈list} g_i
-- Using a simple recursive definition for now
open import Cubical.Data.List hiding (map)

finJoin∞ : List ℕ → ⟨ B∞ ⟩
finJoin∞ [] = 𝟘∞
finJoin∞ (n ∷ ns) = g∞ n ∨∞ finJoin∞ ns

-- Finite meet of negated generators: for a list of indices, compute ⋀_{i∈list} ¬g_i
finMeetNeg∞ : List ℕ → ⟨ B∞ ⟩
finMeetNeg∞ [] = 𝟙∞
finMeetNeg∞ (n ∷ ns) = (¬∞ g∞ n) ∧∞ finMeetNeg∞ ns

-- The normal form data type for B∞ elements
data B∞-NormalForm : Type₀ where
  joinForm : List ℕ → B∞-NormalForm  -- represents ⋁_{i∈list} g_i
  meetNegForm : List ℕ → B∞-NormalForm  -- represents ⋀_{i∈list} ¬g_i

-- Interpretation of normal forms as B∞ elements
⟦_⟧nf : B∞-NormalForm → ⟨ B∞ ⟩
⟦ joinForm ns ⟧nf = finJoin∞ ns
⟦ meetNegForm ns ⟧nf = finMeetNeg∞ ns

-- The Normal Form Theorem (postulated for now):
-- Every element of B∞ has a normal form representation
-- Note: This is the key missing piece for f-injective
--
-- PROOF APPROACH for normalFormExists:
-- B∞ = freeBA ℕ / Im relB∞ where relB∞ enforces g_m · g_n = 0 for m ≠ n
--
-- In any Boolean algebra with orthogonal atoms (generators), every element
-- can be written as either:
--   - A finite join of atoms: ⋁_{i∈I} g_i
--   - A finite meet of negated atoms: ⋀_{i∈I} ¬g_i
--
-- The proof would require:
-- 1. Show that freeBA ℕ elements are finite Boolean expressions over generators
-- 2. Show that the quotient relations collapse products g_i · g_j → 0 for i ≠ j
-- 3. Show that every Boolean expression simplifies to one of the two forms
--
-- This is a standard result in Boolean algebra (CNF/DNF for atom-disjoint case)
-- but formalizing it requires careful handling of the quotient structure.
--
-- Alternative: prove f-injective directly via spectrum argument:
-- - Stone Duality: f is injective ⟺ Sp(f) is surjective
-- - We have Sp B∞ ≅ ℕ∞ and Sp(B∞×B∞) ≅ ℕ∞ + ℕ∞
-- - The surjectivity of Sp(f) follows from the parity decomposition
--
-- SPECTRUM-BASED APPROACH (alternative to normalFormExists):
-- 1. We have SpB∞-to-ℕ∞ : Sp B∞ → ℕ∞ (line ~3776)
-- 2. We have ℕ∞-to-SpB∞ : ℕ∞ → Sp B∞ (line ~4954)
-- 3. SpB∞-roundtrip shows ℕ∞-to-SpB∞ is a section (line ~4989)
-- 4. If SpB∞-to-ℕ∞ is injective, then Sp B∞ ≅ ℕ∞
-- 5. Similarly, Sp(B∞×B∞) ≅ Sp B∞ + Sp B∞ ≅ ℕ∞ + ℕ∞
-- 6. Under these identifications, Sp(f) maps (left α, right β) → merge α β
--    where merge uses parity: evens from α, odds from β
-- 7. Sp(f) surjectivity follows from: given γ : ℕ∞,
--    take α with seq(α)(n) = seq(γ)(2n) and β with seq(β)(n) = seq(γ)(2n+1)
-- 8. By surj-formal-axiom, Sp(f) surjective ⟹ f injective
--
-- The key missing piece: showing SpB∞-to-ℕ∞ is injective requires that
-- homomorphisms B∞ → Bool are determined by their values on generators.
-- This is essentially equivalent to normalFormExists.
--
-- normalFormExists is now partially resolved:
-- - normalFormExists-trunc (truncated version) is PROVED at line ~7849
-- - normalFormExists-from-surj (untruncated) is proved at line ~7882
--   but requires nf-injective which is still postulated
--
-- For f-injective, we don't need the untruncated version - see f-injective-from-trunc
-- at line ~7905 which uses only the truncated normal form existence.
--
-- ANALYSIS: This postulate is UNUSED in the main proof chain!
-- - The only use is in f-injective-from-normalForm (line ~6144)
-- - But f-injective-from-normalForm is NEVER USED (superseded by f-injective-from-trunc)
-- - Therefore this postulate has been COMMENTED OUT.
--
-- {- COMMENTED OUT - UNUSED CODE:
-- postulate
--   normalFormExists : (x : ⟨ B∞ ⟩) → Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ x
-- -}

-- Key lemma: f respects the parity split on indices
-- For a join form: f(⋁_{i∈I} g_i) = (⋁_{k: 2k∈I} g_k, ⋁_{k: 2k+1∈I} g_k)
-- This uses the fact that f(g_n) = (g_{n/2}, 0) or (0, g_{n/2}) depending on parity

-- Helper to split a list by parity of indices
-- For each n in the list, put half(n) in evens if n is even, or in odds if n is odd
-- Note: 'half' is already defined at line 444
splitByParity : List ℕ → List ℕ × List ℕ
splitByParity [] = [] , []
splitByParity (n ∷ ns) with isEven n | splitByParity ns
... | true  | (evens , odds) = half n ∷ evens , odds    -- n is even
... | false | (evens , odds) = evens , half n ∷ odds    -- n is odd

-- Key observations about f on generators (connecting to parity):
-- - f(g_{2k}) = (g_k, 0)   (even generators go to left factor)
-- - f(g_{2k+1}) = (0, g_k)  (odd generators go to right factor)

-- Since generators in B∞ are orthogonal (g_m · g_n = 0 for m ≠ n),
-- finite joins decompose nicely:
-- f(⋁_i g_i) = (⋁_{evens} g_k, ⋁_{odds} g_k)

-- This leads to the key lemma: f respects the parity split
-- Proof sketch:
-- 1. f is a ring homomorphism, so it preserves +
-- 2. In Boolean rings, join = a + b + a·b, and orthogonality gives a·b = 0
-- 3. So f(a ∨ b) = f(a + b) = f(a) + f(b) when a,b are orthogonal
-- 4. The parity split ensures we're summing orthogonal elements on each side

-- Key lemma: for orthogonal elements a · b = 0, we have a ∨ b = a + b
orthogonal→join-is-sum : (a b : ⟨ B∞ ⟩) → a ·∞ b ≡ 𝟘∞ → a ∨∞ b ≡ a +∞ b
orthogonal→join-is-sum a b a·b=0 =
  a ∨∞ b                    ≡⟨ refl ⟩
  a +∞ b +∞ (a ·∞ b)        ≡⟨ cong (a +∞ b +∞_) a·b=0 ⟩
  a +∞ b +∞ 𝟘∞              ≡⟨ +B∞-IdR (a +∞ b) ⟩
  a +∞ b ∎
  where
  open BooleanRingStr (snd B∞) using () renaming (+IdR to +B∞-IdR)

-- Generators are orthogonal: g_m · g_n = 0 for m ≠ n
gen-orthogonal : (m n : ℕ) → ¬ (m ≡ n) → g∞ m ·∞ g∞ n ≡ 𝟘∞
gen-orthogonal = g∞-distinct-mult-zero

-- Product operations in B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×_ ; _·_ to _·×'_ ; 𝟘 to 𝟘× ; 𝟙 to 𝟙×) public

-- Join in B∞×B∞: componentwise
_∨×_ : ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞ ⟩
(a₁ , a₂) ∨× (b₁ , b₂) = (a₁ ∨∞ b₁ , a₂ ∨∞ b₂)

-- f preserves addition
f-pres+ : (a b : ⟨ B∞ ⟩) → fst f (a +∞ b) ≡ (fst f a) +× (fst f b)
f-pres+ a b = IsCommRingHom.pres+ (snd f) a b

-- f preserves multiplication
f-pres·' : (a b : ⟨ B∞ ⟩) → fst f (a ·∞ b) ≡ (fst f a) ·×' (fst f b)
f-pres·' a b = IsCommRingHom.pres· (snd f) a b

-- Key lemma: f respects joins
-- f(a ∨ b) = f(a) ∨ f(b)  (since f is a ring homomorphism)
-- Note: a ∨ b = a + b + a·b in Boolean rings
f-pres-join : (a b : ⟨ B∞ ⟩) → fst f (a ∨∞ b) ≡ ((fst f a) ∨× (fst f b))
f-pres-join a b = step1 ∙ step2 ∙ step3
  where
  step1 : fst f (a ∨∞ b) ≡ ((fst f (a +∞ b)) +× (fst f (a ·∞ b)))
  step1 = f-pres+ (a +∞ b) (a ·∞ b)

  step2 : ((fst f (a +∞ b)) +× (fst f (a ·∞ b))) ≡ (((fst f a) +× (fst f b)) +× ((fst f a) ·×' (fst f b)))
  step2 = cong₂ _+×_ (f-pres+ a b) (f-pres·' a b)

  step3 : (((fst f a) +× (fst f b)) +× ((fst f a) ·×' (fst f b))) ≡ ((fst f a) ∨× (fst f b))
  step3 = refl

-- Product join unfolds to component joins
∨×-eq : (a b : ⟨ B∞×B∞ ⟩) →
  let (a₁ , a₂) = a ; (b₁ , b₂) = b
  in a ∨× b ≡ (a₁ ∨∞ b₁ , a₂ ∨∞ b₂)
∨×-eq (a₁ , a₂) (b₁ , b₂) = refl

-- finJoin∞ for the product B∞×B∞ (componentwise)
finJoin× : List ℕ → List ℕ → ⟨ B∞×B∞ ⟩
finJoin× evens odds = (finJoin∞ evens , finJoin∞ odds)

-- The main theorem about f on finite joins:
-- f(finJoin∞ ns) = finJoin× (evens) (odds) where (evens, odds) = splitByParity ns
--
-- We prove this by induction on the list ns

-- First, f(0) = (0, 0)
f-on-zero : fst f 𝟘∞ ≡ (𝟘∞ , 𝟘∞)
f-on-zero = IsCommRingHom.pres0 (snd f)

-- Next, we need to show f(g_n ∨ x) = f(g_n) ∨ f(x) and then use the parity of n

-- Helper: 0 ∨ x = x (zero is identity for join)
zero-join-left : (x : ⟨ B∞ ⟩) → 𝟘∞ ∨∞ x ≡ x
zero-join-left x =
  𝟘∞ ∨∞ x                     ≡⟨ refl ⟩
  𝟘∞ +∞ x +∞ (𝟘∞ ·∞ x)        ≡⟨ cong (𝟘∞ +∞ x +∞_) (0∞-absorbs-left x) ⟩
  𝟘∞ +∞ x +∞ 𝟘∞              ≡⟨ BooleanRingStr.+IdR (snd B∞) (𝟘∞ +∞ x) ⟩
  𝟘∞ +∞ x                     ≡⟨ BooleanRingStr.+IdL (snd B∞) x ⟩
  x ∎

-- Helper: x ∨ 0 = x (zero is identity for join, right version)
zero-join-right : (x : ⟨ B∞ ⟩) → x ∨∞ 𝟘∞ ≡ x
zero-join-right x =
  x ∨∞ 𝟘∞                     ≡⟨ refl ⟩
  x +∞ 𝟘∞ +∞ (x ·∞ 𝟘∞)        ≡⟨ cong (x +∞ 𝟘∞ +∞_) (0∞-absorbs-right x) ⟩
  x +∞ 𝟘∞ +∞ 𝟘∞              ≡⟨ BooleanRingStr.+IdR (snd B∞) (x +∞ 𝟘∞) ⟩
  x +∞ 𝟘∞                     ≡⟨ BooleanRingStr.+IdR (snd B∞) x ⟩
  x ∎

-- The key induction: f(finJoin∞ ns) = (finJoin∞ evens, finJoin∞ odds)
-- This uses f-even-gen and f-odd-gen which are now in scope.

-- First, prove that isEven (from Cubical.Data.Nat) equals isEvenB (local definition)
-- isEven uses mutual recursion: isEven zero = true, isEven (suc n) = isOdd n
-- isEvenB uses direct recursion: isEvenB zero = true, isEvenB (suc zero) = false, isEvenB (suc (suc n)) = isEvenB n
isEven≡isEvenB : (n : ℕ) → isEven n ≡ isEvenB n
isEven≡isEvenB zero = refl
isEven≡isEvenB (suc zero) = refl
isEven≡isEvenB (suc (suc n)) = isEven≡isEvenB n

-- Helper: relate isEven to 2· form for even case
-- When isEven n = true, we have n = 2 · (half n)
isEven→even : (n : ℕ) → isEven n ≡ true → 2 ·ℕ (half n) ≡ n
isEven→even n prf = 2·half-even n (sym (isEven≡isEvenB n) ∙ prf)

-- Helper: relate isEven to 2· form for odd case
-- When isEven n = false, we have n = suc (2 · (half n))
isEven→odd : (n : ℕ) → isEven n ≡ false → suc (2 ·ℕ (half n)) ≡ n
isEven→odd n prf = suc-2·half-odd n (sym (isEven≡isEvenB n) ∙ prf)

-- Helper: f on generator when even
f-on-gen-even : (n : ℕ) → isEven n ≡ true → fst f (g∞ n) ≡ (g∞ (half n) , 𝟘∞)
f-on-gen-even n even-prf =
  fst f (g∞ n)                    ≡⟨ cong (λ m → fst f (g∞ m)) (sym (isEven→even n even-prf)) ⟩
  fst f (g∞ (2 ·ℕ (half n)))      ≡⟨ f-even-gen (half n) ⟩
  (g∞ (half n) , 𝟘∞) ∎

-- Helper: f on generator when odd
f-on-gen-odd : (n : ℕ) → isEven n ≡ false → fst f (g∞ n) ≡ (𝟘∞ , g∞ (half n))
f-on-gen-odd n odd-prf =
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
  -- n is even: f(g_n ∨ rest) = f(g_n) ∨ f(rest) = (g_{half n}, 0) ∨ (evens', odds')
  fst f (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ f-pres-join (g∞ n) (finJoin∞ ns) ⟩
  (fst f (g∞ n)) ∨× (fst f (finJoin∞ ns))
    ≡⟨ cong₂ _∨×_ (f-on-gen-even n (builtin→Path-Bool parity-eq)) ih ⟩
  (g∞ (half n) , 𝟘∞) ∨× (finJoin∞ evens , finJoin∞ odds)
    ≡⟨ refl ⟩
  (g∞ (half n) ∨∞ finJoin∞ evens , 𝟘∞ ∨∞ finJoin∞ odds)
    ≡⟨ cong (g∞ (half n) ∨∞ finJoin∞ evens ,_) (zero-join-left (finJoin∞ odds)) ⟩
  (g∞ (half n) ∨∞ finJoin∞ evens , finJoin∞ odds)
    ≡⟨ refl ⟩
  (finJoin∞ (half n ∷ evens) , finJoin∞ odds) ∎
... | false | (evens , odds) | ih =
  -- n is odd: f(g_n ∨ rest) = f(g_n) ∨ f(rest) = (0, g_{half n}) ∨ (evens', odds')
  fst f (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ f-pres-join (g∞ n) (finJoin∞ ns) ⟩
  (fst f (g∞ n)) ∨× (fst f (finJoin∞ ns))
    ≡⟨ cong₂ _∨×_ (f-on-gen-odd n (builtin→Path-Bool parity-eq)) ih ⟩
  (𝟘∞ , g∞ (half n)) ∨× (finJoin∞ evens , finJoin∞ odds)
    ≡⟨ refl ⟩
  (𝟘∞ ∨∞ finJoin∞ evens , g∞ (half n) ∨∞ finJoin∞ odds)
    ≡⟨ cong (_, g∞ (half n) ∨∞ finJoin∞ odds) (zero-join-left (finJoin∞ evens)) ⟩
  (finJoin∞ evens , g∞ (half n) ∨∞ finJoin∞ odds)
    ≡⟨ refl ⟩
  (finJoin∞ evens , finJoin∞ (half n ∷ odds)) ∎

-- =============================================================================
-- Lemmas for proving f-injective via normalFormExists
-- =============================================================================

-- Key fact: generators are non-zero in B∞
-- g∞ n ≠ 0 for all n
-- This follows from the fact that B∞ has non-trivial spectrum (ℕ∞)
-- Specifically, the homomorphism that sends g_n ↦ true and all other g_m ↦ false
-- is a point in Sp(B∞), so g_n cannot be 0.

-- For the joinForm case: if finJoin∞ ns = 0, then ns = []
-- Proof sketch: if ns = n ∷ rest, then g_n ≤ finJoin∞ ns (in the lattice order)
-- Since g_n ≠ 0, we have finJoin∞ ns ≠ 0.
-- The formal proof would require showing g_n ≤ g_n ∨ x for any x.

-- For the meetNegForm case: finMeetNeg∞ ns ≠ 0 always
-- Proof: The zero homomorphism h ∈ Sp(B∞) (sending all generators to false)
-- satisfies h(¬g_i) = ¬(h(g_i)) = ¬false = true for all i.
-- So h(⋀_I ¬g_i) = ⋀_I true = true ≠ false.
-- Hence finMeetNeg∞ ns ≠ 0.

-- f on negation: f(¬x) = ¬(f(x)) componentwise
-- Since f is a ring hom and ¬x = 1 + x in Boolean rings:
-- f(¬x) = f(1 + x) = f(1) + f(x) = (1,1) + f(x) = (1 + fst(f(x)), 1 + snd(f(x)))
--       = (¬(fst(f(x))), ¬(snd(f(x))))

-- f preserves 1
f-pres1 : fst f 𝟙∞ ≡ (𝟙∞ , 𝟙∞)
f-pres1 = IsCommRingHom.pres1 (snd f)

-- f preserves negation: f(¬x) = (¬(fst(f(x))), ¬(snd(f(x))))
f-pres-neg : (x : ⟨ B∞ ⟩) → fst f (¬∞ x) ≡ (¬∞ (fst (fst f x)) , ¬∞ (snd (fst f x)))
f-pres-neg x =
  fst f (¬∞ x)
    ≡⟨ refl ⟩  -- ¬∞ x = 𝟙∞ +∞ x
  fst f (𝟙∞ +∞ x)
    ≡⟨ f-pres+ 𝟙∞ x ⟩
  (fst f 𝟙∞) +× (fst f x)
    ≡⟨ cong (_+× (fst f x)) f-pres1 ⟩
  (𝟙∞ , 𝟙∞) +× (fst f x)
    ≡⟨ refl ⟩  -- componentwise addition
  (𝟙∞ +∞ fst (fst f x) , 𝟙∞ +∞ snd (fst f x))
    ≡⟨ refl ⟩  -- ¬∞ = 𝟙∞ +∞ _
  (¬∞ (fst (fst f x)) , ¬∞ (snd (fst f x))) ∎

-- Corollary: f on negated generator
-- f(¬g_n) = (¬(fst(f(g_n))), ¬(snd(f(g_n))))
-- For even n = 2k: f(g_n) = (g_k, 0), so f(¬g_n) = (¬g_k, ¬0) = (¬g_k, 1)
-- For odd n = 2k+1: f(g_n) = (0, g_k), so f(¬g_n) = (¬0, ¬g_k) = (1, ¬g_k)

-- =============================================================================
-- Dirac delta: the ℕ∞ element that hits true exactly at position n
-- =============================================================================

-- The Dirac sequence at n: true at n, false elsewhere
δ-seq : ℕ → ℕ → Bool
δ-seq n m with discreteℕ n m
... | yes _ = true
... | no _ = false

-- δ-seq n hits at most once (it hits exactly at n)
δ-seq-hamo : (n : ℕ) → hitsAtMostOnce (δ-seq n)
δ-seq-hamo n i j δi=t δj=t with discreteℕ n i | discreteℕ n j
... | yes n=i | yes n=j = sym n=i ∙ n=j
... | yes _ | no n≠j = ex-falso (true≢false (sym δj=t))
... | no n≠i | _ = ex-falso (true≢false (sym δi=t))

-- The Dirac delta as an element of ℕ∞
δ∞ : ℕ → ℕ∞
δ∞ n = δ-seq n , δ-seq-hamo n

-- Key property: δ∞ n hits true at position n
δ∞-hits-n : (n : ℕ) → fst (δ∞ n) n ≡ true
δ∞-hits-n n with discreteℕ n n
... | yes _ = refl
... | no n≠n = ex-falso (n≠n refl)

-- Key property: δ∞ n is false at other positions
δ∞-misses-m : (n m : ℕ) → ¬ (n ≡ m) → fst (δ∞ n) m ≡ false
δ∞-misses-m n m n≠m with discreteℕ n m
... | yes n=m = ex-falso (n≠m n=m)
... | no _ = refl

-- =============================================================================
-- Generators are non-zero (proved after ℕ∞-to-SpB∞ is defined at line ~5020)
-- =============================================================================

-- NOTE: g∞-nonzero : (n : ℕ) → ¬ (g∞ n ≡ 𝟘∞)
-- is defined later, after ℕ∞-to-SpB∞, using the witness h_n = ℕ∞-to-SpB∞ (δ∞ n)

-- The injectivity of f then follows:
-- If fst f x = (0,0), then using normal form:
-- - If x = ⋁_I g_i, then both parity-splits are empty, so I = ∅, so x = 0
-- - If x = ⋀_I ¬g_i, then... (requires separate analysis)
--
-- PROOF SKETCH for f-injective (via normalFormExists):
-- 1. Let x ∈ B∞ with f(x) = (0, 0)
-- 2. By normalFormExists, x = ⟦ nf ⟧nf for some normal form nf
-- 3. Case nf = joinForm ns:
--    - f(⋁_I g_i) = (⋁_{evens} g_k, ⋁_{odds} g_k) by f-on-finJoin
--    - If this equals (0,0), both components are 0
--    - For finJoin∞ to be 0, the list must be empty (generators are non-zero)
--    - So ns = [], and x = finJoin∞ [] = 0
-- 4. Case nf = meetNegForm ns:
--    - f(⋀_I ¬g_i) requires showing f preserves negation properly
--    - ¬g_i = 1 + g_i, so f(¬g_i) = f(1) + f(g_i) = (1,1) + f(g_i)
--    - This analysis is more complex but follows from homomorphism properties
--
-- ALTERNATIVE PROOF via Stone Duality (tex line 295):
-- - f is injective ⟺ Sp(f) is surjective (Stone Duality axiom)
-- - Sp-f-surjective would directly give f-injective
-- - But currently Sp-f-surjective is postulated with dependency on f-injective

-- f-injective is now PROVED (not postulated) using truncated normal forms.
-- See f-injective-from-trunc at line ~7148 for the proof.
--
-- The proof uses:
-- 1. interpretB∞-surjective: interpretB∞ is surjective onto B∞
-- 2. normalFormExists-trunc: truncated normal form existence
-- 3. f-kernel-from-trunc: if f(x) = 0 then x = 0 (using truncated forms)
-- 4. f-injective-from-trunc: if f(x) = f(y) then x = y
--
-- ELIMINATED (CHANGES0508): The postulate f-injective is now commented out.
-- It was never used - Part05 uses f-injective-05a from Part05a instead,
-- which is proved using truncated normal forms in Part06.
-- The postulate is kept here (commented) for documentation purposes.
-- postulate
--   f-injective : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y

-- =============================================================================
-- Spectrum of Products: Sp(A × B) ≅ Sp(A) + Sp(B)
-- =============================================================================

-- For Boolean rings, the spectrum of a product is the coproduct of spectra.
-- Key insight: a homomorphism h : A × B → 2 must satisfy:
--   h(1,0) ∧ h(0,1) = h((1,0) · (0,1)) = h(0,0) = 0
-- So exactly one of h(1,0), h(0,1) is 1 (for non-trivial h).

-- B∞×B∞ has a presentation as B∞ × B∞ with:
-- (1_A, 0_B) and (0_A, 1_B) as orthogonal idempotents

-- The unit elements in B∞×B∞
