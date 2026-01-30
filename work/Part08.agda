{-# OPTIONS --cubical --guardedness #-}

module work.Part08 where

-- =============================================================================
-- Part 08: B∞×B∞-Presentation, restrict-to-left/right, inject-left/right,
--          Sp-prod-to-sum/Sp-sum-to-prod, and LLPO infrastructure
-- =============================================================================

-- Import Part07 for previous definitions
open import work.Part07 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open Iso
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isSetΣSndProp; isSetΠ)
open import Cubical.Functions.Embedding using (isEmbedding→Inj)
open import Cubical.Data.Sum.Properties using (isEmbedding-inl; isEmbedding-inr)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; inj-m+; +-zero; injSuc; snotz; znots)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum.Properties using (module ⊎Path)
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

-- Stone duality types (defined locally, matching work.agda lines 1384-1455)
isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → fst g x ≡ fst g y → x ≡ y

-- Sp-hom : precomposition with g
Sp-hom : (B C : Booleω) → BoolHom (fst B) (fst C) → Sp C → Sp B
Sp-hom B C g h = h ∘cr g

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C g = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] Sp-hom B C g h' ≡ h ∥₁

-- The axiom: injective ⟺ Sp-surjective (from work.agda line 1438)
SurjectionsAreFormalSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
SurjectionsAreFormalSurjectionsAxiom = (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g ↔ isSurjectiveSpHom B C g

-- Postulate this axiom (from tex line 294-297)
postulate
  surj-formal-axiom : SurjectionsAreFormalSurjectionsAxiom

-- Convenience: if g is injective, then Sp(g) is surjective
injective→Sp-surjective : (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g → isSurjectiveSpHom B C g
injective→Sp-surjective B C g = fst (surj-formal-axiom B C g)

-- =============================================================================
-- B∞×B∞-Presentation Module (lines 5500-6120 of work.agda)
-- =============================================================================

module B∞×B∞-Presentation where
  open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; _+_ to _+×_ ; 𝟘 to 𝟘× ; 𝟙 to 𝟙×)
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

  -- Helper: ¬(a < b) implies b ≤ a (needed for trichotomy proofs)
  ≮→≥ : {a b : ℕ} → ¬ (a < b) → b ≤ a
  ≮→≥ {zero} {zero} _ = ≤-refl
  ≮→≥ {zero} {suc b} ¬0<sb = ex-falso (¬0<sb (suc-≤-suc zero-≤))
  ≮→≥ {suc a} {zero} _ = zero-≤
  ≮→≥ {suc a} {suc b} ¬sa<sb = suc-≤-suc (≮→≥ (λ a<b → ¬sa<sb (suc-≤-suc a<b)))

  -- Different factors: (0, g∞ m) · (g∞ n, 0) = (0, 0)
  -- genProd⊎-orthog cases already defined in Part07 through f-respects-relations

  -- The ℕ ⊎ ℕ ≃ ℕ bijection
  -- The bijection ℕ ⊎ ℕ ≅ ℕ from the library
  encode× : ℕ ⊎ ℕ → ℕ
  encode× = fun ℕ⊎ℕ≅ℕ

  decode× : ℕ → ℕ ⊎ ℕ
  decode× = inv ℕ⊎ℕ≅ℕ

  encode×∘decode× : (n : ℕ) → encode× (decode× n) ≡ n
  encode×∘decode× = sec ℕ⊎ℕ≅ℕ

  decode×∘encode× : (x : ℕ ⊎ ℕ) → decode× (encode× x) ≡ x
  decode×∘encode× = ret ℕ⊎ℕ≅ℕ

  -- genProd maps to generator in B∞×B∞ based on decode×
  genProd⊎ : ℕ ⊎ ℕ → ⟨ B∞×B∞ ⟩
  genProd⊎ (⊎.inl n) = (g∞ n , 𝟘∞)
  genProd⊎ (⊎.inr n) = (𝟘∞ , g∞ n)

  genProd : ℕ → ⟨ B∞×B∞ ⟩
  genProd n = genProd⊎ (decode× n)

  -- genProd⊎ orthogonality
  genProd⊎-orthog : (x y : ℕ ⊎ ℕ) → ¬ (x ≡ y) → genProd⊎ x ·× genProd⊎ y ≡ (𝟘∞ , 𝟘∞)
  genProd⊎-orthog (⊎.inl m) (⊎.inl n) m≠n =
    let m≠n' : ¬ (m ≡ n)
        m≠n' meq = m≠n (cong ⊎.inl meq)
    in cong₂ _,_ (g∞-distinct-mult-zero m n m≠n') (0∞-absorbs-left 𝟘∞)
  genProd⊎-orthog (⊎.inl m) (⊎.inr n) _ = inl-inr-mult-zero (g∞ m) (g∞ n)
  genProd⊎-orthog (⊎.inr m) (⊎.inl n) _ = inr-inl-mult-zero (g∞ m) (g∞ n)
  genProd⊎-orthog (⊎.inr m) (⊎.inr n) m≠n =
    let m≠n' : ¬ (m ≡ n)
        m≠n' meq = m≠n (cong ⊎.inr meq)
    in cong₂ _,_ (0∞-absorbs-left 𝟘∞) (g∞-distinct-mult-zero m n m≠n')

  -- Transfer to ℕ-indexed genProd
  genProd-orthog : (m n : ℕ) → ¬ (m ≡ n) → genProd m ·× genProd n ≡ (𝟘∞ , 𝟘∞)
  genProd-orthog m n m≠n = genProd⊎-orthog (decode× m) (decode× n) decode-neq
    where
    decode-neq : ¬ (decode× m ≡ decode× n)
    decode-neq deq = m≠n (
      m                    ≡⟨ sym (encode×∘decode× m) ⟩
      encode× (decode× m)  ≡⟨ cong encode× deq ⟩
      encode× (decode× n)  ≡⟨ encode×∘decode× n ⟩
      n                    ∎)

  -- Relations: all distinct generators are orthogonal
  relB∞×B∞-from-pair : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  relB∞×B∞-from-pair (m , d) = gen m · gen (m +ℕ suc d)

  relB∞×B∞ : ℕ → ⟨ freeBA ℕ ⟩
  relB∞×B∞ k = relB∞×B∞-from-pair (cantorUnpair k)

  -- The quotient Boolean ring
  B∞×B∞-quotient : BooleanRing ℓ-zero
  B∞×B∞-quotient = freeBA ℕ QB./Im relB∞×B∞

  -- The quotient map
  π× : BoolHom (freeBA ℕ) B∞×B∞-quotient
  π× = QB.quotientImageHom

  -- Generators in the quotient
  g× : ℕ → ⟨ B∞×B∞-quotient ⟩
  g× n = fst π× (gen n)

  -- Step 1: Build a homomorphism from freeBA ℕ → B∞×B∞
  genProd-free : BoolHom (freeBA ℕ) B∞×B∞
  genProd-free = inducedBAHom ℕ B∞×B∞ genProd

  genProd-free-on-gen : fst genProd-free ∘ generator ≡ genProd
  genProd-free-on-gen = evalBAInduce ℕ B∞×B∞ genProd

  -- Helper: m ≠ m + suc d for any m, d
  m≠m+suc-d : (m d : ℕ) → ¬ (m ≡ m +ℕ suc d)
  m≠m+suc-d zero d meq = snotz (sym meq)
  m≠m+suc-d (suc m) d meq = m≠m+suc-d m d (injSuc meq)

  -- When i < j, we have i + suc (j ∸ suc i) ≡ j
  i+suc[j∸suc-i]≡j : (i j : ℕ) → i < j → i +ℕ suc (j ∸ suc i) ≡ j
  i+suc[j∸suc-i]≡j i zero (k , p) = ex-falso (¬-<-zero (k , p))
  i+suc[j∸suc-i]≡j i (suc j) (k , p) =
    let eq : k +ℕ i ≡ j
        eq = injSuc (sym (+-suc k i) ∙ p)
        i≤j : i ≤ j
        i≤j = k , eq
    in i +ℕ suc (j ∸ i)
         ≡⟨ +-suc i (j ∸ i) ⟩
       suc (i +ℕ (j ∸ i))
         ≡⟨ cong suc (+-comm i (j ∸ i)) ⟩
       suc ((j ∸ i) +ℕ i)
         ≡⟨ cong suc (≤-∸-+-cancel i≤j) ⟩
       suc j ∎

  genProd-respects-rel-pair : (p : ℕ × ℕ) → fst genProd-free (relB∞×B∞-from-pair p) ≡ (𝟘∞ , 𝟘∞)
  genProd-respects-rel-pair (m , d) =
    let n = m +ℕ suc d
        m≠n = m≠m+suc-d m d
    in fst genProd-free (gen m · gen n)
         ≡⟨ IsCommRingHom.pres· (snd genProd-free) (gen m) (gen n) ⟩
       fst genProd-free (gen m) ·× fst genProd-free (gen n)
         ≡⟨ cong₂ _·×_ (funExt⁻ genProd-free-on-gen m) (funExt⁻ genProd-free-on-gen n) ⟩
       genProd m ·× genProd n
         ≡⟨ genProd-orthog m n m≠n ⟩
       (𝟘∞ , 𝟘∞) ∎

  genProd-respects-rel : (k : ℕ) → fst genProd-free (relB∞×B∞ k) ≡ (𝟘∞ , 𝟘∞)
  genProd-respects-rel k = genProd-respects-rel-pair (cantorUnpair k)

  -- Build φ : B∞×B∞-quotient → B∞×B∞
  φ : BoolHom B∞×B∞-quotient B∞×B∞
  φ = QB.inducedHom B∞×B∞ genProd-free genProd-respects-rel

  -- φ sends g× n to genProd n
  φ-on-g× : (n : ℕ) → fst φ (g× n) ≡ genProd n
  φ-on-g× n = funExt⁻ (cong fst (QB.evalInduce B∞×B∞)) (gen n) ∙ funExt⁻ genProd-free-on-gen n

  -- Left generator map: n ↦ g× (encode× (inl n))
  g×-left-gen : ℕ → ⟨ B∞×B∞-quotient ⟩
  g×-left-gen n = g× (encode× (⊎.inl n))

  -- Right generator map: n ↦ g× (encode× (inr n))
  g×-right-gen : ℕ → ⟨ B∞×B∞-quotient ⟩
  g×-right-gen n = g× (encode× (⊎.inr n))

  -- ψ-left-free : freeBA ℕ → B∞×B∞-quotient
  ψ-left-free : BoolHom (freeBA ℕ) B∞×B∞-quotient
  ψ-left-free = inducedBAHom ℕ B∞×B∞-quotient g×-left-gen

  ψ-left-free-on-gen : fst ψ-left-free ∘ generator ≡ g×-left-gen
  ψ-left-free-on-gen = evalBAInduce ℕ B∞×B∞-quotient g×-left-gen

  -- Key lemma: encode× (inl m) ≠ encode× (inl n) when m ≠ n
  encode×-inl-injective : (m n : ℕ) → encode× (⊎.inl m) ≡ encode× (⊎.inl n) → m ≡ n
  encode×-inl-injective m n = λ eq → isEmbedding→Inj isEmbedding-inl m n (
    ⊎.inl m            ≡⟨ sym (decode×∘encode× (⊎.inl m)) ⟩
    decode× (encode× (⊎.inl m))  ≡⟨ cong decode× eq ⟩
    decode× (encode× (⊎.inl n))  ≡⟨ decode×∘encode× (⊎.inl n) ⟩
    ⊎.inl n            ∎)

  -- g×-left generators are orthogonal in the quotient
  g×-left-orthog : (m n : ℕ) → ¬ (m ≡ n) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-left-gen m) (g×-left-gen n) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-left-orthog m n m≠n =
    let i = encode× (⊎.inl m)
        j = encode× (⊎.inl n)
        i≠j : ¬ (i ≡ j)
        i≠j = λ eq → m≠n (encode×-inl-injective m n eq)
    in g×-orthog i j i≠j
    where
    g×-orthog-base : (i j : ℕ) → i < j →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-base i j i<j =
      let k = cantorPair i (j ∸ suc i)
          rel-eq : relB∞×B∞ k ≡ gen i · gen j
          rel-eq = cong relB∞×B∞-from-pair (cantorUnpair-pair i (j ∸ suc i))
                 ∙ cong (λ x → gen i · gen x) (i+suc[j∸suc-i]≡j i j i<j)
      in sym (IsCommRingHom.pres· (snd π×) (gen i) (gen j))
         ∙ cong (fst π×) (sym rel-eq)
         ∙ QB.zeroOnImage k

    g×-orthog : (i j : ℕ) → ¬ (i ≡ j) →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog i j i≠j with Cubical.Data.Nat.Order.<Dec i j
    ... | yes i<j = g×-orthog-base i j i<j
    ... | no ¬i<j with Cubical.Data.Nat.Order.<Dec j i
    ...   | yes j<i =
            BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g× i) (g× j)
            ∙ g×-orthog-base j i j<i
    ...   | no ¬j<i =
            ex-falso (i≠j (≤-antisym (≮→≥ ¬j<i) (≮→≥ ¬i<j)))

  -- ψ-left-free respects relB∞
  ψ-left-respects-relB∞ : (k : ℕ) → fst ψ-left-free (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  ψ-left-respects-relB∞ k =
    let (m , d) = cantorUnpair k
        n = m +ℕ suc d
        m≠n = m≠m+suc-d m d
    in fst ψ-left-free (gen m · gen n)
         ≡⟨ IsCommRingHom.pres· (snd ψ-left-free) (gen m) (gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (fst ψ-left-free (gen m)) (fst ψ-left-free (gen n))
         ≡⟨ cong₂ (BooleanRingStr._·_ (snd B∞×B∞-quotient))
                  (funExt⁻ ψ-left-free-on-gen m) (funExt⁻ ψ-left-free-on-gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-left-gen m) (g×-left-gen n)
         ≡⟨ g×-left-orthog m n m≠n ⟩
       BooleanRingStr.𝟘 (snd B∞×B∞-quotient) ∎

  -- ψ-left : B∞ → B∞×B∞-quotient
  ψ-left : BoolHom B∞ B∞×B∞-quotient
  ψ-left = QB.inducedHom B∞×B∞-quotient ψ-left-free ψ-left-respects-relB∞

  -- Similarly for right factor
  ψ-right-free : BoolHom (freeBA ℕ) B∞×B∞-quotient
  ψ-right-free = inducedBAHom ℕ B∞×B∞-quotient g×-right-gen

  encode×-inr-injective : (m n : ℕ) → encode× (⊎.inr m) ≡ encode× (⊎.inr n) → m ≡ n
  encode×-inr-injective m n = λ eq → isEmbedding→Inj isEmbedding-inr m n (
    ⊎.inr m            ≡⟨ sym (decode×∘encode× (⊎.inr m)) ⟩
    decode× (encode× (⊎.inr m))  ≡⟨ cong decode× eq ⟩
    decode× (encode× (⊎.inr n))  ≡⟨ decode×∘encode× (⊎.inr n) ⟩
    ⊎.inr n            ∎)

  ψ-right-free-on-gen : fst ψ-right-free ∘ generator ≡ g×-right-gen
  ψ-right-free-on-gen = evalBAInduce ℕ B∞×B∞-quotient g×-right-gen

  g×-right-orthog : (m n : ℕ) → ¬ (m ≡ n) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-right-gen m) (g×-right-gen n) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-right-orthog m n m≠n =
    let i = encode× (⊎.inr m)
        j = encode× (⊎.inr n)
        i≠j : ¬ (i ≡ j)
        i≠j = λ eq → m≠n (encode×-inr-injective m n eq)
    in g×-orthog-helper i j i≠j
    where
    g×-orthog-helper-base : (i j : ℕ) → i < j →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-helper-base i j i<j =
      let k = cantorPair i (j ∸ suc i)
          rel-eq : relB∞×B∞ k ≡ gen i · gen j
          rel-eq = cong relB∞×B∞-from-pair (cantorUnpair-pair i (j ∸ suc i))
                 ∙ cong (λ x → gen i · gen x) (i+suc[j∸suc-i]≡j i j i<j)
      in sym (IsCommRingHom.pres· (snd π×) (gen i) (gen j))
         ∙ cong (fst π×) (sym rel-eq)
         ∙ QB.zeroOnImage k

    g×-orthog-helper : (i j : ℕ) → ¬ (i ≡ j) →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-helper i j i≠j with Cubical.Data.Nat.Order.<Dec i j
    ... | yes i<j = g×-orthog-helper-base i j i<j
    ... | no ¬i<j with Cubical.Data.Nat.Order.<Dec j i
    ...   | yes j<i =
            BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g× i) (g× j)
            ∙ g×-orthog-helper-base j i j<i
    ...   | no ¬j<i =
            ex-falso (i≠j (≤-antisym (≮→≥ ¬j<i) (≮→≥ ¬i<j)))

  ψ-right-respects-relB∞ : (k : ℕ) → fst ψ-right-free (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  ψ-right-respects-relB∞ k =
    let (m , d) = cantorUnpair k
        n = m +ℕ suc d
        m≠n = m≠m+suc-d m d
    in fst ψ-right-free (gen m · gen n)
         ≡⟨ IsCommRingHom.pres· (snd ψ-right-free) (gen m) (gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (fst ψ-right-free (gen m)) (fst ψ-right-free (gen n))
         ≡⟨ cong₂ (BooleanRingStr._·_ (snd B∞×B∞-quotient))
                  (funExt⁻ ψ-right-free-on-gen m) (funExt⁻ ψ-right-free-on-gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-right-gen m) (g×-right-gen n)
         ≡⟨ g×-right-orthog m n m≠n ⟩
       BooleanRingStr.𝟘 (snd B∞×B∞-quotient) ∎

  ψ-right : BoolHom B∞ B∞×B∞-quotient
  ψ-right = QB.inducedHom B∞×B∞-quotient ψ-right-free ψ-right-respects-relB∞

  -- Cross-orthogonality: inl m and inr n encode to different naturals
  encode×-inl-inr-distinct : (m n : ℕ) → ¬ (encode× (⊎.inl m) ≡ encode× (⊎.inr n))
  encode×-inl-inr-distinct m n = λ eq →
    lower (⊎Path.encode (⊎.inl m) (⊎.inr n)
           (sym (decode×∘encode× (⊎.inl m))
            ∙ cong decode× eq
            ∙ decode×∘encode× (⊎.inr n)))

  -- Cross-orthogonality: g×-left-gen m · g×-right-gen n = 0
  g×-cross-orthog : (m n : ℕ) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-left-gen m) (g×-right-gen n) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-cross-orthog m n =
    let i = encode× (⊎.inl m)
        j = encode× (⊎.inr n)
        i≠j : ¬ (i ≡ j)
        i≠j = encode×-inl-inr-distinct m n
    in g×-orthog i j i≠j
    where
    g×-orthog-base : (i j : ℕ) → i < j →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-base i j i<j =
      let k = cantorPair i (j ∸ suc i)
          rel-eq : relB∞×B∞ k ≡ gen i · gen j
          rel-eq = cong relB∞×B∞-from-pair (cantorUnpair-pair i (j ∸ suc i))
                 ∙ cong (λ x → gen i · gen x) (i+suc[j∸suc-i]≡j i j i<j)
      in sym (IsCommRingHom.pres· (snd π×) (gen i) (gen j))
         ∙ cong (fst π×) (sym rel-eq)
         ∙ QB.zeroOnImage k

    g×-orthog : (i j : ℕ) → ¬ (i ≡ j) →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog i j i≠j with Cubical.Data.Nat.Order.<Dec i j
    ... | yes i<j = g×-orthog-base i j i<j
    ... | no ¬i<j with Cubical.Data.Nat.Order.<Dec j i
    ...   | yes j<i =
            BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g× i) (g× j)
            ∙ g×-orthog-base j i j<i
    ...   | no ¬j<i =
            ex-falso (i≠j (≤-antisym (≮→≥ ¬j<i) (≮→≥ ¬i<j)))

  -- Symmetric: g×-right-gen n · g×-left-gen m = 0
  g×-cross-orthog-sym : (m n : ℕ) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-right-gen n) (g×-left-gen m) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-cross-orthog-sym m n =
    BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g×-right-gen n) (g×-left-gen m)
    ∙ g×-cross-orthog m n

  -- φ composition properties
  φ-hits-left-gen : (m : ℕ) → fst φ (g×-left-gen m) ≡ (g∞ m , 𝟘∞)
  φ-hits-left-gen m =
    fst φ (g× (encode× (⊎.inl m)))
      ≡⟨ φ-on-g× (encode× (⊎.inl m)) ⟩
    genProd (encode× (⊎.inl m))
      ≡⟨ cong genProd⊎ (decode×∘encode× (⊎.inl m)) ⟩
    genProd⊎ (⊎.inl m)
      ≡⟨ refl ⟩
    (g∞ m , 𝟘∞) ∎

  φ-hits-right-gen : (m : ℕ) → fst φ (g×-right-gen m) ≡ (𝟘∞ , g∞ m)
  φ-hits-right-gen m =
    fst φ (g× (encode× (⊎.inr m)))
      ≡⟨ φ-on-g× (encode× (⊎.inr m)) ⟩
    genProd (encode× (⊎.inr m))
      ≡⟨ cong genProd⊎ (decode×∘encode× (⊎.inr m)) ⟩
    genProd⊎ (⊎.inr m)
      ≡⟨ refl ⟩
    (𝟘∞ , g∞ m) ∎

  ψ-left-on-gen : (m : ℕ) → fst ψ-left (g∞ m) ≡ g×-left-gen m
  ψ-left-on-gen m =
    fst ψ-left (g∞ m)
      ≡⟨ funExt⁻ (cong fst (QB.evalInduce B∞×B∞-quotient)) (gen m) ⟩
    fst ψ-left-free (gen m)
      ≡⟨ funExt⁻ ψ-left-free-on-gen m ⟩
    g×-left-gen m ∎

  ψ-right-on-gen : (m : ℕ) → fst ψ-right (g∞ m) ≡ g×-right-gen m
  ψ-right-on-gen m =
    fst ψ-right (g∞ m)
      ≡⟨ funExt⁻ (cong fst (QB.evalInduce B∞×B∞-quotient)) (gen m) ⟩
    fst ψ-right-free (gen m)
      ≡⟨ funExt⁻ ψ-right-free-on-gen m ⟩
    g×-right-gen m ∎

  -- Composition φ ∘ ψ-left and φ ∘ ψ-right on generators
  φ∘ψ-left-on-gen : (m : ℕ) → fst φ (fst ψ-left (g∞ m)) ≡ (g∞ m , 𝟘∞)
  φ∘ψ-left-on-gen m = cong (fst φ) (ψ-left-on-gen m) ∙ φ-hits-left-gen m

  φ∘ψ-right-on-gen : (m : ℕ) → fst φ (fst ψ-right (g∞ m)) ≡ (𝟘∞ , g∞ m)
  φ∘ψ-right-on-gen m = cong (fst φ) (ψ-right-on-gen m) ∙ φ-hits-right-gen m

  -- The full proof of B∞×B∞≃quotient (postulated)
  postulate
    B∞×B∞≃quotient : BooleanRingEquiv B∞×B∞ B∞×B∞-quotient

open B∞×B∞-Presentation

B∞×B∞-has-Boole-ω' : has-Boole-ω' B∞×B∞
B∞×B∞-has-Boole-ω' = relB∞×B∞ , B∞×B∞≃quotient

B∞×B∞-Booleω : Booleω
B∞×B∞-Booleω = B∞×B∞ , ∣ B∞×B∞-has-Boole-ω' ∣₁

-- =============================================================================
-- restrict-to-left/right helpers (lines 6128-6231 of work.agda)
-- =============================================================================

-- Helper: restrict a homomorphism to the left factor
restrict-to-left : (h' : Sp B∞×B∞-Booleω) → h' $cr B∞×B∞-Units.unit-left ≡ true → Sp B∞-Booleω
restrict-to-left h' h'-unit-left-true = h-on-left , h-on-left-is-hom
  where
  open IsCommRingHom (snd h') renaming (pres0 to h'-pres0 ; pres1 to h'-pres1 ; pres+ to h'-pres+ ; pres· to h'-pres·)
  open CommRingStr (snd (BooleanRing→CommRing B∞)) renaming (_+_ to _+B∞_ ; _·_ to _·B∞_ ; +IdL to +B∞-IdL)
  open CommRingStr (snd (BooleanRing→CommRing B∞×B∞)) renaming (_+_ to _+B∞×B∞_ ; _·_ to _·B∞×B∞_)
  open import Cubical.Algebra.CommRing using (makeIsCommRingHom)

  h-on-left : ⟨ B∞ ⟩ → Bool
  h-on-left x = h' $cr (x , 𝟘∞)

  h-on-left-pres0 : h-on-left 𝟘∞ ≡ false
  h-on-left-pres0 = h'-pres0

  h-on-left-pres1 : h-on-left 𝟙∞ ≡ true
  h-on-left-pres1 = h'-unit-left-true

  h-on-left-pres+ : (x y : ⟨ B∞ ⟩) → h-on-left (x +B∞ y) ≡ (h-on-left x) ⊕ (h-on-left y)
  h-on-left-pres+ x y =
    h' $cr (x +B∞ y , 𝟘∞)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ refl (sym (+B∞-IdL 𝟘∞))) ⟩
    h' $cr (_+B∞×B∞_ (x , 𝟘∞) (y , 𝟘∞))
      ≡⟨ h'-pres+ (x , 𝟘∞) (y , 𝟘∞) ⟩
    (h' $cr (x , 𝟘∞)) ⊕ (h' $cr (y , 𝟘∞)) ∎

  h-on-left-pres· : (x y : ⟨ B∞ ⟩) → h-on-left (x ·B∞ y) ≡ (h-on-left x) and (h-on-left y)
  h-on-left-pres· x y =
    h' $cr (x ·B∞ y , 𝟘∞)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ refl (sym (0∞-absorbs-left 𝟘∞))) ⟩
    h' $cr (_·B∞×B∞_ (x , 𝟘∞) (y , 𝟘∞))
      ≡⟨ h'-pres· (x , 𝟘∞) (y , 𝟘∞) ⟩
    (h' $cr (x , 𝟘∞)) and (h' $cr (y , 𝟘∞)) ∎

  h-on-left-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞)) h-on-left (snd (BooleanRing→CommRing BoolBR))
  h-on-left-is-hom = makeIsCommRingHom h-on-left-pres1 h-on-left-pres+ h-on-left-pres·

-- Helper: restrict a homomorphism to the right factor
restrict-to-right : (h' : Sp B∞×B∞-Booleω) → h' $cr B∞×B∞-Units.unit-left ≡ false → Sp B∞-Booleω
restrict-to-right h' h'-unit-left-false = h-on-right , h-on-right-is-hom
  where
  open IsCommRingHom (snd h') renaming (pres0 to h'-pres0 ; pres1 to h'-pres1 ; pres+ to h'-pres+ ; pres· to h'-pres·)
  open CommRingStr (snd (BooleanRing→CommRing B∞)) renaming (_+_ to _+B∞_ ; _·_ to _·B∞_ ; +IdL to +B∞-IdL ; +IdR to +B∞-IdR)
  open CommRingStr (snd (BooleanRing→CommRing B∞×B∞)) renaming (_+_ to _+B∞×B∞_ ; _·_ to _·B∞×B∞_)
  open import Cubical.Algebra.CommRing using (makeIsCommRingHom)

  h-on-right : ⟨ B∞ ⟩ → Bool
  h-on-right x = h' $cr (𝟘∞ , x)

  h-on-right-pres0 : h-on-right 𝟘∞ ≡ false
  h-on-right-pres0 = h'-pres0

  h-on-right-pres1 : h-on-right 𝟙∞ ≡ true
  h-on-right-pres1 =
    let
      h'-on-1 : h' $cr (𝟙∞ , 𝟙∞) ≡ true
      h'-on-1 = h'-pres1
      unit-sum' : (𝟙∞ , 𝟙∞) ≡ _+B∞×B∞_ (𝟙∞ , 𝟘∞) (𝟘∞ , 𝟙∞)
      unit-sum' = cong₂ _,_ (sym (+B∞-IdR 𝟙∞)) (sym (+B∞-IdL 𝟙∞))
      h'-sum : h' $cr (𝟙∞ , 𝟙∞) ≡ (h' $cr B∞×B∞-Units.unit-left) ⊕ (h' $cr B∞×B∞-Units.unit-right)
      h'-sum = cong (h' $cr_) unit-sum' ∙ h'-pres+ B∞×B∞-Units.unit-left B∞×B∞-Units.unit-right
      xor-eq : false ⊕ (h' $cr B∞×B∞-Units.unit-right) ≡ true
      xor-eq = cong (λ b → b ⊕ (h' $cr B∞×B∞-Units.unit-right)) (sym h'-unit-left-false) ∙ sym h'-sum ∙ h'-on-1
    in xor-eq

  h-on-right-pres+ : (x y : ⟨ B∞ ⟩) → h-on-right (x +B∞ y) ≡ (h-on-right x) ⊕ (h-on-right y)
  h-on-right-pres+ x y =
    h' $cr (𝟘∞ , x +B∞ y)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ (sym (+B∞-IdL 𝟘∞)) refl) ⟩
    h' $cr (_+B∞×B∞_ (𝟘∞ , x) (𝟘∞ , y))
      ≡⟨ h'-pres+ (𝟘∞ , x) (𝟘∞ , y) ⟩
    (h' $cr (𝟘∞ , x)) ⊕ (h' $cr (𝟘∞ , y)) ∎

  h-on-right-pres· : (x y : ⟨ B∞ ⟩) → h-on-right (x ·B∞ y) ≡ (h-on-right x) and (h-on-right y)
  h-on-right-pres· x y =
    h' $cr (𝟘∞ , x ·B∞ y)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ (sym (0∞-absorbs-left 𝟘∞)) refl) ⟩
    h' $cr (_·B∞×B∞_ (𝟘∞ , x) (𝟘∞ , y))
      ≡⟨ h'-pres· (𝟘∞ , x) (𝟘∞ , y) ⟩
    (h' $cr (𝟘∞ , x)) and (h' $cr (𝟘∞ , y)) ∎

  h-on-right-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞)) h-on-right (snd (BooleanRing→CommRing BoolBR))
  h-on-right-is-hom = makeIsCommRingHom h-on-right-pres1 h-on-right-pres+ h-on-right-pres·

-- =============================================================================
-- Sp-prod-to-sum and inject-left/right (lines 6232-6340 of work.agda)
-- =============================================================================

Sp-prod-to-sum : Sp B∞×B∞-Booleω → (Sp B∞-Booleω) ⊎.⊎ (Sp B∞-Booleω)
Sp-prod-to-sum h with h $cr B∞×B∞-Units.unit-left in p
... | true = ⊎.inl (restrict-to-left h (builtin→Path-Bool p))
... | false = ⊎.inr (restrict-to-right h (builtin→Path-Bool p))

-- Embed Sp B∞ into Sp B∞×B∞ via left factor
inject-left : Sp B∞-Booleω → Sp B∞×B∞-Booleω
inject-left h = h' , h'-is-hom
  where
  open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1 ; pres+ to h-pres+ ; pres· to h-pres·)
  open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×'_ ; _·_ to _·×'_)

  h' : ⟨ B∞×B∞ ⟩ → Bool
  h' (x , y) = h $cr x

  h'-pres1 : h' (𝟙∞ , 𝟙∞) ≡ true
  h'-pres1 = h-pres1

  h'-pres+ : (a b : ⟨ B∞×B∞ ⟩) → h' (a +×' b) ≡ (h' a) ⊕ (h' b)
  h'-pres+ (x1 , y1) (x2 , y2) = h-pres+ x1 x2

  h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' (a ·×' b) ≡ (h' a) and (h' b)
  h'-pres· (x1 , y1) (x2 , y2) = h-pres· x1 x2

  h'-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞×B∞)) h' (snd (BooleanRing→CommRing BoolBR))
  h'-is-hom = makeIsCommRingHom h'-pres1 h'-pres+ h'-pres·

-- Embed Sp B∞ into Sp B∞×B∞ via right factor
inject-right : Sp B∞-Booleω → Sp B∞×B∞-Booleω
inject-right h = h' , h'-is-hom
  where
  open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1 ; pres+ to h-pres+ ; pres· to h-pres·)
  open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×'_ ; _·_ to _·×'_)

  h' : ⟨ B∞×B∞ ⟩ → Bool
  h' (x , y) = h $cr y

  h'-pres1 : h' (𝟙∞ , 𝟙∞) ≡ true
  h'-pres1 = h-pres1

  h'-pres+ : (a b : ⟨ B∞×B∞ ⟩) → h' (a +×' b) ≡ (h' a) ⊕ (h' b)
  h'-pres+ (x1 , y1) (x2 , y2) = h-pres+ y1 y2

  h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' (a ·×' b) ≡ (h' a) and (h' b)
  h'-pres· (x1 , y1) (x2 , y2) = h-pres· y1 y2

  h'-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞×B∞)) h' (snd (BooleanRing→CommRing BoolBR))
  h'-is-hom = makeIsCommRingHom h'-pres1 h'-pres+ h'-pres·

-- Backward map: combine inject-left and inject-right
Sp-sum-to-prod : (Sp B∞-Booleω) ⊎.⊎ (Sp B∞-Booleω) → Sp B∞×B∞-Booleω
Sp-sum-to-prod (⊎.inl h) = inject-left h
Sp-sum-to-prod (⊎.inr h) = inject-right h

-- Lemmas for roundtrip
inject-left-unit-left : (h : Sp B∞-Booleω) → inject-left h $cr B∞×B∞-Units.unit-left ≡ true
inject-left-unit-left h = IsCommRingHom.pres1 (snd h)

inject-right-unit-left : (h : Sp B∞-Booleω) → inject-right h $cr B∞×B∞-Units.unit-left ≡ false
inject-right-unit-left h = IsCommRingHom.pres0 (snd h)

restrict-inject-left : (h : Sp B∞-Booleω) → (pf : inject-left h $cr B∞×B∞-Units.unit-left ≡ true)
                     → restrict-to-left (inject-left h) pf ≡ h
restrict-inject-left h pf = Σ≡Prop
  (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞)) f (snd (BooleanRing→CommRing BoolBR)))
  refl

restrict-inject-right : (h : Sp B∞-Booleω) → (pf : inject-right h $cr B∞×B∞-Units.unit-left ≡ false)
                      → restrict-to-right (inject-right h) pf ≡ h
restrict-inject-right h pf = Σ≡Prop
  (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞)) f (snd (BooleanRing→CommRing BoolBR)))
  refl

-- =============================================================================
-- LLPO infrastructure (lines 6341-6500 of work.agda)
-- =============================================================================

-- Open the ring operations for B∞×B∞
open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_)

-- Sp(f) : Sp(B∞×B∞) → Sp(B∞)
Sp-f : Sp B∞×B∞-Booleω → Sp B∞-Booleω
Sp-f h = h ∘cr f

-- f is injective (postulated in Part07)
f-is-injective-hom : isInjectiveBoolHom B∞-Booleω B∞×B∞-Booleω f
f-is-injective-hom = f-injective

-- Apply the SurjectionsAreFormalSurjections axiom
Sp-f-surjective' : isSurjectiveSpHom B∞-Booleω B∞×B∞-Booleω f
Sp-f-surjective' = injective→Sp-surjective B∞-Booleω B∞×B∞-Booleω f f-is-injective-hom

Sp-f-surjective : (h : Sp B∞-Booleω) → ∥ Σ[ h' ∈ Sp B∞×B∞-Booleω ] Sp-f h' ≡ h ∥₁
Sp-f-surjective = Sp-f-surjective'

-- Sp-f relates homomorphism values through f
Sp-f-value : (h' : Sp B∞×B∞-Booleω) (x : ⟨ B∞ ⟩) →
  (Sp-f h') $cr x ≡ h' $cr (fst f x)
Sp-f-value h' x = refl

-- Unit orthogonality
unit-left-right-orth : (y : ⟨ B∞ ⟩) → B∞×B∞-Units.unit-left ·× (𝟘∞ , y) ≡ (𝟘∞ , 𝟘∞)
unit-left-right-orth y = cong₂ _,_ (0∞-absorbs-right 𝟙B∞) (0∞-absorbs-left y)
  where
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

unit-right-left-orth : (x : ⟨ B∞ ⟩) → B∞×B∞-Units.unit-right ·× (x , 𝟘∞) ≡ (𝟘∞ , 𝟘∞)
unit-right-left-orth x = cong₂ _,_ (0∞-absorbs-left x) (0∞-absorbs-right 𝟙B∞)
  where
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

-- If h'(1,0) = true, then h'(0,y) = false for all y
h'-left-true→right-false : (h' : Sp B∞×B∞-Booleω) → h' $cr B∞×B∞-Units.unit-left ≡ true →
  (y : ⟨ B∞ ⟩) → h' $cr (𝟘∞ , y) ≡ false
h'-left-true→right-false h' h'-left-true y =
  let
    h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' $cr (a ·× b) ≡ (h' $cr a) and (h' $cr b)
    h'-pres· = IsCommRingHom.pres· (snd h')
    prod-zero : B∞×B∞-Units.unit-left ·× (𝟘∞ , y) ≡ (𝟘∞ , 𝟘∞)
    prod-zero = unit-left-right-orth y
    h'-prod : h' $cr (B∞×B∞-Units.unit-left ·× (𝟘∞ , y)) ≡ false
    h'-prod = cong (h' $cr_) prod-zero ∙ IsCommRingHom.pres0 (snd h')
    h'-and : (h' $cr B∞×B∞-Units.unit-left) and (h' $cr (𝟘∞ , y)) ≡ false
    h'-and = sym (h'-pres· B∞×B∞-Units.unit-left (𝟘∞ , y)) ∙ h'-prod
    result : (h' $cr (𝟘∞ , y)) ≡ false
    result = subst (λ b → b and (h' $cr (𝟘∞ , y)) ≡ false) h'-left-true h'-and
  in result

-- Similarly for the other direction
h'-right-true→left-false : (h' : Sp B∞×B∞-Booleω) → h' $cr B∞×B∞-Units.unit-right ≡ true →
  (x : ⟨ B∞ ⟩) → h' $cr (x , 𝟘∞) ≡ false
h'-right-true→left-false h' h'-right-true x =
  let
    h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' $cr (a ·× b) ≡ (h' $cr a) and (h' $cr b)
    h'-pres· = IsCommRingHom.pres· (snd h')
    prod-zero : B∞×B∞-Units.unit-right ·× (x , 𝟘∞) ≡ (𝟘∞ , 𝟘∞)
    prod-zero = unit-right-left-orth x
    h'-prod : h' $cr (B∞×B∞-Units.unit-right ·× (x , 𝟘∞)) ≡ false
    h'-prod = cong (h' $cr_) prod-zero ∙ IsCommRingHom.pres0 (snd h')
    h'-and : (h' $cr B∞×B∞-Units.unit-right) and (h' $cr (x , 𝟘∞)) ≡ false
    h'-and = sym (h'-pres· B∞×B∞-Units.unit-right (x , 𝟘∞)) ∙ h'-prod
    result : (h' $cr (x , 𝟘∞)) ≡ false
    result = subst (λ b → b and (h' $cr (x , 𝟘∞)) ≡ false) h'-right-true h'-and
  in result

