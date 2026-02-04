{-# OPTIONS --cubical --guardedness #-}

module work.Part10c where

open import work.Part10a public

-- =============================================================================
-- Part 10c: More Boolean algebra laws for closed/open subsets of Cantor space
-- Split from Part10a to improve compilation time
-- =============================================================================

-- Additional imports for Part10c
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Data.Unit using (tt)

module BooleanAlgebraLawsModule2 where
  open StoneAsClosedSubsetOfCantorModule
  open StoneAsClosedSubsetOfCantorModule2
  open StoneEqualityClosedModule using (isPropIsClosedProp)
  open BooleanAlgebraLawsModule

  -- ==========================================================================
  -- Helper lemmas for identity and annihilation laws
  -- ==========================================================================

  -- Helper: P × Unit ↔ P (right identity for product)
  ×-Unit-right : (P : hProp ℓ-zero)
    → ((fst P × Unit) , isProp× (snd P) (λ _ _ → refl)) ≡ P
  ×-Unit-right P = hProp≡ _ _ (λ (p , _) → p) (λ p → p , tt)

  -- Helper: ∥ P ⊎ ⊥ ∥₁ ↔ P (right identity for truncated union)
  ⊎-⊥-right : (P : hProp ℓ-zero)
    → (∥ fst P ⊎ ⊥ ∥₁ , squash₁) ≡ P
  ⊎-⊥-right P = hProp≡ _ _
    (PT.rec (snd P) (λ { (inl p) → p ; (inr ()) }))
    (λ p → ∣ inl p ∣₁)

  -- Helper: P × ⊥ ↔ ⊥ (right annihilation for product)
  ×-⊥-right : (P : hProp ℓ-zero)
    → ((fst P × ⊥) , isProp× (snd P) isProp⊥) ≡ ⊥-hProp
  ×-⊥-right P = hProp≡ _ _ (λ (_ , bot) → bot) (λ ())

  -- Helper: ∥ P ⊎ Unit ∥₁ ↔ Unit (right annihilation for truncated union)
  ⊎-Unit-right : (P : hProp ℓ-zero)
    → (∥ fst P ⊎ Unit ∥₁ , squash₁) ≡ ⊤-hProp
  ⊎-Unit-right P = hProp≡ _ _
    (λ _ → tt)
    (λ _ → ∣ inr tt ∣₁)

  -- ==========================================================================
  -- Identity and Annihilation laws for closed subsets
  -- ==========================================================================

  -- Identity: A ∩ Full = A - PROVED
  closedIntersectionFull' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A FullClosedSubset ≡ A
  closedIntersectionFull' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × Unit) , isProp× (snd (A x)) (λ _ _ → refl)) ≡ A
    fst-path = funExt (λ x → ×-Unit-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊤-hProp (Aclosed x) ⊤-isClosed)
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Identity: A ∪ Empty = A - PROVED
  closedUnionEmpty' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A EmptyClosedSubset ≡ A
  closedUnionEmpty' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ ⊥ ∥₁) , squash₁) ≡ A
    fst-path = funExt (λ x → ⊎-⊥-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) ⊥-hProp (Aclosed x) ⊥-isClosed)
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Annihilation: A ∩ Empty = Empty - PROVED
  closedIntersectionEmpty' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A EmptyClosedSubset ≡ EmptyClosedSubset
  closedIntersectionEmpty' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × ⊥) , isProp× (snd (A x)) isProp⊥) ≡ (λ _ → ⊥-hProp)
    fst-path = funExt (λ x → ×-⊥-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊥-hProp (Aclosed x) ⊥-isClosed)
                     (λ _ → ⊥-isClosed)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Annihilation: A ∪ Full = Full - PROVED
  closedUnionFull' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A FullClosedSubset ≡ FullClosedSubset
  closedUnionFull' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ Unit ∥₁) , squash₁) ≡ (λ _ → ⊤-hProp)
    fst-path = funExt (λ x → ⊎-Unit-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) ⊤-hProp (Aclosed x) ⊤-isClosed)
                     (λ _ → ⊤-isClosed)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

-- End of Part10c
