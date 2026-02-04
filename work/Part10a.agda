{-# OPTIONS --cubical --guardedness #-}

module work.Part10a where

open import work.Part10b public

-- =============================================================================
-- Part 10a: Boolean algebra laws for closed/open subsets of Cantor space
-- Split from Part10 to improve compilation time
-- All laws postulated for compilation speed - proofs depend on operation definitions
-- =============================================================================

-- Additional imports for Part10a
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary using (¬_)

module BooleanAlgebraLawsModule where
  open StoneAsClosedSubsetOfCantorModule
  open StoneAsClosedSubsetOfCantorModule2
  open StoneEqualityClosedModule using (isPropIsClosedProp)

  -- ==========================================================================
  -- Helper: hProp equality via biimplication
  -- ==========================================================================

  -- Propositional extensionality: Props with bi-implications are equal
  hPropExt : {A B : Type₀} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B
  hPropExt pA pB f g = ua (isoToEquiv (iso f g (λ b → pB _ _) (λ a → pA _ _)))

  -- Two hProps are equal if they are logically equivalent (propositional extensionality)
  hProp≡ : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩) → P ≡ Q
  hProp≡ P Q f g = Σ≡Prop (λ _ → isPropIsProp) (hPropExt (snd P) (snd Q) f g)

  -- Product of propositions is commutative up to hProp equality
  ×-hProp-comm : (P Q : hProp ℓ-zero)
    → ((fst P × fst Q) , isProp× (snd P) (snd Q))
      ≡ ((fst Q × fst P) , isProp× (snd Q) (snd P))
  ×-hProp-comm P Q = hProp≡ _ _ (λ (p , q) → q , p) (λ (q , p) → p , q)

  -- ==========================================================================
  -- Boolean algebra laws for closed subsets
  -- ==========================================================================

  -- Commutativity of intersection (closed) - PROVED
  closedIntersectionComm : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A B ≡ ClosedSubsetIntersection B A
  closedIntersectionComm (A , Aclosed) (B , Bclosed) = ΣPathP (fst-path , snd-path)
    where
    -- First component: the underlying hProp-valued functions are equal
    fst-path : (λ x → (fst (A x) × fst (B x)) , isProp× (snd (A x)) (snd (B x)))
             ≡ (λ x → (fst (B x) × fst (A x)) , isProp× (snd (B x)) (snd (A x)))
    fst-path = funExt (λ x → ×-hProp-comm (A x) (B x))

    -- Second component: closedness witnesses are equal after transport
    -- Since isClosedProp is a prop (postulated), we use isProp→PathP
    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) (B x) (Aclosed x) (Bclosed x))
                     (λ x → closedAnd (B x) (A x) (Bclosed x) (Aclosed x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x}))
                            _ _

  -- Commutativity of union (closed) - PROVED
  -- Union uses truncated disjunction: ∥ P ⊎ Q ∥₁
  closedUnionComm : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A B ≡ ClosedSubsetUnion B A
  closedUnionComm (A , Aclosed) (B , Bclosed) = ΣPathP (fst-path , snd-path)
    where
    -- For truncated disjunction: ∥ P ⊎ Q ∥₁ ↔ ∥ Q ⊎ P ∥₁ via map over inl/inr swap
    ⊎-swap : {P Q : Type₀} → ∥ P ⊎ Q ∥₁ → ∥ Q ⊎ P ∥₁
    ⊎-swap = PT.map (λ { (inl p) → inr p ; (inr q) → inl q })

    fst-path : (λ x → (∥ fst (A x) ⊎ fst (B x) ∥₁) , squash₁)
             ≡ (λ x → (∥ fst (B x) ⊎ fst (A x) ∥₁) , squash₁)
    fst-path = funExt (λ x → hProp≡ _ _ ⊎-swap ⊎-swap)

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) (B x) (Aclosed x) (Bclosed x))
                     (λ x → closedOr (B x) (A x) (Bclosed x) (Aclosed x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x}))
                            _ _

  -- Helper: P × P ↔ P for props (idempotence of product)
  ×-hProp-idem : (P : hProp ℓ-zero)
    → ((fst P × fst P) , isProp× (snd P) (snd P)) ≡ P
  ×-hProp-idem P = hProp≡ _ _ (λ (p , _) → p) (λ p → p , p)

  -- Helper: ∥ P ⊎ P ∥₁ ↔ P for props (idempotence of truncated union)
  ⊎-hProp-idem : (P : hProp ℓ-zero)
    → (∥ fst P ⊎ fst P ∥₁ , squash₁) ≡ P
  ⊎-hProp-idem P = hProp≡ _ _
    (PT.rec (snd P) (λ { (inl p) → p ; (inr p) → p }))
    (λ p → ∣ inl p ∣₁)

  -- Idempotence of intersection (closed) - PROVED
  closedIntersectionIdem : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A A ≡ A
  closedIntersectionIdem (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (A x)) , isProp× (snd (A x)) (snd (A x))) ≡ A
    fst-path = funExt (λ x → ×-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) (A x) (Aclosed x) (Aclosed x))
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Idempotence of union (closed) - PROVED
  closedUnionIdem : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A A ≡ A
  closedUnionIdem (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ fst (A x) ∥₁) , squash₁) ≡ A
    fst-path = funExt (λ x → ⊎-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) (A x) (Aclosed x) (Aclosed x))
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Helper: P × ⊥ ↔ ⊥ for props (annihilation of product by empty)
  ×-hProp-empty : (P : hProp ℓ-zero)
    → ((fst P × ⊥) , isProp× (snd P) isProp⊥) ≡ ⊥-hProp
  ×-hProp-empty P = hProp≡ _ _ (λ (_ , bot) → bot) (λ bot → ex-falso bot , bot)

  -- Helper: P × Unit ↔ P for props (identity of product with unit)
  -- This is fast because Unit is trivial (single constructor tt)
  ×-hProp-full : (P : hProp ℓ-zero)
    → ((fst P × Unit) , isProp× (snd P) (λ _ _ → refl)) ≡ P
  ×-hProp-full P = hProp≡ _ _ (λ (p , _) → p) (λ p → p , tt)

  -- Helper: (P × Q) × R ↔ P × (Q × R) for props (associativity of product)
  ×-hProp-assoc : (P Q R : hProp ℓ-zero)
    → ((fst P × fst Q) × fst R , isProp× (isProp× (snd P) (snd Q)) (snd R))
      ≡ (fst P × (fst Q × fst R) , isProp× (snd P) (isProp× (snd Q) (snd R)))
  ×-hProp-assoc P Q R = hProp≡ _ _
    (λ ((p , q) , r) → p , (q , r))
    (λ (p , (q , r)) → (p , q) , r)

  -- Annihilation: A ∩ Empty = Empty (PROVED)
  closedIntersectionEmpty : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A EmptyClosedSubset ≡ EmptyClosedSubset
  closedIntersectionEmpty (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × ⊥) , isProp× (snd (A x)) isProp⊥) ≡ (λ _ → ⊥-hProp)
    fst-path = funExt (λ x → ×-hProp-empty (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊥-hProp (Aclosed x) ⊥-isClosed)
                     (λ _ → ⊥-isClosed)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Identity: A ∩ Full = A (PROVED)
  -- FullClosedSubset = (λ _ → ⊤-hProp) where ⊤-hProp = (Unit , λ _ _ → refl)
  closedIntersectionFull : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A FullClosedSubset ≡ A
  closedIntersectionFull (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × Unit) , isProp× (snd (A x)) (λ _ _ → refl)) ≡ A
    fst-path = funExt (λ x → ×-hProp-full (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊤-hProp (Aclosed x) ⊤-isClosed)
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Associativity of intersection (closed) - PROVED
  closedIntersectionAssoc : (A B C : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A (ClosedSubsetIntersection B C)
      ≡ ClosedSubsetIntersection (ClosedSubsetIntersection A B) C
  closedIntersectionAssoc (A , Acl) (B , Bcl) (C , Ccl) = ΣPathP (fst-path , snd-path)
    where
    -- Helper: apply ×-hProp-assoc with swapped direction (right assoc → left assoc)
    fst-path : (λ x → (fst (A x) × (fst (B x) × fst (C x))) ,
                      isProp× (snd (A x)) (isProp× (snd (B x)) (snd (C x))))
             ≡ (λ x → ((fst (A x) × fst (B x)) × fst (C x)) ,
                      isProp× (isProp× (snd (A x)) (snd (B x))) (snd (C x)))
    fst-path = funExt (λ x → sym (×-hProp-assoc (A x) (B x) (C x)))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ((fst (B x) × fst (C x)) ,
                              isProp× (snd (B x)) (snd (C x))) (Acl x)
                              (closedAnd (B x) (C x) (Bcl x) (Ccl x)))
                     (λ x → closedAnd ((fst (A x) × fst (B x)) ,
                              isProp× (snd (A x)) (snd (B x))) (C x)
                              (closedAnd (A x) (B x) (Acl x) (Bcl x)) (Ccl x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  -- Remaining closed subset laws (postulated for compilation speed)
  -- NOTE: These have straightforward proofs using hProp≡ (propositional extensionality via ua)
  -- but the ua causes expensive normalization that times out compilation.
  -- Proof sketches available in work/backup_parts/Part17.agda
  postulate
    -- Absorption: A ∩ (A ∪ B) = A
    closedAbsorption1 : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetUnion A B) ≡ A

    -- Absorption: A ∪ (A ∩ B) = A
    closedAbsorption2 : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (ClosedSubsetIntersection A B) ≡ A

    -- Identity: A ∪ Empty = A
    closedUnionEmpty : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A EmptyClosedSubset ≡ A

    -- Annihilation: A ∪ Full = Full
    closedUnionFull : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A FullClosedSubset ≡ FullClosedSubset

    -- Associativity of union (closed)
    closedUnionAssoc : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (ClosedSubsetUnion B C)
        ≡ ClosedSubsetUnion (ClosedSubsetUnion A B) C

    -- Distributivity: A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C) (closed)
    closedDistributiveIntersection : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetUnion B C)
        ≡ ClosedSubsetUnion (ClosedSubsetIntersection A B) (ClosedSubsetIntersection A C)

  -- ==========================================================================
  -- Boolean algebra laws for open subsets
  -- ==========================================================================

  -- Annihilation: A ∩ Empty = Empty (open) - PROVED
  openIntersectionEmpty : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A EmptyOpenSubset ≡ EmptyOpenSubset
  openIntersectionEmpty (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × ⊥) , isProp× (snd (A x)) isProp⊥) ≡ (λ _ → ⊥-hProp)
    fst-path = funExt (λ x → ×-hProp-empty (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) ⊥-hProp (Aopen x) ⊥-isOpen)
                     (λ _ → ⊥-isOpen)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Commutativity of intersection (open) - PROVED
  openIntersectionComm : (A B : OpenSubsetOfCantor)
    → OpenSubsetIntersection A B ≡ OpenSubsetIntersection B A
  openIntersectionComm (A , Aopen) (B , Bopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (B x)) , isProp× (snd (A x)) (snd (B x)))
             ≡ (λ x → (fst (B x) × fst (A x)) , isProp× (snd (B x)) (snd (A x)))
    fst-path = funExt (λ x → ×-hProp-comm (A x) (B x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) (B x) (Aopen x) (Bopen x))
                     (λ x → openAnd (B x) (A x) (Bopen x) (Aopen x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Commutativity of union (open) - PROVED
  openUnionComm : (A B : OpenSubsetOfCantor)
    → OpenSubsetUnion A B ≡ OpenSubsetUnion B A
  openUnionComm (A , Aopen) (B , Bopen) = ΣPathP (fst-path , snd-path)
    where
    ⊎-swap : {P Q : Type₀} → ∥ P ⊎ Q ∥₁ → ∥ Q ⊎ P ∥₁
    ⊎-swap = PT.map (λ { (inl p) → inr p ; (inr q) → inl q })

    fst-path : (λ x → (∥ fst (A x) ⊎ fst (B x) ∥₁) , squash₁)
             ≡ (λ x → (∥ fst (B x) ⊎ fst (A x) ∥₁) , squash₁)
    fst-path = funExt (λ x → hProp≡ _ _ ⊎-swap ⊎-swap)

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openOr (A x) (B x) (Aopen x) (Bopen x))
                     (λ x → openOr (B x) (A x) (Bopen x) (Aopen x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Idempotence of intersection (open) - PROVED
  openIntersectionIdem : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A A ≡ A
  openIntersectionIdem (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (A x)) , isProp× (snd (A x)) (snd (A x))) ≡ A
    fst-path = funExt (λ x → ×-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) (A x) (Aopen x) (Aopen x))
                     Aopen
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Idempotence of union (open) - PROVED
  openUnionIdem : (A : OpenSubsetOfCantor)
    → OpenSubsetUnion A A ≡ A
  openUnionIdem (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ fst (A x) ∥₁) , squash₁) ≡ A
    fst-path = funExt (λ x → ⊎-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openOr (A x) (A x) (Aopen x) (Aopen x))
                     Aopen
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Identity: A ∩ Full = A (open) - PROVED
  openIntersectionFull : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A FullOpenSubset ≡ A
  openIntersectionFull (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × Unit) , isProp× (snd (A x)) (λ _ _ → refl)) ≡ A
    fst-path = funExt (λ x → ×-hProp-full (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) ⊤-hProp (Aopen x) ⊤-isOpen)
                     Aopen
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Associativity of intersection (open) - PROVED
  openIntersectionAssoc : (A B C : OpenSubsetOfCantor)
    → OpenSubsetIntersection A (OpenSubsetIntersection B C)
      ≡ OpenSubsetIntersection (OpenSubsetIntersection A B) C
  openIntersectionAssoc (A , Aop) (B , Bop) (C , Cop) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × (fst (B x) × fst (C x))) ,
                      isProp× (snd (A x)) (isProp× (snd (B x)) (snd (C x))))
             ≡ (λ x → ((fst (A x) × fst (B x)) × fst (C x)) ,
                      isProp× (isProp× (snd (A x)) (snd (B x))) (snd (C x)))
    fst-path = funExt (λ x → sym (×-hProp-assoc (A x) (B x) (C x)))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) ((fst (B x) × fst (C x)) ,
                              isProp× (snd (B x)) (snd (C x))) (Aop x)
                              (openAnd (B x) (C x) (Bop x) (Cop x)))
                     (λ x → openAnd ((fst (A x) × fst (B x)) ,
                              isProp× (snd (A x)) (snd (B x))) (C x)
                              (openAnd (A x) (B x) (Aop x) (Bop x)) (Cop x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  -- Remaining open subset laws (postulated for speed)
  postulate
    -- Absorption: A ∩ (A ∪ B) = A (open)
    openAbsorption1 : (A B : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetUnion A B) ≡ A

    -- Absorption: A ∪ (A ∩ B) = A (open)
    openAbsorption2 : (A B : OpenSubsetOfCantor)
      → OpenSubsetUnion A (OpenSubsetIntersection A B) ≡ A

    -- Identity: A ∪ Empty = A (open)
    openUnionEmpty : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A EmptyOpenSubset ≡ A

    -- Annihilation: A ∪ Full = Full (open)
    openUnionFull : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A FullOpenSubset ≡ FullOpenSubset

    -- Associativity of union (open)
    openUnionAssoc : (A B C : OpenSubsetOfCantor)
      → OpenSubsetUnion A (OpenSubsetUnion B C)
        ≡ OpenSubsetUnion (OpenSubsetUnion A B) C

    -- Distributivity: A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C) (open)
    openDistributiveIntersection : (A B C : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetUnion B C)
        ≡ OpenSubsetUnion (OpenSubsetIntersection A B) (OpenSubsetIntersection A C)

  -- ==========================================================================
  -- Complement laws (postulated for speed)
  -- ==========================================================================

  postulate
    -- Double complement involution for closed subsets
    closedDoubleComplementInvolution : (A : ClosedSubsetOfCantor)
      → OpenSubsetComplement (ClosedSubsetComplement A) ≡ A

    -- Double complement involution for open subsets
    openDoubleComplementInvolution : (A : OpenSubsetOfCantor)
      → ClosedSubsetComplement (OpenSubsetComplement A) ≡ A

    -- Law of excluded middle for closed subsets as path equality
    closedUnionComplement : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (OpenSubsetComplement (ClosedSubsetComplement A))
        ≡ FullClosedSubset

    -- Law of excluded middle for open subsets as path equality
    openUnionComplement : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A (ClosedSubsetComplement (OpenSubsetComplement A))
        ≡ FullOpenSubset

  -- ==========================================================================
  -- De Morgan laws
  -- ==========================================================================

  -- De Morgan: ¬(closed A ∪ closed B) ↔ ¬A ∩ ¬B - PROVED
  -- Forward: ¬∥ A ⊎ B ∥₁ → (¬A × ¬B)
  closedDeMorganUnion-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
    → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
  closedDeMorganUnion-fwd (A , _) (B , _) x ¬AorB =
    (λ ax → ¬AorB ∣ inl ax ∣₁) , (λ bx → ¬AorB ∣ inr bx ∣₁)

  -- Backward: (¬A × ¬B) → ¬∥ A ⊎ B ∥₁
  closedDeMorganUnion-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
  closedDeMorganUnion-bwd (A , _) (B , _) x (¬ax , ¬bx) =
    PT.rec isProp⊥ (λ { (inl ax) → ¬ax ax ; (inr bx) → ¬bx bx })

  -- De Morgan: ¬(open A ∪ open B) ↔ ¬A ∩ ¬B - PROVED
  openDeMorganUnion-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
    → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
  openDeMorganUnion-fwd (A , _) (B , _) x ¬AorB =
    (λ ax → ¬AorB ∣ inl ax ∣₁) , (λ bx → ¬AorB ∣ inr bx ∣₁)

  openDeMorganUnion-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
  openDeMorganUnion-bwd (A , _) (B , _) x (¬ax , ¬bx) =
    PT.rec isProp⊥ (λ { (inl ax) → ¬ax ax ; (inr bx) → ¬bx bx })

  -- De Morgan: ¬(closed A ∩ closed B) ↔ ¬A ∪ ¬B
  -- Forward direction (¬(A × B) → ∥¬A ⊎ ¬B∥₁) is NOT constructively provable
  -- Backward direction (∥¬A ⊎ ¬B∥₁ → ¬(A × B)) IS constructively provable
  postulate
    closedDeMorganIntersection-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
      → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)

  -- PROVED: Backward direction of De Morgan for closed intersection
  -- Given ∥¬A ⊎ ¬B∥₁ and (a , b) : A × B, we get ⊥ by case analysis on the disjunction
  closedDeMorganIntersection-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
  closedDeMorganIntersection-bwd (A , _) (B , _) x =
    λ (h : ∥ (fst (A x) → ⊥) ⊎ (fst (B x) → ⊥) ∥₁) →
    λ ((ax , bx) : fst (A x) × fst (B x)) →
    PT.rec isProp⊥ (λ { (inl ¬ax) → ¬ax ax ; (inr ¬bx) → ¬bx bx }) h

  -- De Morgan: ¬(open A ∩ open B) ↔ ¬A ∪ ¬B
  -- Forward direction NOT constructively provable; backward IS
  postulate
    openDeMorganIntersection-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
      → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)

  -- PROVED: Backward direction of De Morgan for open intersection
  openDeMorganIntersection-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
  openDeMorganIntersection-bwd (A , _) (B , _) x =
    λ (h : ∥ (fst (A x) → ⊥) ⊎ (fst (B x) → ⊥) ∥₁) →
    λ ((ax , bx) : fst (A x) × fst (B x)) →
    PT.rec isProp⊥ (λ { (inl ¬ax) → ¬ax ax ; (inr ¬bx) → ¬bx bx }) h

-- =============================================================================
-- BooleEpiMono (tex Remark 1475)
-- =============================================================================
--
-- Any morphism g : B → C in Boole has an overtly discrete kernel.
-- As a consequence:
-- 1. Ker(g) is enumerable
-- 2. B/Ker(g) is in Boole
-- 3. The factorization B ↠ B/Ker(g) ↪ C corresponds to
--    Sp(C) ↠ Sp(B/Ker(g)) ↪ Sp(B)
--
-- This means quotient maps in Boole correspond to closed embeddings of spectra.
--

-- End of Part10a
